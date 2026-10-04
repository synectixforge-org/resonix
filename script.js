/* ============================================================
   SIGNAL — Tab Audio Visualizer
   script.js
   Modules: AudioEngine, AnalysisUtils, ThemeManager, SettingsManager,
            Visualizer base + 9 modes + Auto mode, AnimationEngine, UIController
   No frameworks. No backend. Everything runs locally.
   ============================================================ */

'use strict';

/* ============================================================
   SECTION 1 — SMALL MATH / UTILITY HELPERS
   ============================================================ */
const Util = {
  lerp(a, b, t) { return a + (b - a) * t; },
  clamp(v, min, max) { return v < min ? min : v > max ? max : v; },
  map(v, inMin, inMax, outMin, outMax) {
    return outMin + ((v - inMin) / (inMax - inMin)) * (outMax - outMin);
  },
  easeOutCubic(t) { return 1 - Math.pow(1 - t, 3); },
  easeInOutSine(t) { return -(Math.cos(Math.PI * t) - 1) / 2; },
  // Spring-ish smoothing toward a target. Returns new value.
  spring(current, target, velocity, stiffness = 0.18, damping = 0.78) {
    const force = (target - current) * stiffness;
    velocity = (velocity + force) * damping;
    return { value: current + velocity, velocity };
  },
  hexToRgb(hex) {
    const m = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
    return m ? { r: parseInt(m[1], 16), g: parseInt(m[2], 16), b: parseInt(m[3], 16) } : { r: 255, g: 255, b: 255 };
  },
  // Reads a CSS variable's resolved color and returns rgb components
  cssVarRgb(name) {
    const val = getComputedStyle(document.body).getPropertyValue(name).trim();
    if (val.startsWith('#')) return Util.hexToRgb(val);
    const m = /rgba?\(\s*([\d.]+)[,\s]+([\d.]+)[,\s]+([\d.]+)/.exec(val);
    if (m) return { r: +m[1], g: +m[2], b: +m[3] };
    return { r: 255, g: 255, b: 255 };
  },
  formatHz(hz) {
    if (hz >= 1000) return (hz / 1000).toFixed(1) + 'k';
    return Math.round(hz).toString();
  },
  downloadCanvasPNG(canvas, filename) {
    const link = document.getElementById('downloadLink');
    canvas.toBlob((blob) => {
      const url = URL.createObjectURL(blob);
      link.href = url;
      link.download = filename;
      link.click();
      setTimeout(() => URL.revokeObjectURL(url), 2000);
    }, 'image/png');
  }
};

/* ============================================================
   SECTION 2 — AUDIO ENGINE
   Captures tab audio via getDisplayMedia, builds the Web Audio
   graph (source -> gain -> analyser -> destination-less sink),
   and exposes per-frame analysis data (FFT, waveform, bands).
   ============================================================ */
class AudioEngine {
  constructor() {
    this.audioCtx = null;
    this.analyser = null;
    this.gainNode = null;
    this.sourceNode = null;
    this.displayStream = null;

    this.fftSize = 2048;
    this.smoothing = 0.78;
    this.gain = 1;
    this.sensitivity = 1;

    // Reusable typed arrays — never reallocate per frame.
    this.freqData = null;      // Uint8Array frequency domain
    this.freqDataF = null;     // Float32Array frequency domain (dB)
    this.timeData = null;      // Uint8Array time domain

    this.sampleRate = 0;
    this.isCapturing = false;
    this.isPaused = false;

    // Frequency bands (Hz) used for Orchestra mode + bass/mid/treble analysis
    this.bandDefs = [
      { name: 'Sub Bass', lo: 20, hi: 60, icon: 'sub' },
      { name: 'Bass', lo: 60, hi: 250, icon: 'bass' },
      { name: 'Low Mid', lo: 250, hi: 500, icon: 'lowmid' },
      { name: 'Mid', lo: 500, hi: 2000, icon: 'mid' },
      { name: 'High Mid', lo: 2000, hi: 4000, icon: 'highmid' },
      { name: 'Presence', lo: 4000, hi: 6000, icon: 'presence' },
      { name: 'Brilliance', lo: 6000, hi: 20000, icon: 'brilliance' },
    ];

    // Beat detection state
    this.beatEnergyHistory = [];
    this.beatHistorySize = 43; // ~ last second at 60fps-ish sampling of energy
    this.lastBeatTime = 0;
    this.beatIntervals = [];
    this.bpm = 0;
    this.beatFlashCallback = null;

    // Output metrics (read by UI every frame)
    this.metrics = {
      volume: 0,        // 0-100 %
      peakFreq: 0,       // Hz
      rms: 0,
      peak: 0,
      average: 0,
      db: -Infinity,
      bass: 0,
      mid: 0,
      treble: 0,
      energy: 0,
      isSilent: true,
    };

    this.latencyMs = 0;
    // 'interactive' | 'balanced' | 'playback' — passed to the AudioContext
    // constructor, so a change only takes effect on the next start().
    this.latencyHint = 'interactive';
  }

  setLatencyHint(hint) {
    this.latencyHint = hint;
  }

  get isSupported() {
    return !!(navigator.mediaDevices && navigator.mediaDevices.getDisplayMedia && (window.AudioContext || window.webkitAudioContext));
  }

  async start() {
    if (!this.isSupported) {
      throw new Error('UNSUPPORTED');
    }

    const t0 = performance.now();

    // Ask the user to pick a tab and share its audio.
    this.displayStream = await navigator.mediaDevices.getDisplayMedia({
      video: true,        // required by spec to trigger the tab picker on most browsers
      audio: true,
      systemAudio: 'include',
      preferCurrentTab: false,
    });

    const audioTracks = this.displayStream.getAudioTracks();
    if (audioTracks.length === 0) {
      this.stop();
      throw new Error('NO_AUDIO_TRACK');
    }

    // We don't need the video track at all — drop it immediately to save resources.
    this.displayStream.getVideoTracks().forEach(t => t.stop());

    const AC = window.AudioContext || window.webkitAudioContext;
    try {
      this.audioCtx = new AC({ latencyHint: this.latencyHint });
    } catch (e) {
      // Older browsers can reject an unrecognized latencyHint value.
      this.audioCtx = new AC();
    }
    this.sampleRate = this.audioCtx.sampleRate;

    this.sourceNode = this.audioCtx.createMediaStreamSource(this.displayStream);

    this.gainNode = this.audioCtx.createGain();
    this.gainNode.gain.value = this.gain;

    this.analyser = this.audioCtx.createAnalyser();
    this.analyser.fftSize = this.fftSize;
    this.analyser.smoothingTimeConstant = this.smoothing;
    // Ceiling was -10dB, which is close enough to typical mastered-music
    // peak levels that the bass bins pinned to 100% almost immediately —
    // even a touch of extra sensitivity/gain instantly "filled the room".
    // Pushing the ceiling out toward full scale (and the floor down for
    // more low-level resolution) gives real headroom, so normal listening
    // levels read well below max and there's still room for the sliders
    // to matter.
    this.analyser.minDecibels = -100;
    this.analyser.maxDecibels = -6;

    this.sourceNode.connect(this.gainNode);
    this.gainNode.connect(this.analyser);
    // Intentionally NOT connecting to audioCtx.destination:
    // we don't want to play the captured tab audio back out of the speakers
    // (that would create an echo since the tab is already playing audio).

    this._allocateBuffers();

    this.isCapturing = true;
    this.isPaused = false;

    // If the user stops sharing from the browser's native "Stop sharing" bar.
    audioTracks[0].addEventListener('ended', () => {
      if (this.onExternalStop) this.onExternalStop();
    });

    // Prefer the context's own reported base latency (what the latencyHint
    // actually bought us) — fall back to the capture setup time if the
    // browser doesn't expose baseLatency.
    const baseLatencySec = this.audioCtx.baseLatency;
    this.latencyMs = baseLatencySec
      ? Math.round(baseLatencySec * 1000)
      : Math.round(performance.now() - t0);
  }

  _allocateBuffers() {
    const binCount = this.analyser.frequencyBinCount;
    this.freqData = new Uint8Array(binCount);
    this.freqDataF = new Float32Array(binCount);
    this.timeData = new Uint8Array(this.analyser.fftSize);
  }

  setFftSize(size) {
    this.fftSize = size;
    if (this.analyser) {
      this.analyser.fftSize = size;
      this._allocateBuffers();
    }
  }

  setSmoothing(val) {
    this.smoothing = val;
    if (this.analyser) this.analyser.smoothingTimeConstant = val;
  }

  setGain(val) {
    this.gain = val;
    if (this.gainNode) this.gainNode.gain.value = val;
  }

  setSensitivity(val) {
    this.sensitivity = val;
  }

  pause() {
    this.isPaused = true;
    if (this.audioCtx && this.audioCtx.state === 'running') this.audioCtx.suspend();
  }

  resume() {
    this.isPaused = false;
    if (this.audioCtx && this.audioCtx.state === 'suspended') this.audioCtx.resume();
  }

  stop() {
    this.isCapturing = false;
    this.isPaused = false;
    try {
      if (this.displayStream) this.displayStream.getTracks().forEach(t => t.stop());
    } catch (e) { /* noop */ }
    try {
      if (this.sourceNode) this.sourceNode.disconnect();
      if (this.gainNode) this.gainNode.disconnect();
      if (this.analyser) this.analyser.disconnect();
    } catch (e) { /* noop */ }
    try {
      if (this.audioCtx) this.audioCtx.close();
    } catch (e) { /* noop */ }

    this.audioCtx = null;
    this.analyser = null;
    this.gainNode = null;
    this.sourceNode = null;
    this.displayStream = null;
    this.beatEnergyHistory.length = 0;
    this.beatIntervals.length = 0;
    this.bpm = 0;
  }

  /** Pull the latest frequency + time domain data into the reusable buffers. */
  update() {
    if (!this.analyser) return;
    this.analyser.getByteFrequencyData(this.freqData);
    this.analyser.getFloatFrequencyData(this.freqDataF);
    this.analyser.getByteTimeDomainData(this.timeData);
    this._computeMetrics();
    this._detectBeat();
  }

  /** Convert an FFT bin index to its corresponding frequency in Hz. */
  binToFreq(bin) {
    return (bin * this.sampleRate) / this.fftSize;
  }
  freqToBin(freq) {
    return Math.round((freq * this.fftSize) / this.sampleRate);
  }

  /** Get averaged energy (0-255) for a Hz range. */
  /** More detailed version of bandDefs, generated on demand for any row
   *  count above 7 (Orchestra Mode 2 / Line Graph 2 / Meter Bank 2's row
   *  slider). Rather than blindly slicing the whole spectrum into unlabeled
   *  ranges, each of the 7 real bands (Sub Bass, Bass, Low Mid, Mid, High
   *  Mid, Presence, Brilliance) gets split into that many numbered
   *  sub-rows — "Bass 1" / "Bass 2" / "Bass 3" and so on — so a row's label
   *  still tells you what part of the mix it's showing. Bands that span
   *  more octaves (e.g. Brilliance: 6kHz-20kHz) get more sub-rows than
   *  narrow ones (e.g. Sub Bass: 20-60Hz) in proportion, since that's where
   *  there's actually more going on to resolve. This is just a finer label
   *  scheme on top of the same raw bins — resolution comes from
   *  getBandEnergy averaging whatever falls in each narrower range, which
   *  works at any FFT size. */
  getDynamicBands(count) {
    const base = this.bandDefs;
    const n = Math.max(base.length, Math.round(count));
    const extra = n - base.length;

    const weights = base.map(b => Math.log2(b.hi / b.lo)); // octaves spanned
    const totalWeight = weights.reduce((a, b) => a + b, 0);
    const raw = weights.map(w => (w / totalWeight) * extra);
    const counts = raw.map(Math.floor);
    let used = counts.reduce((a, b) => a + b, 0);
    const byRemainder = raw
      .map((r, i) => ({ i, frac: r - counts[i] }))
      .sort((a, b) => b.frac - a.frac);
    for (let k = 0; used < extra; k++, used++) counts[byRemainder[k % byRemainder.length].i]++;

    const bands = [];
    base.forEach((band, bi) => {
      const k = counts[bi] + 1; // every band keeps at least its own row
      for (let j = 0; j < k; j++) {
        const lo = band.lo * Math.pow(band.hi / band.lo, j / k);
        const hi = band.lo * Math.pow(band.hi / band.lo, (j + 1) / k);
        bands.push({
          name: k === 1 ? band.name : `${band.name} ${j + 1}`,
          lo: Math.round(lo),
          hi: Math.round(hi),
          icon: band.icon,
        });
      }
    });
    return bands;
  }

  /** Fixed band set used by Meter Bank 2: the normal 7 bands, except Bass
   *  (60-250Hz) is always split into 3 log-spaced sub-rows — Bass 1, Bass 2,
   *  Bass 3 — regardless of any row-count setting. Everything else stays
   *  exactly as it is in bandDefs, one row each. 9 rows total, fixed. */
  getMeterBank2Bands() {
    const bands = [];
    for (const band of this.bandDefs) {
      if (band.name !== 'Bass') { bands.push(band); continue; }
      const k = 3;
      for (let j = 0; j < k; j++) {
        const lo = band.lo * Math.pow(band.hi / band.lo, j / k);
        const hi = band.lo * Math.pow(band.hi / band.lo, (j + 1) / k);
        bands.push({ name: `Bass ${j + 1}`, lo: Math.round(lo), hi: Math.round(hi), icon: band.icon });
      }
    }
    return bands;
  }

  getBandEnergy(loHz, hiHz) {
    const loBin = Util.clamp(this.freqToBin(loHz), 0, this.freqData.length - 1);
    const hiBin = Util.clamp(this.freqToBin(hiHz), loBin + 1, this.freqData.length - 1);
    let sum = 0;
    let count = 0;
    for (let i = loBin; i <= hiBin; i++) {
      sum += this.freqData[i];
      count++;
    }
    return count > 0 ? sum / count : 0;
  }

  _computeMetrics() {
    const freq = this.freqData;
    const time = this.timeData;
    const n = freq.length;

    // RMS from time-domain (centered at 128)
    let sumSquares = 0;
    let maxDevi = 0;
    for (let i = 0; i < time.length; i++) {
      const v = (time[i] - 128) / 128;
      sumSquares += v * v;
      const dev = Math.abs(v);
      if (dev > maxDevi) maxDevi = dev;
    }
    const rms = Math.sqrt(sumSquares / time.length);

    // Peak / average / dominant frequency from frequency-domain
    let peak = 0, peakBin = 0, sum = 0;
    for (let i = 0; i < n; i++) {
      const v = freq[i];
      sum += v;
      if (v > peak) { peak = v; peakBin = i; }
    }
    const average = sum / n;

    const bass = this.getBandEnergy(20, 250);
    const mid = this.getBandEnergy(250, 4000);
    const treble = this.getBandEnergy(4000, 16000);

    const sensApplied = (val) => Util.clamp(val * this.sensitivity, 0, 255);

    const m = this.metrics;
    m.rms = rms;
    m.peak = sensApplied(peak) / 255;
    m.average = sensApplied(average) / 255;
    m.peakFreq = this.binToFreq(peakBin);
    m.bass = sensApplied(bass) / 255;
    m.mid = sensApplied(mid) / 255;
    m.treble = sensApplied(treble) / 255;
    m.volume = Util.clamp(rms * this.sensitivity * 140, 0, 100);
    m.db = rms > 0 ? 20 * Math.log10(rms) : -90;
    m.energy = (m.bass * 0.5 + m.mid * 0.3 + m.treble * 0.2);
    m.isSilent = m.volume < 1.2;
  }

  _detectBeat() {
    const energy = this.metrics.bass; // bass-weighted energy works best for beat onset
    const hist = this.beatEnergyHistory;
    hist.push(energy);
    if (hist.length > this.beatHistorySize) hist.shift();

    if (hist.length < 8) return;

    let avg = 0;
    for (let i = 0; i < hist.length; i++) avg += hist[i];
    avg /= hist.length;

    let variance = 0;
    for (let i = 0; i < hist.length; i++) variance += (hist[i] - avg) ** 2;
    variance /= hist.length;

    // Adaptive threshold: more variance => need a bigger spike to count as a beat
    const threshold = 1.5 - 0.0025 * variance * 1000;
    const now = performance.now();

    if (energy > avg * Math.max(threshold, 1.08) && energy > 0.12 && (now - this.lastBeatTime) > 240) {
      if (this.lastBeatTime > 0) {
        const interval = now - this.lastBeatTime;
        if (interval > 240 && interval < 2000) {
          this.beatIntervals.push(interval);
          if (this.beatIntervals.length > 8) this.beatIntervals.shift();
          const avgInterval = this.beatIntervals.reduce((a, b) => a + b, 0) / this.beatIntervals.length;
          this.bpm = Math.round(60000 / avgInterval);
        }
      }
      this.lastBeatTime = now;
      if (this.beatFlashCallback) this.beatFlashCallback(energy);
    }
  }
}

/* ============================================================
   SECTION 3 — THEME MANAGER
   ============================================================ */
class ThemeManager {
  constructor() {
    this.themes = [
      { id: 'phosphor', label: 'Phosphor' },
      { id: 'cyber-purple', label: 'Cyber Purple' },
      { id: 'neon-blue', label: 'Neon Blue' },
      { id: 'synthwave', label: 'Synthwave' },
      { id: 'aurora', label: 'Aurora' },
      { id: 'matrix-green', label: 'Matrix Green' },
      { id: 'fire', label: 'Fire' },
      { id: 'ocean', label: 'Ocean' },
      { id: 'sunset', label: 'Sunset' },
      { id: 'monochrome', label: 'Monochrome' },
      { id: 'sakura', label: 'Sakura' },
      { id: 'ice', label: 'Ice' },
      { id: 'amber', label: 'Amber' },
      { id: 'toxic', label: 'Toxic' },
      { id: 'vaporwave', label: 'Vaporwave' },
      { id: 'lava', label: 'Lava' },
      { id: 'forest', label: 'Forest' },
      { id: 'cotton-candy', label: 'Cotton Candy' },
      { id: 'deep-space', label: 'Deep Space' },
      { id: 'ruby', label: 'Ruby' },
      { id: 'coral-reef', label: 'Coral Reef' },
      { id: 'cyberpunk', label: 'Cyberpunk' },
      { id: 'rainbow', label: 'Rainbow (live cycle)' },
    ];
    this.current = 'deep-space';
    this.lightMode = false;
  }

  populateSelect(selectEl) {
    selectEl.innerHTML = '';
    this.themes.forEach(t => {
      const opt = document.createElement('option');
      opt.value = t.id;
      opt.textContent = t.label;
      selectEl.appendChild(opt);
    });
    selectEl.value = this.current;
  }

  apply(themeId) {
    this.current = themeId;
    document.body.setAttribute('data-theme', themeId);
    // Leaving the live-cycling theme: drop the inline colors it was setting.
    if (themeId !== 'rainbow') {
      ['--accent', '--accent-2', '--accent-3', '--border', '--border-strong', '--grid-line']
        .forEach(v => document.body.style.removeProperty(v));
    }
  }

  static hslToRgb(h, s, l) {
    h = ((h % 360) + 360) % 360 / 360;
    const q = l < 0.5 ? l * (1 + s) : l + s - l * s, p = 2 * l - q;
    const f = (t) => {
      t = (t + 1) % 1;
      if (t < 1 / 6) return p + (q - p) * 6 * t;
      if (t < 1 / 2) return q;
      if (t < 2 / 3) return p + (q - p) * (2 / 3 - t) * 6;
      return p;
    };
    return { r: Math.round(f(h + 1 / 3) * 255), g: Math.round(f(h) * 255), b: Math.round(f(h - 1 / 3) * 255) };
  }

  /** Rainbow theme: hue drifts over time; UI accents are updated ~10x/sec to match. */
  _rainbowColors() {
    const now = performance.now();
    const h = (now / 45) % 360;
    const c = {
      accent: ThemeManager.hslToRgb(h, 1, 0.62),
      accent2: ThemeManager.hslToRgb(h + 120, 1, 0.62),
      accent3: ThemeManager.hslToRgb(h + 240, 1, 0.62),
    };
    if (!this._rbAt || now - this._rbAt > 100) {
      this._rbAt = now;
      const st = document.body.style, rgb = (o) => `rgb(${o.r},${o.g},${o.b})`;
      st.setProperty('--accent', rgb(c.accent));
      st.setProperty('--accent-2', rgb(c.accent2));
      st.setProperty('--accent-3', rgb(c.accent3));
      st.setProperty('--border', `rgba(${c.accent.r},${c.accent.g},${c.accent.b},0.18)`);
      st.setProperty('--border-strong', `rgba(${c.accent.r},${c.accent.g},${c.accent.b},0.34)`);
      st.setProperty('--grid-line', `rgba(${c.accent.r},${c.accent.g},${c.accent.b},0.06)`);
    }
    return c;
  }

  toggleLightMode() {
    this.lightMode = !this.lightMode;
    document.body.classList.toggle('light-mode', this.lightMode);
    return this.lightMode;
  }

  /** Returns the three accent colors as {r,g,b} for canvas drawing, read fresh each call. */
  getAccentColors() {
    if (this.current === 'rainbow') return this._rainbowColors();
    return {
      accent: Util.cssVarRgb('--accent'),
      accent2: Util.cssVarRgb('--accent-2'),
      accent3: Util.cssVarRgb('--accent-3'),
    };
  }
}

/* ============================================================
   SECTION 4 — SETTINGS MANAGER
   Central store for all tunable parameters, with sensible
   defaults. UIController binds inputs to these values.
   ============================================================ */
class SettingsManager {
  constructor() {
    this.values = {
      fftSize: 2048,
      barCount: 64,
      sensitivity: 1,
      gain: 1,
      smoothing: 0.78,
      lineWidth: 2.5,
      glowIntensity: 14,
      particleCount: 600,
      bgBlur: 18,
      mirrorMode: false,
      rotationSpeed: 0.20,
      radius: 100,
      peakHoldTime: 900,
      waveThickness: 2,
      moreLines: false, // Line Graph modes 1 & 2: classic 3-band vs full 7-band detail
      bandRows: 7, // Row count for Orchestra Mode 2 & Line Graph 2 (7 = named bands, 8-40 = log-spaced slices)
      targetFps: 0, // 0 = unlimited (draw every rAF tick); otherwise caps the render loop
      latencyHint: 'interactive', // AudioContext latencyHint — applied on next capture start
    };
    this.listeners = {};
  }

  set(key, value) {
    this.values[key] = value;
    if (this.listeners[key]) this.listeners[key].forEach(fn => fn(value));
  }

  get(key) { return this.values[key]; }

  on(key, fn) {
    if (!this.listeners[key]) this.listeners[key] = [];
    this.listeners[key].push(fn);
  }
}

/* ============================================================
   SECTION 5 — VISUALIZER BASE CLASS
   Each mode extends this. Subclasses implement draw(ctx, audio, dt).
   The base class supplies shared canvas geometry + helpers so each
   mode file doesn't repeat boilerplate.
   ============================================================ */
class Visualizer {
  constructor(ctx, settings, theme) {
    this.ctx = ctx;
    this.settings = settings;
    this.theme = theme;
    this.width = 0;
    this.height = 0;
    this.dpr = 1;
  }

  resize(width, height, dpr) {
    this.width = width;
    this.height = height;
    this.dpr = dpr;
  }

  /** Apply a glow via shadow blur. Cheap & GPU-composited on most browsers. */
  applyGlow(color, intensityMultiplier = 1) {
    const ctx = this.ctx;
    const intensity = this.settings.get('glowIntensity') * intensityMultiplier;
    ctx.shadowBlur = intensity;
    ctx.shadowColor = color;
  }

  clearGlow() {
    this.ctx.shadowBlur = 0;
  }

  reset() { /* override if a mode keeps internal state (particles, trails) */ }

  /** Draws a smooth curve through `points` ({x,y}[], length >= 2) onto an
   *  already-begun path, via quadratic curves through each segment's
   *  midpoint — the standard cheap canvas smoothing trick. Replaces a
   *  straight lineTo-per-point polyline with a flowing curve, independent
   *  of how many points there are. Caller does ctx.beginPath() first (and
   *  any extra moveTo for a filled shape); this does the first moveTo. */
  smoothPath(ctx, points) {
    // Caller must already have positioned the path at points[0] — via
    // ctx.moveTo(points[0].x, points[0].y) for a standalone stroke, or
    // ctx.lineTo(points[0].x, points[0].y) right after a different starting
    // point (e.g. a fill's baseline corner) so the shape stays one
    // continuous subpath. This call only draws the curve through points[1..].
    if (points.length < 2) return;
    for (let i = 1; i < points.length - 1; i++) {
      const mx = (points[i].x + points[i + 1].x) / 2;
      const my = (points[i].y + points[i + 1].y) / 2;
      ctx.quadraticCurveTo(points[i].x, points[i].y, mx, my);
    }
    const last = points[points.length - 1];
    ctx.lineTo(last.x, last.y);
  }
}

/* ---------------- MODE 1: SPECTRUM BARS ---------------- */
class SpectrumBars extends Visualizer {
  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    this.peaks = null;       // current peak height per bar
    this.peakVelocity = null;
    this.peakHoldUntil = null;
    this.smoothedBars = null;
  }

  _ensureArrays(count) {
    if (!this.peaks || this.peaks.length !== count) {
      this.peaks = new Float32Array(count);
      this.peakVelocity = new Float32Array(count);
      this.peakHoldUntil = new Float32Array(count);
      this.smoothedBars = new Float32Array(count);
    }
  }

  draw(audio, now) {
    const ctx = this.ctx;
    const { width, height } = this;
    // Capped at 128: past that, bars get too thin to read even though the
    // shared slider goes up to 256 (other modes, like Circular Spectrum,
    // use the higher end fine).
    const barCount = Math.min(128, this.settings.get('barCount'));
    const mirror = this.settings.get('mirrorMode');
    const peakHoldTime = this.settings.get('peakHoldTime');

    this._ensureArrays(barCount);

    const freq = audio.freqData;
    const binCount = freq.length;
    const gap = Math.max(1, width / barCount * 0.18);
    const barWidth = (width / barCount) - gap;

    const colors = this.theme.getAccentColors();
    const baseline = mirror ? height / 2 : height;

    ctx.clearRect(0, 0, width, height);

    for (let i = 0; i < barCount; i++) {
      // Log-scaled bin mapping so low frequencies aren't crushed into 2px
      const t0 = i / barCount;
      const t1 = (i + 1) / barCount;
      const startBin = Math.floor(Math.pow(t0, 1.6) * binCount);
      const endBin = Math.max(startBin + 1, Math.floor(Math.pow(t1, 1.6) * binCount));

      let sum = 0, cnt = 0;
      for (let b = startBin; b < endBin && b < binCount; b++) { sum += freq[b]; cnt++; }
      const raw = (cnt > 0 ? sum / cnt : 0) / 255 * audio.sensitivity;

      // Adaptive smoothing — bigger jumps move faster than small ones
      const prev = this.smoothedBars[i];
      const diff = raw - prev;
      const smoothFactor = diff > 0 ? 0.55 : 0.18;
      const smoothed = prev + diff * smoothFactor;
      this.smoothedBars[i] = smoothed;

      const barHeight = Util.clamp(smoothed, 0, 1) * (mirror ? height / 2 - 4 : height - 4);
      const x = i * (barWidth + gap);

      // Peak hold + fall-off
      if (barHeight >= this.peaks[i]) {
        this.peaks[i] = barHeight;
        this.peakVelocity[i] = 0;
        this.peakHoldUntil[i] = now + peakHoldTime;
      } else if (now > this.peakHoldUntil[i]) {
        this.peakVelocity[i] += 0.4; // gravity
        this.peaks[i] = Math.max(barHeight, this.peaks[i] - this.peakVelocity[i]);
      }

      // Gradient fill: accent -> accent2 bottom to top
      const grad = ctx.createLinearGradient(0, baseline, 0, baseline - barHeight);
      grad.addColorStop(0, `rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.95)`);
      grad.addColorStop(1, `rgba(${colors.accent2.r},${colors.accent2.g},${colors.accent2.b},0.85)`);

      ctx.fillStyle = grad;
      this.applyGlow(`rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.7)`, 0.6);

      const r = Math.min(barWidth / 2, 5);
      this._roundedBarTop(ctx, x, baseline, barWidth, barHeight, r, mirror ? 1 : -1);

      if (mirror) {
        ctx.globalAlpha = 0.5;
        this._roundedBarTop(ctx, x, baseline, barWidth, barHeight, r, -1);
        ctx.globalAlpha = 1;
      }

      this.clearGlow();

      // Peak indicator
      ctx.fillStyle = `rgba(${colors.accent2.r},${colors.accent2.g},${colors.accent2.b},0.9)`;
      const peakY = mirror ? baseline - this.peaks[i] : baseline - this.peaks[i];
      ctx.fillRect(x, peakY - 2, barWidth, 2);
      if (mirror) ctx.fillRect(x, baseline + this.peaks[i], barWidth, 2);
    }
  }

  /** Draws a vertical bar with rounded top (dir=-1 grows up, dir=1 grows down). */
  _roundedBarTop(ctx, x, baseline, w, h, r, dir) {
    if (h < 1) return;
    const yTop = dir === -1 ? baseline - h : baseline;
    const yBot = dir === -1 ? baseline : baseline + h;
    ctx.beginPath();
    if (dir === -1) {
      ctx.moveTo(x, yBot);
      ctx.lineTo(x, yTop + r);
      ctx.arcTo(x, yTop, x + r, yTop, r);
      ctx.lineTo(x + w - r, yTop);
      ctx.arcTo(x + w, yTop, x + w, yTop + r, r);
      ctx.lineTo(x + w, yBot);
    } else {
      ctx.moveTo(x, yTop);
      ctx.lineTo(x, yBot - r);
      ctx.arcTo(x, yBot, x + r, yBot, r);
      ctx.lineTo(x + w - r, yBot);
      ctx.arcTo(x + w, yBot, x + w, yBot - r, r);
      ctx.lineTo(x + w, yTop);
    }
    ctx.closePath();
    ctx.fill();
  }

  reset() {
    if (this.peaks) this.peaks.fill(0);
    if (this.smoothedBars) this.smoothedBars.fill(0);
  }
}


/* ---------------- MODE 1b: SPECTRUM BARS 2 (LED block segments) ----------------
   Same frequency-column layout and peak-hold logic as Spectrum Bars, but
   each column is a stack of small lit/unlit blocks (classic hardware
   equalizer look) instead of one solid bar — the same idea used for
   Meter Bank 2's segmented meters, applied to the main spectrum view. */
class SpectrumBarsBlocks extends Visualizer {
  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    this.peaks = null;
    this.peakVelocity = null;
    this.peakHoldUntil = null;
    this.smoothedBars = null;
  }

  _ensureArrays(count) {
    if (!this.peaks || this.peaks.length !== count) {
      this.peaks = new Float32Array(count);
      this.peakVelocity = new Float32Array(count);
      this.peakHoldUntil = new Float32Array(count);
      this.smoothedBars = new Float32Array(count);
    }
  }

  draw(audio, now) {
    const ctx = this.ctx;
    const { width, height } = this;
    // Capped at 32: each bar here is already a stack of small segments, so
    // packing in as many columns as the shared slider allows (up to 256)
    // would leave no room for the blocks themselves to read.
    const barCount = Math.min(32, this.settings.get('barCount'));
    const mirror = this.settings.get('mirrorMode');
    const peakHoldTime = this.settings.get('peakHoldTime');

    this._ensureArrays(barCount);

    const freq = audio.freqData;
    const binCount = freq.length;
    const gap = Math.max(1, width / barCount * 0.18);
    const barWidth = (width / barCount) - gap;

    const colors = this.theme.getAccentColors();
    const baseline = mirror ? height / 2 : height;
    const availH = (mirror ? height / 2 : height) - 4;

    const segGap = Util.clamp(barWidth * 0.14, 1, 3);
    const segH = Util.clamp(barWidth * 0.6, 3, 16);
    const segCount = Math.max(6, Math.floor((availH + segGap) / (segH + segGap)));

    ctx.clearRect(0, 0, width, height);

    for (let i = 0; i < barCount; i++) {
      // Same log-scaled bin mapping as the original Spectrum Bars.
      const t0 = i / barCount;
      const t1 = (i + 1) / barCount;
      const startBin = Math.floor(Math.pow(t0, 1.6) * binCount);
      const endBin = Math.max(startBin + 1, Math.floor(Math.pow(t1, 1.6) * binCount));

      let sum = 0, cnt = 0;
      for (let b = startBin; b < endBin && b < binCount; b++) { sum += freq[b]; cnt++; }
      const raw = (cnt > 0 ? sum / cnt : 0) / 255 * audio.sensitivity;

      const prev = this.smoothedBars[i];
      const diff = raw - prev;
      const smoothed = prev + diff * (diff > 0 ? 0.55 : 0.18);
      this.smoothedBars[i] = smoothed;

      const frac = Util.clamp(smoothed, 0, 1);
      const x = i * (barWidth + gap);

      // Peak hold + fall-off (fractional, same shape as the original's
      // pixel-based version)
      if (frac >= this.peaks[i]) {
        this.peaks[i] = frac;
        this.peakVelocity[i] = 0;
        this.peakHoldUntil[i] = now + peakHoldTime;
      } else if (now > this.peakHoldUntil[i]) {
        this.peakVelocity[i] += 0.012;
        this.peaks[i] = Math.max(frac, this.peaks[i] - this.peakVelocity[i]);
      }

      this._drawColumn(ctx, x, baseline, barWidth, -1, frac, this.peaks[i], segCount, segH, segGap, colors);
      if (mirror) {
        ctx.globalAlpha = 0.45;
        this._drawColumn(ctx, x, baseline, barWidth, 1, frac, this.peaks[i], segCount, segH, segGap, colors);
        ctx.globalAlpha = 1;
      }
    }
  }

  /** dir=-1 grows up from baseline (main column); dir=1 grows down (the
   *  dimmed mirror reflection below baseline). Segments are colored in
   *  the same green/amber/red zones as Meter Bank 2, with the lit segment
   *  nearest the peak given a brighter highlight. */
  _drawColumn(ctx, x, baseline, w, dir, frac, peak, segCount, segH, segGap, colors) {
    const lit = Math.round(frac * segCount);
    const peakSeg = Math.round(peak * segCount);
    const r = Math.min(w / 2, 2);

    for (let s = 0; s < segCount; s++) {
      const segFrac = s / segCount;
      const y = baseline + dir * (s * (segH + segGap) + segH) - (dir === -1 ? 0 : segH);
      const on = s < lit;
      const isPeakSeg = s === Math.max(0, peakSeg - 1) && peak > 0.02;

      let col = colors.accent;
      if (segFrac > 0.88) col = colors.accent2;
      else if (segFrac > 0.65) col = colors.accent3;

      if (on || isPeakSeg) {
        ctx.fillStyle = `rgba(${col.r},${col.g},${col.b},${isPeakSeg && !on ? 0.95 : 0.92})`;
        this._roundRect(ctx, x, y, w, segH, r);
        ctx.fill();
        if (on) {
          ctx.fillStyle = `rgba(255,255,255,${segFrac > 0.65 ? 0.22 : 0.14})`;
          this._roundRect(ctx, x, y, w, segH * 0.35, r);
          ctx.fill();
        }
      } else {
        ctx.fillStyle = `rgba(${col.r},${col.g},${col.b},0.08)`;
        this._roundRect(ctx, x, y, w, segH, r);
        ctx.fill();
      }
    }
  }

  _roundRect(ctx, x, y, w, h, r) {
    r = Math.min(r, h / 2, w / 2 > 0 ? w / 2 : r);
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.arcTo(x + w, y, x + w, y + h, r);
    ctx.arcTo(x + w, y + h, x, y + h, r);
    ctx.arcTo(x, y + h, x, y, r);
    ctx.arcTo(x, y, x + w, y, r);
    ctx.closePath();
  }

  reset() {
    if (this.peaks) this.peaks.fill(0);
    if (this.smoothedBars) this.smoothedBars.fill(0);
  }
}

/* ---------------- MODE 2: WAVEFORM (Oscilloscope) ---------------- */
/* ---------------- MODE 2a: WAVEFORM MODE 1 (raw oscilloscope, original) ---------------- */
class WaveformViz1 extends Visualizer {
  draw(audio) {
    const ctx = this.ctx;
    const { width, height } = this;
    const time = audio.timeData;
    const n = time.length;
    const lineWidth = this.settings.get('lineWidth');
    const colors = this.theme.getAccentColors();

    ctx.clearRect(0, 0, width, height);

    const midY = height / 2;
    const ampScale = (height / 2 - 8) * audio.sensitivity;
    const sliceWidth = width / (n - 1);

    ctx.lineWidth = lineWidth;
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    const grad = ctx.createLinearGradient(0, 0, width, 0);
    grad.addColorStop(0, `rgba(${colors.accent3.r},${colors.accent3.g},${colors.accent3.b},0.95)`);
    grad.addColorStop(0.5, `rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.95)`);
    grad.addColorStop(1, `rgba(${colors.accent3.r},${colors.accent3.g},${colors.accent3.b},0.95)`);
    ctx.strokeStyle = grad;
    this.applyGlow(`rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.8)`);

    ctx.beginPath();
    // Smooth bezier curve through time-domain samples
    let prevX = 0, prevY = midY;
    for (let i = 0; i < n; i++) {
      const v = (time[i] - 128) / 128;
      const x = i * sliceWidth;
      const y = midY + v * ampScale;
      if (i === 0) {
        ctx.moveTo(x, y);
      } else {
        const cx = (prevX + x) / 2;
        const cy = (prevY + y) / 2;
        ctx.quadraticCurveTo(prevX, prevY, cx, cy);
      }
      prevX = x; prevY = y;
    }
    ctx.lineTo(width, prevY);
    ctx.stroke();
    this.clearGlow();

    // Faint center line for instrument-panel feel
    ctx.strokeStyle = `rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.12)`;
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.moveTo(0, midY);
    ctx.lineTo(width, midY);
    ctx.stroke();
  }
}

/* ---------------- MODE 2b: WAVEFORM MODE 2 (temporally smoothed, settled) ---------------- */
class WaveformViz2 extends Visualizer {
  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    // Fixed-position sample points across the width (same idea as Orchestra
    // Mode 2): each point's x-position never moves, only its height eases
    // toward the live sample each frame, so the trace settles instead of
    // jittering raw sample-to-sample.
    this.pointCount = 160;
    this.samples = new Float32Array(this.pointCount);
    this._initialized = false;
  }

  draw(audio) {
    const ctx = this.ctx;
    const { width, height } = this;
    const time = audio.timeData;
    const n = time.length;
    const lineWidth = this.settings.get('lineWidth');
    const colors = this.theme.getAccentColors();

    ctx.clearRect(0, 0, width, height);

    const midY = height / 2;
    const ampScale = (height / 2 - 8) * audio.sensitivity;
    const pointCount = this.pointCount;

    // Resample the raw time-domain buffer down to a fixed point count, then
    // ease each fixed point toward its new target instead of redrawing the
    // raw signal directly — this is what removes the frame-to-frame jitter.
    for (let p = 0; p < pointCount; p++) {
      const srcIndex = Math.min(n - 1, Math.floor((p / (pointCount - 1)) * (n - 1)));
      const raw = (time[srcIndex] - 128) / 128;
      const prev = this.samples[p];
      const smoothFactor = this._initialized ? 0.22 : 1; // snap on first frame, ease after
      this.samples[p] = prev + (raw - prev) * smoothFactor;
    }
    this._initialized = true;

    const step = width / (pointCount - 1);

    ctx.lineWidth = lineWidth;
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    const grad = ctx.createLinearGradient(0, 0, width, 0);
    grad.addColorStop(0, `rgba(${colors.accent3.r},${colors.accent3.g},${colors.accent3.b},0.95)`);
    grad.addColorStop(0.5, `rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.95)`);
    grad.addColorStop(1, `rgba(${colors.accent3.r},${colors.accent3.g},${colors.accent3.b},0.95)`);
    ctx.strokeStyle = grad;
    this.applyGlow(`rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.8)`);

    ctx.beginPath();
    let prevX = 0, prevY = midY;
    for (let p = 0; p < pointCount; p++) {
      const x = p * step;
      const y = midY + this.samples[p] * ampScale;
      if (p === 0) {
        ctx.moveTo(x, y);
      } else {
        const cx = (prevX + x) / 2;
        const cy = (prevY + y) / 2;
        ctx.quadraticCurveTo(prevX, prevY, cx, cy);
      }
      prevX = x; prevY = y;
    }
    ctx.lineTo(width, prevY);
    ctx.stroke();
    this.clearGlow();

    // Faint center line for instrument-panel feel
    ctx.strokeStyle = `rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.12)`;
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.moveTo(0, midY);
    ctx.lineTo(width, midY);
    ctx.stroke();
  }

  reset() {
    this.samples.fill(0);
    this._initialized = false;
  }
}

/* ---------------- MODE 3: CIRCULAR SPECTRUM ---------------- */
class CircularVisualizer extends Visualizer {
  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    this.rotation = 0;
    this.particles = [];
    this.smoothedBars = null;
    this.pulseRadius = 0;
  }

  _ensureParticles(count) {
    if (this.particles.length === count) return;
    this.particles = [];
    for (let i = 0; i < count; i++) {
      this.particles.push({ angle: (i / count) * Math.PI * 2, dist: 0, speed: 0.3 + Math.random() * 0.4 });
    }
  }

  draw(audio, now, dt) {
    const ctx = this.ctx;
    const { width, height } = this;
    const cx = width / 2, cy = height / 2;
    const baseRadius = this.settings.get('radius') * (Math.min(width, height) / 480);
    const rotSpeed = this.settings.get('rotationSpeed');
    const barCount = Math.max(32, this.settings.get('barCount'));
    const colors = this.theme.getAccentColors();
    const freq = audio.freqData;
    const binCount = freq.length;

    if (!this.smoothedBars || this.smoothedBars.length !== barCount) {
      this.smoothedBars = new Float32Array(barCount);
    }

    ctx.clearRect(0, 0, width, height);
    this.rotation += rotSpeed * dt * 0.001;

    // Rotating outer glow ring
    const ringGrad = ctx.createRadialGradient(cx, cy, baseRadius * 0.5, cx, cy, baseRadius * 1.9);
    ringGrad.addColorStop(0, `rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.08)`);
    ringGrad.addColorStop(1, 'rgba(0,0,0,0)');
    ctx.fillStyle = ringGrad;
    ctx.beginPath();
    ctx.arc(cx, cy, baseRadius * 1.9, 0, Math.PI * 2);
    ctx.fill();

    // Radial FFT bars
    for (let i = 0; i < barCount; i++) {
      const t0 = i / barCount, t1 = (i + 1) / barCount;
      const startBin = Math.floor(Math.pow(t0, 1.5) * binCount);
      const endBin = Math.max(startBin + 1, Math.floor(Math.pow(t1, 1.5) * binCount));
      let sum = 0, cnt = 0;
      for (let b = startBin; b < endBin && b < binCount; b++) { sum += freq[b]; cnt++; }
      const raw = (cnt > 0 ? sum / cnt : 0) / 255 * audio.sensitivity;

      const prev = this.smoothedBars[i];
      const smoothed = prev + (raw - prev) * (raw > prev ? 0.5 : 0.15);
      this.smoothedBars[i] = smoothed;

      const angle = (i / barCount) * Math.PI * 2 + this.rotation;
      const barLen = smoothed * baseRadius * 1.1;
      const x0 = cx + Math.cos(angle) * baseRadius;
      const y0 = cy + Math.sin(angle) * baseRadius;
      const x1 = cx + Math.cos(angle) * (baseRadius + barLen);
      const y1 = cy + Math.sin(angle) * (baseRadius + barLen);

      const hue = Util.lerp(0, 1, i / barCount);
      ctx.strokeStyle = `rgba(${Util.lerp(colors.accent.r, colors.accent3.r, hue)},${Util.lerp(colors.accent.g, colors.accent3.g, hue)},${Util.lerp(colors.accent.b, colors.accent3.b, hue)},0.9)`;
      ctx.lineWidth = Math.max(1.5, (Math.PI * 2 * baseRadius / barCount) * 0.6);
      ctx.lineCap = 'round';
      ctx.beginPath();
      ctx.moveTo(x0, y0);
      ctx.lineTo(x1, y1);
      ctx.stroke();
    }

    // Center pulse (reacts to bass)
    const targetPulse = baseRadius * (0.55 + audio.metrics.bass * 0.5);
    this.pulseRadius += (targetPulse - this.pulseRadius) * 0.18;
    const pulseGrad = ctx.createRadialGradient(cx, cy, 0, cx, cy, this.pulseRadius);
    pulseGrad.addColorStop(0, `rgba(${colors.accent2.r},${colors.accent2.g},${colors.accent2.b},0.55)`);
    pulseGrad.addColorStop(1, `rgba(${colors.accent2.r},${colors.accent2.g},${colors.accent2.b},0)`);
    ctx.fillStyle = pulseGrad;
    this.applyGlow(`rgba(${colors.accent2.r},${colors.accent2.g},${colors.accent2.b},0.6)`, 1.2);
    ctx.beginPath();
    ctx.arc(cx, cy, this.pulseRadius, 0, Math.PI * 2);
    ctx.fill();
    this.clearGlow();

    // Album-art placeholder ring (subtle bezel)
    ctx.strokeStyle = `rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.25)`;
    ctx.lineWidth = 1.5;
    ctx.beginPath();
    ctx.arc(cx, cy, baseRadius * 0.5, 0, Math.PI * 2);
    ctx.stroke();

    // Particle ring
    this._ensureParticles(48);
    for (const p of this.particles) {
      p.angle += p.speed * dt * 0.0008;
      const targetDist = baseRadius * (1.15 + audio.metrics.treble * 0.4);
      p.dist += (targetDist - p.dist) * 0.06;
      const x = cx + Math.cos(p.angle) * p.dist;
      const y = cy + Math.sin(p.angle) * p.dist;
      ctx.fillStyle = `rgba(${colors.accent3.r},${colors.accent3.g},${colors.accent3.b},0.7)`;
      ctx.beginPath();
      ctx.arc(x, y, 1.6 + audio.metrics.treble * 2, 0, Math.PI * 2);
      ctx.fill();
    }
  }

  reset() {
    if (this.smoothedBars) this.smoothedBars.fill(0);
    this.pulseRadius = 0;
  }
}

/* ---------------- MODE 4: LINE GRAPH (scrolling frequency history) ---------------- */
/* ---------------- MODE: LINE GRAPH 1 (scrolling history, original) ---------------- */
/* ---------------- MODE: LINE GRAPH 1 (real-time, anchored — no scroll/delay) ---------------- */
/* ---------------- MODE: LINE GRAPH 1 (sweep style, wraps left→right) ---------------- */
/* ---------------- MODE: LINE GRAPH 1 (sweep style, 3 or 7 stacked rows) ---------------- */
class LineGraphV1 extends Visualizer {
  // Classic 3-lane band set, used when the "more lines" toggle is off.
  static CLASSIC_BANDS = [
    { name: 'Bass', lo: 20, hi: 250 },
    { name: 'Mid', lo: 250, hi: 4000 },
    { name: 'Treble', lo: 4000, hi: 16000 },
  ];

  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    this.maxPoints = 220;
    // Fixed-position circular buffers — a sweep cursor writes into them and
    // wraps, instead of the whole trace scrolling sideways. Pre-allocated
    // for the full 7-band detailed view; the classic view just uses the
    // first 3.
    this.bandCount = 7;
    this.buffers = Array.from({ length: this.bandCount }, () => new Float32Array(this.maxPoints));
    this.writeIndex = 0;
  }

  draw(audio) {
    const ctx = this.ctx;
    const { width, height } = this;
    const colors = this.theme.getAccentColors();
    const moreLines = this.settings.get('moreLines');

    ctx.clearRect(0, 0, width, height);

    const n = this.maxPoints;
    const step = width / (n - 1);

    // --- classic (3-line) vs detailed (7-line, full band breakdown) ---
    const bands = moreLines ? audio.bandDefs : LineGraphV1.CLASSIC_BANDS;
    const rowCount = bands.length;
    const labels = bands.map(b => b.name.toUpperCase());
    const colorFor = moreLines
      ? (idx) => idx < 2 ? colors.accent : idx < 5 ? colors.accent3 : colors.accent2
      : (idx) => [colors.accent, colors.accent3, colors.accent2][idx];
    const energyFor = moreLines
      ? (idx) => audio.getBandEnergy(bands[idx].lo, bands[idx].hi) / 255 * audio.sensitivity
      : (idx) => idx === 0 ? audio.metrics.bass : idx === 1 ? audio.metrics.mid : audio.metrics.treble;

    // Write the latest sample at the shared sweep cursor for every active row.
    for (let r = 0; r < rowCount; r++) {
      this.buffers[r][this.writeIndex] = energyFor(r);
    }

    const rowGap = moreLines ? 4 : 8;
    const padY = moreLines ? 6 : 8;
    const weights = moreLines ? new Array(rowCount).fill(1) : [1.7, 1, 1];
    const totalWeight = weights.reduce((a, b) => a + b, 0);
    const availableHeight = height - rowGap * (rowCount - 1);
    const rowHeights = weights.map(w => (w / totalWeight) * availableHeight);

    let cursorY = 0;
    const rowYs = rowHeights.map(h => {
      const y = cursorY;
      cursorY += h + rowGap;
      return y;
    });

    for (let idx = 0; idx < rowCount; idx++) {
      const buf = this.buffers[idx];
      const c = colorFor(idx);
      const rowY = rowYs[idx];
      const rowHeight = rowHeights[idx];
      const baseY = rowY + rowHeight - padY;
      const topY = rowY + padY;
      const ampRange = baseY - topY;

      // Row background card
      ctx.fillStyle = `rgba(${c.r},${c.g},${c.b},0.04)`;
      ctx.fillRect(0, rowY, width, rowHeight);

      // Per-row grid
      ctx.strokeStyle = `rgba(${c.r},${c.g},${c.b},0.08)`;
      ctx.lineWidth = 1;
      const gridLines = moreLines ? 3 : 4;
      for (let g = 0; g <= gridLines; g++) {
        const y = topY + (ampRange / gridLines) * g;
        ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(width, y); ctx.stroke();
      }
      const cols = 12;
      for (let g = 0; g <= cols; g++) {
        const x = (width / cols) * g;
        ctx.beginPath(); ctx.moveTo(x, rowY); ctx.lineTo(x, rowY + rowHeight); ctx.stroke();
      }

      ctx.save();
      ctx.beginPath();
      ctx.rect(0, rowY, width, rowHeight);
      ctx.clip();

      ctx.lineWidth = moreLines ? 1.6 : 2;
      ctx.lineJoin = 'round';
      ctx.lineCap = 'round';
      this.applyGlow(`rgba(${c.r},${c.g},${c.b},0.6)`, 0.5);

      // Everything the sweep has already passed over this lap (to the left
      // of the cursor) stays visible the whole way back to the start of
      // the sweep — a much longer trail than a short comet, fading only
      // gently so the full history reads clearly. Nothing to the right of
      // the cursor is drawn: those points haven't been swept yet this lap
      // and still hold last lap's stale values, so that side stays clear
      // until the cursor actually reaches it.
      for (let i = 1; i <= this.writeIndex; i++) {
        const prevIdx = i - 1;
        const age = this.writeIndex - i; // 0 right at the cursor, growing toward the left edge
        const alpha = 0.4 + 0.6 * (1 - age / Math.max(1, this.writeIndex));

        const x0 = prevIdx * step, x1 = i * step;
        const y0 = baseY - buf[prevIdx] * ampRange;
        const y1 = baseY - buf[i] * ampRange;

        ctx.strokeStyle = `rgba(${c.r},${c.g},${c.b},${alpha})`;
        ctx.beginPath();
        ctx.moveTo(x0, y0);
        ctx.lineTo(x1, y1);
        ctx.stroke();
      }
      this.clearGlow();

      // Sweep cursor dot
      const cx = this.writeIndex * step;
      const cy = baseY - buf[this.writeIndex] * ampRange;
      ctx.fillStyle = `rgba(${c.r},${c.g},${c.b},1)`;
      ctx.beginPath();
      ctx.arc(cx, cy, moreLines ? 2 : 2.5, 0, Math.PI * 2);
      ctx.fill();

      ctx.restore();

      // Row label + live readout
      ctx.font = `600 ${moreLines ? 10 : 11}px "JetBrains Mono", monospace`;
      ctx.fillStyle = `rgba(${c.r},${c.g},${c.b},0.9)`;
      ctx.fillText(labels[idx], 10, rowY + (moreLines ? 13 : 16));

      const current = buf[this.writeIndex];
      ctx.font = `500 ${moreLines ? 9 : 10}px "JetBrains Mono", monospace`;
      ctx.textAlign = 'right';
      ctx.fillStyle = `rgba(${c.r},${c.g},${c.b},0.7)`;
      ctx.fillText(`${Math.round(current * 100)}%`, width - 10, rowY + (moreLines ? 13 : 16));
      ctx.textAlign = 'left';
    }

    // Advance the shared cursor; wraps to 0 at the right edge of every row,
    // which is also what makes the trail clear and start rebuilding from
    // the left again on the next lap.
    this.writeIndex = (this.writeIndex + 1) % n;
  }

  reset() {
    for (const buf of this.buffers) buf.fill(0);
    this.writeIndex = 0;
  }
}

/* ---------------- MODE: LINE GRAPH 2 (static, anchored in place) ---------------- */
class LineGraphV2 extends Visualizer {
  // Classic 3-lane band set, used when the "more lines" toggle is off.
  static CLASSIC_BANDS = [
    { name: 'Bass', lo: 20, hi: 250 },
    { name: 'Mid', lo: 250, hi: 4000 },
    { name: 'Treble', lo: 4000, hi: 16000 },
  ];

  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    // Fixed-position sample points (NOT a scrolling history) per row.
    this.pointsPerTrace = 40;
    this.bandCount = 0; // forces _ensureRows to allocate on first draw
    this._ensureRows(3);
  }

  // Row count follows settings.bandRows once "more lines" is on (7-40); the
  // classic 3-band view always uses exactly 3. Reallocated only when the
  // count actually changes.
  _ensureRows(count) {
    if (count === this.bandCount) return;
    this.bandCount = count;
    this.traceSamples = Array.from({ length: count }, () => new Float32Array(this.pointsPerTrace));
  }

  draw(audio) {
    const ctx = this.ctx;
    const { width, height } = this;
    const colors = this.theme.getAccentColors();
    const moreLines = this.settings.get('moreLines');
    const rowCountSetting = Util.clamp(Math.round(this.settings.get('bandRows') || 7), 7, 40);
    const bands = moreLines
      ? (rowCountSetting === 7 ? audio.bandDefs : audio.getDynamicBands(rowCountSetting))
      : LineGraphV2.CLASSIC_BANDS;
    this._ensureRows(bands.length);

    ctx.clearRect(0, 0, width, height);

    const n = this.pointsPerTrace;
    const rowCount = bands.length;
    const rowGap = moreLines ? 4 : 8;
    const padY = moreLines ? 7 : 9;
    const rowHeight = (height - rowGap * (rowCount - 1)) / rowCount;
    const step = width / (n - 1);

    for (let idx = 0; idx < rowCount; idx++) {
      const samples = this.traceSamples[idx];
      const band = bands[idx];
      const span = band.hi - band.lo;
      const rowY = idx * (rowHeight + rowGap);
      const baseY = rowY + rowHeight - padY;
      const topY = rowY + padY;
      // Same 3-way color cycling used across the rest of the app's 7-band
      // views (low bands warm toward accent, mids toward accent3, highs
      // toward accent2) so this mode reads consistently with Orchestra;
      // with only 3 rows this lines up with the original bass/mid/treble
      // coloring too.
      const c = rowCount <= 3
        ? [colors.accent, colors.accent3, colors.accent2][idx]
        : idx < 2 ? colors.accent : idx < 5 ? colors.accent3 : colors.accent2;

      // Row background card
      ctx.fillStyle = `rgba(${c.r},${c.g},${c.b},0.04)`;
      ctx.fillRect(0, rowY, width, rowHeight);

      // Per-row grid (own baseline, independent of the other rows)
      ctx.strokeStyle = `rgba(${c.r},${c.g},${c.b},0.08)`;
      ctx.lineWidth = 1;
      const gridLines = moreLines ? 3 : 4;
      for (let g = 0; g <= gridLines; g++) {
        const y = topY + ((baseY - topY) / gridLines) * g;
        ctx.beginPath(); ctx.moveTo(0, y); ctx.lineTo(width, y); ctx.stroke();
      }
      const cols = moreLines ? 16 : 12;
      for (let g = 0; g <= cols; g++) {
        const x = (width / cols) * g;
        ctx.beginPath(); ctx.moveTo(x, rowY); ctx.lineTo(x, rowY + rowHeight); ctx.stroke();
      }

      // Sample n fixed points across this band's own Hz range — only the
      // height at each fixed x updates frame to frame, never the x itself.
      for (let p = 0; p < n; p++) {
        const loP = band.lo + (p / n) * span;
        const hiP = band.lo + ((p + 1) / n) * span;
        const raw = audio.getBandEnergy(loP, hiP) / 255 * audio.sensitivity;
        const prev = samples[p];
        samples[p] = prev + (raw - prev) * (raw > prev ? 0.5 : 0.15);
      }

      // Filled area under the trace, scoped to this row only
      ctx.save();
      ctx.beginPath();
      ctx.rect(0, rowY, width, rowHeight);
      ctx.clip();

      const tracePts = [];
      for (let p = 0; p < n; p++) {
        tracePts.push({ x: p * step, y: baseY - samples[p] * (baseY - topY) });
      }
      ctx.beginPath();
      ctx.moveTo(0, baseY);
      ctx.lineTo(tracePts[0].x, tracePts[0].y);
      this.smoothPath(ctx, tracePts);
      ctx.lineTo((n - 1) * step, baseY);
      ctx.closePath();
      const grad = ctx.createLinearGradient(0, topY, 0, baseY);
      grad.addColorStop(0, `rgba(${c.r},${c.g},${c.b},0.30)`);
      grad.addColorStop(1, `rgba(${c.r},${c.g},${c.b},0.02)`);
      ctx.fillStyle = grad;
      ctx.fill();

      // Trace line itself
      ctx.strokeStyle = `rgba(${c.r},${c.g},${c.b},0.9)`;
      ctx.lineWidth = 1.6;
      ctx.lineJoin = 'round';
      this.applyGlow(`rgba(${c.r},${c.g},${c.b},0.6)`, 0.45);
      ctx.beginPath();
      ctx.moveTo(tracePts[0].x, tracePts[0].y);
      this.smoothPath(ctx, tracePts);
      ctx.stroke();
      this.clearGlow();
      ctx.restore();

      // Row label + live readout
      ctx.font = `600 ${moreLines ? 10 : 11}px "JetBrains Mono", monospace`;
      ctx.fillStyle = `rgba(${c.r},${c.g},${c.b},0.9)`;
      ctx.fillText(band.name.toUpperCase(), 10, rowY + (moreLines ? 13 : 16));

      const current = samples[n - 1];
      ctx.font = `500 ${moreLines ? 9 : 10}px "JetBrains Mono", monospace`;
      ctx.textAlign = 'right';
      ctx.fillStyle = `rgba(${c.r},${c.g},${c.b},0.7)`;
      ctx.fillText(`${Math.round(current * 100)}%`, width - 10, rowY + (moreLines ? 13 : 16));
      ctx.textAlign = 'left';
    }
  }

  reset() {
    for (const arr of this.traceSamples) arr.fill(0);
  }
}

/* ---------------- MODE 5: PARTICLE VISUALIZER ---------------- */
class ParticleViz extends Visualizer {
  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    this.particles = [];
  }

  _ensure(count) {
    while (this.particles.length < count) {
      this.particles.push(this._spawn());
    }
    if (this.particles.length > count) this.particles.length = count;
  }

  _spawn() {
    return {
      x: Math.random() * this.width,
      y: Math.random() * this.height,
      vx: (Math.random() - 0.5) * 0.4,
      vy: (Math.random() - 0.5) * 0.4,
      baseSize: 0.8 + Math.random() * 1.6,
      hueT: Math.random(),
    };
  }

  draw(audio, now, dt) {
    const ctx = this.ctx;
    const { width, height } = this;
    const count = this.settings.get('particleCount');
    const colors = this.theme.getAccentColors();
    this._ensure(count);

    // Trail effect via low-alpha overpaint (motion blur). Note: this canvas is
    // created with {alpha:false}, so 'destination-out' compositing has no
    // alpha channel to act on — a plain semi-transparent fill fades old
    // pixels toward black instead, which reads the same visually.
    ctx.fillStyle = 'rgba(0,0,0,0.18)';
    ctx.fillRect(0, 0, width, height);

    const bass = audio.metrics.bass, mid = audio.metrics.mid, treble = audio.metrics.treble;
    const speedMul = 1 + treble * 3;
    const sizeMul = 1 + bass * 2.6;

    for (const p of this.particles) {
      p.x += p.vx * speedMul * (dt * 0.06);
      p.y += p.vy * speedMul * (dt * 0.06);

      if (p.x < 0) p.x += width;
      if (p.x > width) p.x -= width;
      if (p.y < 0) p.y += height;
      if (p.y > height) p.y -= height;

      const size = p.baseSize * sizeMul;
      const r = Util.lerp(colors.accent.r, colors.accent3.r, Util.lerp(p.hueT, mid, 0.5));
      const g = Util.lerp(colors.accent.g, colors.accent3.g, Util.lerp(p.hueT, mid, 0.5));
      const b = Util.lerp(colors.accent.b, colors.accent3.b, Util.lerp(p.hueT, mid, 0.5));

      ctx.fillStyle = `rgba(${r},${g},${b},${0.55 + bass * 0.4})`;
      ctx.beginPath();
      ctx.arc(p.x, p.y, size, 0, Math.PI * 2);
      ctx.fill();
    }

    // Occasional connecting lines on strong beats for cohesion (cheap O(n) sampled pairs)
    if (bass > 0.45) {
      ctx.strokeStyle = `rgba(${colors.accent2.r},${colors.accent2.g},${colors.accent2.b},${0.12 * bass})`;
      ctx.lineWidth = 1;
      ctx.beginPath();
      for (let i = 0; i < this.particles.length; i += 9) {
        const a = this.particles[i];
        const b2 = this.particles[(i + 9) % this.particles.length];
        ctx.moveTo(a.x, a.y);
        ctx.lineTo(b2.x, b2.y);
      }
      ctx.stroke();
    }
  }

  reset() { this.particles = []; }
}

/* ---------------- MODE 6: ORCHESTRA MODE (multi-band meter bank) ---------------- */
/* ---------------- shared helpers for both Orchestra variants ---------------- */
class OrchestraBase extends Visualizer {
  _roundRect(ctx, x, y, w, h, r) {
    r = Math.min(r, h / 2, w / 2 > 0 ? w / 2 : r);
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.arcTo(x + w, y, x + w, y + h, r);
    ctx.arcTo(x + w, y + h, x, y + h, r);
    ctx.arcTo(x, y + h, x, y, r);
    ctx.arcTo(x, y, x + w, y, r);
    ctx.closePath();
  }

  /** Minimal glyph set so we don't need external icon assets. */
  _drawBandGlyph(ctx, cx, cy, type, colors, energy) {
    ctx.save();
    ctx.translate(cx, cy);
    ctx.lineWidth = 1.4;
    ctx.strokeStyle = ctx.fillStyle;
    const s = 5 + energy * 2;
    switch (type) {
      case 'sub':
        ctx.beginPath(); ctx.arc(0, 0, s * 0.9, 0, Math.PI * 2); ctx.fill(); break;
      case 'bass':
        ctx.beginPath(); ctx.arc(0, 0, s * 0.7, 0, Math.PI * 2); ctx.stroke();
        ctx.beginPath(); ctx.arc(0, 0, s * 0.3, 0, Math.PI * 2); ctx.fill(); break;
      case 'lowmid':
        ctx.beginPath(); ctx.moveTo(-s, 3); ctx.lineTo(0, -s); ctx.lineTo(s, 3); ctx.closePath(); ctx.fill(); break;
      case 'mid':
        ctx.beginPath(); ctx.rect(-s * 0.7, -s * 0.7, s * 1.4, s * 1.4); ctx.fill(); break;
      case 'highmid':
        ctx.beginPath();
        for (let i = 0; i < 5; i++) {
          const a = (i / 5) * Math.PI * 2 - Math.PI / 2;
          const x = Math.cos(a) * s, y = Math.sin(a) * s;
          if (i === 0) ctx.moveTo(x, y); else ctx.lineTo(x, y);
        }
        ctx.closePath(); ctx.fill(); break;
      case 'presence':
        ctx.beginPath(); ctx.moveTo(-s, -s * 0.5); ctx.lineTo(s, -s * 0.5); ctx.lineTo(0, s); ctx.closePath(); ctx.fill(); break;
      case 'volume':
        // three ascending bars — a plain signal/level glyph
        ctx.fillRect(-s * 0.95, s * 0.15, s * 0.5, s * 0.65);
        ctx.fillRect(-s * 0.2, -s * 0.35, s * 0.5, s * 1.15);
        ctx.fillRect(s * 0.55, -s * 0.85, s * 0.5, s * 1.65);
        break;
      case 'freq':
        // small sine-wave glyph
        ctx.beginPath();
        ctx.moveTo(-s, 0);
        ctx.bezierCurveTo(-s * 0.5, -s * 1.3, -s * 0.15, s * 1.3, s * 0.1, 0);
        ctx.bezierCurveTo(s * 0.35, -s * 1.3, s * 0.65, s * 1.3, s, 0);
        ctx.lineWidth = 1.5;
        ctx.stroke();
        break;
      case 'peak':
        // a single sharp spike — the loudest instant, not a smoothed level
        ctx.beginPath(); ctx.moveTo(-s, s * 0.7); ctx.lineTo(0, -s); ctx.lineTo(s, s * 0.7); ctx.closePath(); ctx.fill();
        break;
      case 'range':
        // double-headed vertical arrow — the spread between peak and average
        ctx.lineWidth = 1.5;
        ctx.beginPath(); ctx.moveTo(0, -s); ctx.lineTo(0, s); ctx.stroke();
        ctx.beginPath(); ctx.moveTo(-s * 0.4, -s * 0.6); ctx.lineTo(0, -s); ctx.lineTo(s * 0.4, -s * 0.6); ctx.stroke();
        ctx.beginPath(); ctx.moveTo(-s * 0.4, s * 0.6); ctx.lineTo(0, s); ctx.lineTo(s * 0.4, s * 0.6); ctx.stroke();
        break;
      case 'bpm':
        // a heartbeat/pulse zigzag
        ctx.lineWidth = 1.5;
        ctx.beginPath();
        ctx.moveTo(-s, 0); ctx.lineTo(-s * 0.35, 0); ctx.lineTo(-s * 0.1, -s); ctx.lineTo(s * 0.2, s); ctx.lineTo(s * 0.45, 0); ctx.lineTo(s, 0);
        ctx.stroke();
        break;
      case 'brilliance':
      default:
        for (let i = 0; i < 4; i++) {
          const a = (i / 4) * Math.PI * 2;
          ctx.beginPath();
          ctx.moveTo(0, 0);
          ctx.lineTo(Math.cos(a) * s, Math.sin(a) * s);
          ctx.lineWidth = 1.6;
          ctx.stroke();
        }
        break;
    }
    ctx.restore();
  }


  /** A classic LED/VU-style bank of individually lit segments instead of one
   *  continuous bar (used by Meter Bank 2 and Signal Meter) — a lot more
   *  "bars" to look at per row, and the per-segment coloring (green through
   *  the middle, amber near the top, red at the very top) reads peaks at a
   *  glance the way a single smooth bar doesn't. `valueLabelOverride` lets a
   *  row show something other than dB (e.g. "67%" or "212Hz"). */
  _drawSegmentedMeter(ctx, width, rightColW, y, rowHeight, smoothed, peak, colors, c, valueLabelOverride) {
    const pad = 10;
    const meterX = width - rightColW + pad;
    const meterW = rightColW - pad * 1.6;
    const segGap = rowHeight > 24 ? 3 : 2;
    const segH = Util.clamp(rowHeight * 0.6, 8, 28);
    const meterY = y + rowHeight / 2 - segH / 2;
    const segW = Util.clamp((rowHeight > 24 ? 10 : 7), 4, 14);
    const segCount = Math.max(8, Math.floor((meterW + segGap) / (segW + segGap)));
    const lit = Math.round(Util.clamp(smoothed, 0, 1) * segCount);
    const peakSeg = Math.round(Util.clamp(peak, 0, 1) * segCount);

    for (let s = 0; s < segCount; s++) {
      const x = meterX + s * (segW + segGap);
      const frac = s / segCount;
      const on = s < lit;
      const isPeakSeg = s === Math.max(0, peakSeg - 1) && peak > 0.02;
      let col = c;
      if (frac > 0.88) col = colors.accent2;       // red zone near the top
      else if (frac > 0.65) col = colors.accent3;  // amber zone

      if (on || isPeakSeg) {
        ctx.fillStyle = `rgba(${col.r},${col.g},${col.b},${isPeakSeg && !on ? 0.95 : 0.92})`;
        this._roundRect(ctx, x, meterY, segW, segH, 2);
        ctx.fill();
        if (on) {
          ctx.fillStyle = `rgba(255,255,255,${frac > 0.65 ? 0.22 : 0.14})`;
          this._roundRect(ctx, x, meterY, segW, segH * 0.4, 2);
          ctx.fill();
        }
      } else {
        ctx.fillStyle = `rgba(${col.r},${col.g},${col.b},0.08)`;
        this._roundRect(ctx, x, meterY, segW, segH, 2);
        ctx.fill();
      }
    }

    const label = valueLabelOverride !== undefined
      ? valueLabelOverride
      : `${smoothed > 0.001 ? (20 * Math.log10(smoothed)).toFixed(0) : '-∞'}dB`;
    ctx.font = `500 9px "JetBrains Mono", monospace`;
    ctx.fillStyle = `rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.6)`;
    ctx.textAlign = 'right';
    ctx.textBaseline = 'middle';
    ctx.fillText(label, width - 4, y + rowHeight / 2);
    ctx.textAlign = 'left';
  }

  /** Shared left-column icon + label + caption, identical in both variants.
   *  By default the caption is the band's Hz range; pass `captionOverride`
   *  for a row that isn't a frequency band at all (e.g. Meter Bank 2's
   *  Volume/Frequency rows), to show a live reading instead. */
  _drawLeftColumn(ctx, band, y, rowHeight, colors, smoothed, captionOverride) {
    ctx.save();
    ctx.fillStyle = `rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},${0.5 + smoothed * 0.5})`;
    ctx.font = '600 12px "Space Grotesk", sans-serif';
    ctx.textBaseline = 'middle';
    this._drawBandGlyph(ctx, 16, y + rowHeight / 2, band.icon, colors, smoothed);
    ctx.fillStyle = `rgba(${colors.accent.r + 40},${colors.accent.g + 40},${colors.accent.b + 40},0.92)`;
    ctx.fillText(band.name, 40, y + rowHeight / 2);
    ctx.font = '400 9px "JetBrains Mono", monospace';
    ctx.fillStyle = `rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.45)`;
    const caption = captionOverride !== undefined
      ? captionOverride
      : `${band.lo}–${band.hi >= 1000 ? (band.hi / 1000) + 'k' : band.hi}Hz`;
    ctx.fillText(caption, 40, y + rowHeight / 2 + 13);
    ctx.restore();
  }

  /** Shared right-column dB/% meter + peak tick, used by all Orchestra-style
   *  variants. `barHeight` lets a mode with more room to spare (Orchestra 2,
   *  Meter Bank) draw a chunkier bar than the default. */
  _drawRightMeter(ctx, width, rightColW, y, rowHeight, smoothed, peak, colors, c, barHeight = 8) {
    const meterX = width - rightColW + 10;
    const meterW = rightColW - 24;
    const meterY = y + rowHeight / 2 - barHeight / 2;
    const r = barHeight / 2;

    ctx.fillStyle = `rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.12)`;
    this._roundRect(ctx, meterX, meterY, meterW, barHeight, r);
    ctx.fill();

    ctx.fillStyle = `rgba(${c.r},${c.g},${c.b},0.9)`;
    this._roundRect(ctx, meterX, meterY, meterW * Util.clamp(smoothed, 0, 1), barHeight, r);
    ctx.fill();

    const peakX = meterX + meterW * Util.clamp(peak, 0, 1);
    ctx.fillStyle = `rgba(${colors.accent2.r},${colors.accent2.g},${colors.accent2.b},0.95)`;
    ctx.fillRect(peakX - 1, meterY - 2, 2, barHeight + 4);

    const db = smoothed > 0.001 ? (20 * Math.log10(smoothed)).toFixed(0) : '-∞';
    const fontSize = barHeight > 14 ? 11 : 9;
    ctx.font = `500 ${fontSize}px "JetBrains Mono", monospace`;
    ctx.fillStyle = `rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.7)`;
    ctx.textAlign = 'right';
    ctx.fillText(`${db}dB  ${Math.round(smoothed * 100)}%`, width - 14, meterY + barHeight + 10);
    ctx.textAlign = 'left';
  }
}

/* ---------------- MODE 6: ORCHESTRA MODE 1 (scrolling history, original) ---------------- */
class OrchestraModeV1 extends OrchestraBase {
  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    this.bandSmoothed = new Float32Array(7);
    this.bandPeaks = new Float32Array(7);
    this.bandPeakHold = new Float32Array(7);
    // Scrolling history buffer per row — each new sample pushes in from the
    // right and the whole trace crawls left, like a seismograph feed.
    this.waveHistories = [[], [], [], [], [], [], []];
    this.historyLen = 64;
  }

  draw(audio, now) {
    const ctx = this.ctx;
    const { width, height } = this;
    const colors = this.theme.getAccentColors();
    const bands = audio.bandDefs;
    const rowCount = bands.length;
    const rowGap = 4;
    const rowHeight = (height - rowGap * (rowCount - 1)) / rowCount;

    ctx.clearRect(0, 0, width, height);

    const leftColW = Math.min(150, width * 0.22);
    const rightColW = Math.min(110, width * 0.16);
    const centerX = leftColW;
    const centerW = width - leftColW - rightColW;

    for (let i = 0; i < rowCount; i++) {
      const band = bands[i];
      const y = i * (rowHeight + rowGap);
      const energy = audio.getBandEnergy(band.lo, band.hi) / 255 * audio.sensitivity;

      const prev = this.bandSmoothed[i];
      const smoothed = prev + (energy - prev) * (energy > prev ? 0.45 : 0.12);
      this.bandSmoothed[i] = smoothed;

      if (smoothed >= this.bandPeaks[i]) {
        this.bandPeaks[i] = smoothed;
        this.bandPeakHold[i] = now + 900;
      } else if (now > this.bandPeakHold[i]) {
        this.bandPeaks[i] = Math.max(smoothed, this.bandPeaks[i] - 0.006);
      }

      // Row background card
      ctx.fillStyle = `rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.035)`;
      this._roundRect(ctx, 0, y, width, rowHeight, 6);
      ctx.fill();

      this._drawLeftColumn(ctx, band, y, rowHeight, colors, smoothed);

      // --- CENTER: filled waveform area, scrolling ---
      const hist = this.waveHistories[i];
      hist.push(smoothed);
      if (hist.length > this.historyLen) hist.shift();

      ctx.save();
      ctx.beginPath();
      ctx.rect(centerX, y + 2, centerW, rowHeight - 4);
      ctx.clip();

      const baseY = y + rowHeight - 4;
      const topY = y + 4;
      const step = centerW / (this.historyLen - 1);
      const startX = centerX + centerW - (hist.length - 1) * step;

      ctx.beginPath();
      ctx.moveTo(startX, baseY);
      for (let h = 0; h < hist.length; h++) {
        const x = startX + h * step;
        const yVal = baseY - hist[h] * (rowHeight - 10);
        ctx.lineTo(x, yVal);
      }
      ctx.lineTo(startX + (hist.length - 1) * step, baseY);
      ctx.closePath();

      const grad = ctx.createLinearGradient(0, topY, 0, baseY);
      const c = i < 2 ? colors.accent : i < 5 ? colors.accent3 : colors.accent2;
      grad.addColorStop(0, `rgba(${c.r},${c.g},${c.b},0.75)`);
      grad.addColorStop(1, `rgba(${c.r},${c.g},${c.b},0.05)`);
      ctx.fillStyle = grad;
      ctx.fill();

      ctx.strokeStyle = `rgba(${c.r},${c.g},${c.b},0.9)`;
      ctx.lineWidth = 1.4;
      ctx.beginPath();
      for (let h = 0; h < hist.length; h++) {
        const x = startX + h * step;
        const yVal = baseY - hist[h] * (rowHeight - 10);
        if (h === 0) ctx.moveTo(x, yVal); else ctx.lineTo(x, yVal);
      }
      ctx.stroke();
      ctx.restore();

      this._drawRightMeter(ctx, width, rightColW, y, rowHeight, smoothed, this.bandPeaks[i], colors, c);
    }
  }

  reset() {
    this.bandSmoothed.fill(0);
    this.bandPeaks.fill(0);
    this.waveHistories = [[], [], [], [], [], [], []];
  }
}

/* ---------------- MODE 7: ORCHESTRA MODE 2 (static, anchored in place) ---------------- */
class OrchestraModeV2 extends OrchestraBase {
  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    this.pointsPerRow = 36;
    this.rowCount = 0; // forces _ensureRows to allocate on first draw
    this._ensureRows(7);
  }

  // Row count is user-adjustable (7-40, see settings.bandRows), so the
  // per-row state arrays are reallocated (preserving whatever fits) whenever
  // it changes, rather than being fixed at 7 the way they used to be.
  _ensureRows(rowCount) {
    if (rowCount === this.rowCount) return;
    this.rowCount = rowCount;
    this.bandSmoothed = new Float32Array(rowCount);
    this.bandPeaks = new Float32Array(rowCount);
    this.bandPeakHold = new Float32Array(rowCount);
    this.rowSamples = Array.from({ length: rowCount }, () => new Float32Array(this.pointsPerRow));
    // Slower-decaying envelope per row — an overlaid "ceiling" line that
    // traces the recent local maxima above the live silhouette.
    this.rowEnvelope = Array.from({ length: rowCount }, () => new Float32Array(this.pointsPerRow));
    // Slow-rising "floor" that traces recent local minima below the live
    // silhouette — a third independent variable per point, alongside the
    // silhouette and the ceiling.
    this.rowFloor = Array.from({ length: rowCount }, () => new Float32Array(this.pointsPerRow));
  }

  draw(audio, now) {
    const ctx = this.ctx;
    const { width, height } = this;
    const colors = this.theme.getAccentColors();
    const rowCountSetting = Util.clamp(Math.round(this.settings.get('bandRows') || 7), 7, 40);
    const bands = rowCountSetting === 7 ? audio.bandDefs : audio.getDynamicBands(rowCountSetting);
    this._ensureRows(bands.length);
    const rowCount = bands.length;
    // More breathing room than Orchestra Mode 1 — bigger row gap, a wider
    // meter column with a chunkier bar, and more clip padding around the
    // waveform fill so nothing feels crammed edge-to-edge.
    const rowGap = 7;
    const rowHeight = (height - rowGap * (rowCount - 1)) / rowCount;

    ctx.clearRect(0, 0, width, height);

    const leftColW = Math.min(150, width * 0.22);
    const rightColW = Math.min(150, width * 0.21);
    const centerX = leftColW;
    const centerW = width - leftColW - rightColW;
    const nyquist = (audio.sampleRate || 44100) / 2;
    const meterBarHeight = 12;

    for (let i = 0; i < rowCount; i++) {
      const band = bands[i];
      const y = i * (rowHeight + rowGap);
      const energy = audio.getBandEnergy(band.lo, band.hi) / 255 * audio.sensitivity;

      const prev = this.bandSmoothed[i];
      const smoothed = prev + (energy - prev) * (energy > prev ? 0.45 : 0.12);
      this.bandSmoothed[i] = smoothed;

      if (smoothed >= this.bandPeaks[i]) {
        this.bandPeaks[i] = smoothed;
        this.bandPeakHold[i] = now + 900;
      } else if (now > this.bandPeakHold[i]) {
        this.bandPeaks[i] = Math.max(smoothed, this.bandPeaks[i] - 0.006);
      }

      // Row background card
      ctx.fillStyle = `rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.035)`;
      this._roundRect(ctx, 0, y, width, rowHeight, 8);
      ctx.fill();

      this._drawLeftColumn(ctx, band, y, rowHeight, colors, smoothed);

      // --- CENTER: filled waveform area, anchored in place ---
      // Sample N fixed points across an EXTENDED slice of the spectrum —
      // each row now reaches a bit into its neighboring bands (and the
      // final row reaches all the way to Nyquist) instead of being
      // strictly boxed into its nominal Hz range, so the silhouette
      // reflects more of the surrounding spectrum. Each point's
      // x-position is still permanent — only its height changes frame to
      // frame. No scrolling, no shifting buffer.
      const bandSpan = band.hi - band.lo;
      const extLo = i === 0 ? 0 : Math.max(0, band.lo - bandSpan * 0.25);
      const extHi = i === rowCount - 1 ? nyquist : band.hi + bandSpan * 0.25;
      const samples = this.rowSamples[i];
      const envelope = this.rowEnvelope[i];
      const floor = this.rowFloor[i];
      const n = this.pointsPerRow;
      const span = extHi - extLo;
      for (let p = 0; p < n; p++) {
        const loP = extLo + (p / n) * span;
        const hiP = extLo + ((p + 1) / n) * span;
        const raw = audio.getBandEnergy(loP, hiP) / 255 * audio.sensitivity;
        const sPrev = samples[p];
        samples[p] = sPrev + (raw - sPrev) * (raw > sPrev ? 0.5 : 0.15);

        // Slow-decaying ceiling line: snaps up instantly with the signal,
        // then eases back down, tracing recent local maxima above the
        // live silhouette — a second, independent variable per point.
        if (samples[p] >= envelope[p]) envelope[p] = samples[p];
        else envelope[p] = Math.max(samples[p], envelope[p] - 0.008);

        // Slow-rising floor line: snaps down instantly with the signal,
        // then eases back up, tracing recent local minima below the live
        // silhouette — a third, independent variable per point.
        if (samples[p] <= floor[p]) floor[p] = samples[p];
        else floor[p] = Math.min(samples[p], floor[p] + 0.006);
      }

      ctx.save();
      ctx.beginPath();
      ctx.rect(centerX, y + 3, centerW, rowHeight - 6);
      ctx.clip();

      const baseY = y + rowHeight - 5;
      const topY = y + 5;
      const step = centerW / (n - 1);

      const silPts = [];
      for (let p = 0; p < n; p++) {
        silPts.push({ x: centerX + p * step, y: baseY - samples[p] * (rowHeight - 12) });
      }
      ctx.beginPath();
      ctx.moveTo(centerX, baseY);
      ctx.lineTo(silPts[0].x, silPts[0].y);
      this.smoothPath(ctx, silPts);
      ctx.lineTo(centerX + (n - 1) * step, baseY);
      ctx.closePath();

      const grad = ctx.createLinearGradient(0, topY, 0, baseY);
      const c = i < 2 ? colors.accent : i < 5 ? colors.accent3 : colors.accent2;
      grad.addColorStop(0, `rgba(${c.r},${c.g},${c.b},0.75)`);
      grad.addColorStop(1, `rgba(${c.r},${c.g},${c.b},0.05)`);
      ctx.fillStyle = grad;
      ctx.fill();

      ctx.strokeStyle = `rgba(${c.r},${c.g},${c.b},0.9)`;
      ctx.lineWidth = 1.4;
      ctx.lineJoin = 'round';
      ctx.beginPath();
      ctx.moveTo(silPts[0].x, silPts[0].y);
      this.smoothPath(ctx, silPts);
      ctx.stroke();

      // Envelope/ceiling line — a second, lighter dashed trace riding
      // above the live silhouette.
      ctx.strokeStyle = `rgba(${colors.accent2.r},${colors.accent2.g},${colors.accent2.b},0.65)`;
      ctx.lineWidth = 1;
      ctx.setLineDash([3, 3]);
      const envPts = Array.from({ length: n }, (_, p) => ({ x: centerX + p * step, y: baseY - envelope[p] * (rowHeight - 12) }));
      ctx.beginPath();
      ctx.moveTo(envPts[0].x, envPts[0].y);
      this.smoothPath(ctx, envPts);
      ctx.stroke();

      // Floor line — a third, dotted trace riding below the live
      // silhouette, in a color distinct from both the silhouette and the
      // ceiling so all three read as separate variables at a glance.
      ctx.strokeStyle = `rgba(${colors.accent3.r},${colors.accent3.g},${colors.accent3.b},0.6)`;
      ctx.lineWidth = 1;
      ctx.setLineDash([1, 3]);
      const floorPts = Array.from({ length: n }, (_, p) => ({ x: centerX + p * step, y: baseY - floor[p] * (rowHeight - 12) }));
      ctx.beginPath();
      ctx.moveTo(floorPts[0].x, floorPts[0].y);
      this.smoothPath(ctx, floorPts);
      ctx.stroke();
      ctx.setLineDash([]);
      ctx.restore();

      this._drawRightMeter(ctx, width, rightColW, y, rowHeight, smoothed, this.bandPeaks[i], colors, c, meterBarHeight);
    }
  }

  reset() {
    this.bandSmoothed.fill(0);
    this.bandPeaks.fill(0);
    for (const arr of this.rowSamples) arr.fill(0);
    for (const arr of this.rowEnvelope) arr.fill(0);
    for (const arr of this.rowFloor) arr.fill(0);
  }
}

/* ---------------- MODE: METER BANK (big channel-strip style bar meters) ---------------- */
/* A cleaner, more spacious take on Orchestra's right-hand meter column —
   full-width bar meters with peak-hold ticks, one big roomy row per band,
   no waveform trace competing for space. Reuses OrchestraBase's icon/label
   and meter-drawing helpers so it looks and feels consistent with the
   other two Orchestra modes. */
class MeterBankViz extends OrchestraBase {
  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    this.bandSmoothed = new Float32Array(7);
    this.bandPeaks = new Float32Array(7);
    this.bandPeakHold = new Float32Array(7);
  }

  draw(audio, now) {
    const ctx = this.ctx;
    const { width, height } = this;
    const colors = this.theme.getAccentColors();
    const bands = audio.bandDefs;
    const rowCount = bands.length;
    const rowGap = 10;
    const rowHeight = (height - rowGap * (rowCount - 1)) / rowCount;

    ctx.clearRect(0, 0, width, height);

    const leftColW = Math.min(170, width * 0.26);
    // No center waveform column here — the meter gets everything that's
    // left, which is most of the row's width.
    const rightColW = width - leftColW;
    const meterBarHeight = Util.clamp(rowHeight * 0.34, 14, 34);

    for (let i = 0; i < rowCount; i++) {
      const band = bands[i];
      const y = i * (rowHeight + rowGap);
      const energy = audio.getBandEnergy(band.lo, band.hi) / 255 * audio.sensitivity;

      const prev = this.bandSmoothed[i];
      const smoothed = prev + (energy - prev) * (energy > prev ? 0.45 : 0.12);
      this.bandSmoothed[i] = smoothed;

      if (smoothed >= this.bandPeaks[i]) {
        this.bandPeaks[i] = smoothed;
        this.bandPeakHold[i] = now + 1100;
      } else if (now > this.bandPeakHold[i]) {
        this.bandPeaks[i] = Math.max(smoothed, this.bandPeaks[i] - 0.005);
      }

      const c = i < 2 ? colors.accent : i < 5 ? colors.accent3 : colors.accent2;

      // Row background card — a bit more glow than Orchestra's when the
      // band is loud, since there's nothing else in the row competing for
      // attention.
      ctx.fillStyle = `rgba(${c.r},${c.g},${c.b},${0.03 + smoothed * 0.05})`;
      this._roundRect(ctx, 0, y, width, rowHeight, 10);
      ctx.fill();
      ctx.strokeStyle = `rgba(${c.r},${c.g},${c.b},${0.08 + smoothed * 0.18})`;
      ctx.lineWidth = 1;
      this._roundRect(ctx, 0.5, y + 0.5, width - 1, rowHeight - 1, 10);
      ctx.stroke();

      this._drawLeftColumn(ctx, band, y, rowHeight, colors, smoothed);
      this._drawRightMeter(ctx, width, rightColW, y, rowHeight, smoothed, this.bandPeaks[i], colors, c, meterBarHeight);
    }
  }

  reset() {
    this.bandSmoothed.fill(0);
    this.bandPeaks.fill(0);
  }
}

class MeterBankV2 extends OrchestraBase {
  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    this.rowCount = 0; // forces _ensureRows to allocate on first draw
    this._ensureRows(9);
  }

  _ensureRows(rowCount) {
    if (rowCount === this.rowCount) return;
    this.rowCount = rowCount;
    this.bandSmoothed = new Float32Array(rowCount);
    this.bandPeaks = new Float32Array(rowCount);
    this.bandPeakHold = new Float32Array(rowCount);
  }

  draw(audio, now) {
    const ctx = this.ctx;
    const { width, height } = this;
    const colors = this.theme.getAccentColors();
    const bands = audio.getMeterBank2Bands();
    this._ensureRows(bands.length);
    const rowCount = bands.length;
    const rowGap = rowCount > 16 ? 3 : rowCount > 10 ? 5 : 8;
    const rowHeight = (height - rowGap * (rowCount - 1)) / rowCount;
    const showLabels = rowHeight >= 20; // too thin to carry a left column once rows pile up

    ctx.clearRect(0, 0, width, height);

    const leftColW = showLabels ? Math.min(170, width * 0.26) : 0;
    const rightColW = width - leftColW;

    for (let i = 0; i < rowCount; i++) {
      const band = bands[i];
      const y = i * (rowHeight + rowGap);
      const energy = audio.getBandEnergy(band.lo, band.hi) / 255 * audio.sensitivity;

      const prev = this.bandSmoothed[i];
      const smoothed = prev + (energy - prev) * (energy > prev ? 0.5 : 0.1);
      this.bandSmoothed[i] = smoothed;

      if (smoothed >= this.bandPeaks[i]) {
        this.bandPeaks[i] = smoothed;
        this.bandPeakHold[i] = now + 900;
      } else if (now > this.bandPeakHold[i]) {
        this.bandPeaks[i] = Math.max(smoothed, this.bandPeaks[i] - 0.006);
      }

      const t = rowCount > 1 ? i / (rowCount - 1) : 0;
      const c = t < 0.4 ? colors.accent : t < 0.75 ? colors.accent3 : colors.accent2;

      if (showLabels) {
        this._drawLeftColumn(ctx, band, y, rowHeight, colors, smoothed);
      } else {
        ctx.font = '400 9px "JetBrains Mono", monospace';
        ctx.textBaseline = 'middle';
        ctx.fillStyle = `rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.55)`;
        ctx.fillText(band.name, 4, y + rowHeight / 2);
      }
      this._drawSegmentedMeter(ctx, width, rightColW, y, rowHeight, smoothed, this.bandPeaks[i], colors, c);
    }
  }

  reset() {
    this.bandSmoothed.fill(0);
    this.bandPeaks.fill(0);
  }
}

/* ---------------- MODE: SIGNAL METER (Volume / Frequency + 3 essentials) ----------------
   A dedicated, always-5-row segmented meter bank for the handful of
   headline numbers that aren't really "frequency bands" — the same ones
   shown in the topbar readouts (Volume, Frequency, BPM) plus two more that
   round out the picture: Peak (how hot the loudest instant is, distinct
   from the smoothed Volume reading) and Dynamic Range (the gap between
   peak and average level — a compressed, loud-all-the-way-through track
   reads near 0, a track with real quiet/loud contrast reads higher). */
class SignalMeter extends OrchestraBase {
  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    this.rowCount = 5;
    this.bandSmoothed = new Float32Array(this.rowCount);
    this.bandPeaks = new Float32Array(this.rowCount);
    this.bandPeakHold = new Float32Array(this.rowCount);
  }

  draw(audio, now) {
    const ctx = this.ctx;
    const { width, height } = this;
    const colors = this.theme.getAccentColors();
    const rowCount = this.rowCount;
    const rowGap = 10;
    const rowHeight = (height - rowGap * (rowCount - 1)) / rowCount;
    const showLabels = rowHeight >= 20;

    ctx.clearRect(0, 0, width, height);

    const leftColW = showLabels ? Math.min(170, width * 0.26) : 0;
    const rightColW = width - leftColW;

    const m = audio.metrics;
    const freqHz = m.peakFreq;
    const freqNorm = Util.clamp(Math.log10(Math.max(freqHz, 20) / 20) / Math.log10(20000 / 20), 0, 1);
    // Crest factor (peak-to-average, in dB) as a 0-20dB range mapped to 0-1.
    const crestDb = (m.peak > 0.001 && m.average > 0.001) ? 20 * Math.log10(m.peak / m.average) : 0;
    const crestNorm = Util.clamp(crestDb / 20, 0, 1);
    const bpm = audio.bpm;
    const bpmNorm = Util.clamp(bpm / 200, 0, 1);

    const rows = [
      { name: 'Volume', icon: 'volume', energy: Util.clamp(m.volume / 100, 0, 1), label: `${Math.round(m.volume)}%` },
      { name: 'Frequency', icon: 'freq', energy: freqNorm, label: `${Util.formatHz(freqHz)}Hz` },
      { name: 'Peak', icon: 'peak', energy: Util.clamp(m.peak, 0, 1), label: `${Math.round(m.peak * 100)}%` },
      { name: 'Dynamic Range', icon: 'range', energy: crestNorm, label: `${crestDb.toFixed(1)}dB` },
      { name: 'BPM', icon: 'bpm', energy: bpmNorm, label: bpm > 0 ? `${Math.round(bpm)}` : '—' },
    ];

    for (let i = 0; i < rowCount; i++) {
      const row = rows[i];
      const y = i * (rowHeight + rowGap);

      const prev = this.bandSmoothed[i];
      const diff = row.energy - prev;
      const smoothed = prev + diff * (diff > 0 ? 0.5 : 0.08);
      this.bandSmoothed[i] = smoothed;

      if (smoothed >= this.bandPeaks[i]) {
        this.bandPeaks[i] = smoothed;
        this.bandPeakHold[i] = now + 900;
      } else if (now > this.bandPeakHold[i]) {
        this.bandPeaks[i] = Math.max(smoothed, this.bandPeaks[i] - 0.006);
      }

      const t = i / (rowCount - 1);
      const c = t < 0.4 ? colors.accent : t < 0.75 ? colors.accent3 : colors.accent2;

      if (showLabels) {
        this._drawLeftColumn(ctx, { name: row.name, icon: row.icon }, y, rowHeight, colors, smoothed, row.label);
      } else {
        ctx.font = '400 9px "JetBrains Mono", monospace';
        ctx.textBaseline = 'middle';
        ctx.fillStyle = `rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},0.55)`;
        ctx.fillText(row.name, 4, y + rowHeight / 2);
      }
      this._drawSegmentedMeter(ctx, width, rightColW, y, rowHeight, smoothed, this.bandPeaks[i], colors, c, row.label);
    }
  }

  reset() {
    this.bandSmoothed.fill(0);
    this.bandPeaks.fill(0);
  }
}


/* ---------------- MODE: AUTO (picks + tunes a mode from the music itself) ---------------- */
/* Delegates drawing to one of the other visualizer instances, choosing which
   one based on simple, cheap heuristics over the live band energies and beat
   detection — no ML, just the same metrics every other mode already reads.
   It also nudges the analyser's FFT size to suit what's playing: larger for
   bass-heavy/tonal material (better frequency resolution), smaller for
   treble-heavy/percussive material (faster time response). Switches are
   debounced so it settles instead of flickering between modes. */
/* ---------------- MODE: SPECTROGRAM (scrolling waterfall) ---------------- */
class SpectrogramViz extends Visualizer {
  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    this.rows = 160;
    this.buf = null; this.bctx = null; this.col = null;
    this.lut = new Uint8ClampedArray(256 * 3);
    this.lutKey = '';
    this.acc = 0;
  }

  _ensure() {
    const cols = Math.max(96, Math.floor(this.width / 2));
    if (!this.buf || this.buf.width !== cols) {
      this.buf = document.createElement('canvas');
      this.buf.width = cols;
      this.buf.height = this.rows;
      this.bctx = this.buf.getContext('2d');
      this.bctx.fillStyle = '#000';
      this.bctx.fillRect(0, 0, cols, this.rows);
      this.col = this.bctx.createImageData(1, this.rows);
    }
  }

  _buildLut(c) {
    const key = `${c.accent.r},${c.accent.g},${c.accent.b},${c.accent2.r},${c.accent2.g},${c.accent2.b},${c.accent3.r},${c.accent3.g},${c.accent3.b}`;
    if (key === this.lutKey) return;
    this.lutKey = key;
    const stops = [
      [0.00, [0, 0, 0]],
      [0.28, [c.accent3.r * 0.55, c.accent3.g * 0.55, c.accent3.b * 0.55]],
      [0.58, [c.accent.r, c.accent.g, c.accent.b]],
      [0.85, [c.accent2.r, c.accent2.g, c.accent2.b]],
      [1.00, [255, 255, 255]],
    ];
    for (let i = 0; i < 256; i++) {
      const t = i / 255;
      let k = 1;
      while (k < stops.length - 1 && t > stops[k][0]) k++;
      const [t0, a] = stops[k - 1], [t1, b] = stops[k];
      const u = Util.clamp((t - t0) / (t1 - t0), 0, 1);
      this.lut[i * 3] = Util.lerp(a[0], b[0], u);
      this.lut[i * 3 + 1] = Util.lerp(a[1], b[1], u);
      this.lut[i * 3 + 2] = Util.lerp(a[2], b[2], u);
    }
  }

  draw(audio, now, dt) {
    const ctx = this.ctx, { width, height } = this;
    this._ensure();
    this._buildLut(this.theme.getAccentColors());

    // One new column per ~16.7ms regardless of frame rate
    this.acc += dt / 16.7;
    const n = Math.min(4, Math.floor(this.acc));
    this.acc -= Math.floor(this.acc);

    if (n > 0) {
      const freq = audio.freqData, bins = freq.length, d = this.col.data;
      for (let r = 0; r < this.rows; r++) {
        const frac = 1 - r / (this.rows - 1);            // top row = highest frequency
        const bin = Math.min(bins - 1, Math.floor(Math.pow(frac, 2.0) * (bins - 1)));
        const raw = ((freq[bin] + freq[Math.min(bins - 1, bin + 1)]) / 510) * audio.sensitivity;
        const idx = Math.floor(Math.pow(Util.clamp(raw, 0, 1), 1.15) * 255) * 3;
        const o = r * 4;
        d[o] = this.lut[idx]; d[o + 1] = this.lut[idx + 1]; d[o + 2] = this.lut[idx + 2]; d[o + 3] = 255;
      }
      for (let i = 0; i < n; i++) {
        this.bctx.globalCompositeOperation = 'copy';
        this.bctx.drawImage(this.buf, -1, 0);
        this.bctx.globalCompositeOperation = 'source-over';
        this.bctx.putImageData(this.col, this.buf.width - 1, 0);
      }
    }

    ctx.fillStyle = '#000';
    ctx.fillRect(0, 0, width, height);
    ctx.imageSmoothingEnabled = true;
    ctx.drawImage(this.buf, 0, 0, this.buf.width, this.rows, 0, 0, width, height);

    // Frequency scale
    ctx.font = '10px ui-monospace, monospace';
    ctx.textBaseline = 'middle';
    ctx.fillStyle = 'rgba(255,255,255,0.55)';
    for (const hz of [100, 500, 1000, 5000, 10000]) {
      const bin = audio.freqToBin(hz);
      const y = (1 - Math.sqrt(bin / (audio.freqData.length - 1))) * height;
      if (y < 8 || y > height - 8) continue;
      ctx.fillRect(0, y, 6, 1);
      ctx.fillText(Util.formatHz(hz), 10, y);
    }
  }

  reset() { this.buf = null; this.lutKey = ''; }
}

/* ---------------- MODE: WARP TUNNEL (bass-driven starfield) ---------------- */
class WarpViz extends Visualizer {
  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    this.stars = [];
    this.speed = 0.4;
    this.punch = 0;
    this.prevBass = 0;
  }

  _spawn(initial) {
    return { x: Math.random() * 2 - 1, y: Math.random() * 2 - 1, z: initial ? Math.random() : 1, h: Math.random() };
  }

  draw(audio, now, dt) {
    const ctx = this.ctx, { width, height } = this;
    const m = audio.metrics, c = this.theme.getAccentColors();
    const count = Util.clamp(Math.round(this.settings.get('particleCount') * 0.7), 150, 1600);
    while (this.stars.length < count) this.stars.push(this._spawn(true));
    if (this.stars.length > count) this.stars.length = count;

    ctx.fillStyle = 'rgba(0,0,0,0.30)';
    ctx.fillRect(0, 0, width, height);

    if (m.bass - this.prevBass > 0.12 && m.bass > 0.25) this.punch = 1;
    this.prevBass = Util.lerp(this.prevBass, m.bass, 0.5);
    this.punch *= Math.exp(-dt / 260);
    const target = 0.25 + m.energy * 1.6 + this.punch * 2.2;
    this.speed = Util.lerp(this.speed, target, 1 - Math.exp(-dt / 120));

    const cx = width / 2, cy = height / 2, scale = Math.max(width, height) * 0.3;

    // Soft core glow that breathes with the bass
    const gr = 30 + m.bass * 110;
    const g = ctx.createRadialGradient(cx, cy, 0, cx, cy, gr * 2.4);
    g.addColorStop(0, `rgba(${c.accent.r},${c.accent.g},${c.accent.b},${0.10 + m.bass * 0.22})`);
    g.addColorStop(1, `rgba(${c.accent.r},${c.accent.g},${c.accent.b},0)`);
    ctx.fillStyle = g;
    ctx.fillRect(0, 0, width, height);

    ctx.lineCap = 'round';
    for (const s of this.stars) {
      const zPrev = s.z;
      s.z -= this.speed * dt * 0.0006;
      if (s.z <= 0.02) { Object.assign(s, this._spawn(false)); continue; }
      const zTail = Math.min(1.2, s.z + (zPrev - s.z) * 2.5);
      const sx = cx + (s.x / s.z) * scale, sy = cy + (s.y / s.z) * scale;
      const px = cx + (s.x / zTail) * scale, py = cy + (s.y / zTail) * scale;
      if (sx < -40 || sx > width + 40 || sy < -40 || sy > height + 40) { Object.assign(s, this._spawn(false)); continue; }

      const depth = 1 - s.z;
      const mix = s.h;
      const r = Util.lerp(c.accent.r, c.accent3.r, mix) + (c.accent2.r - c.accent.r) * this.punch * 0.5;
      const gg = Util.lerp(c.accent.g, c.accent3.g, mix) + (c.accent2.g - c.accent.g) * this.punch * 0.5;
      const b = Util.lerp(c.accent.b, c.accent3.b, mix) + (c.accent2.b - c.accent.b) * this.punch * 0.5;
      ctx.strokeStyle = `rgba(${r | 0},${gg | 0},${b | 0},${Math.min(1, depth * 1.3 + 0.1)})`;
      ctx.lineWidth = 0.5 + depth * 2.2 * (1 + m.bass);
      ctx.beginPath();
      ctx.moveTo(px, py);
      ctx.lineTo(sx, sy);
      ctx.stroke();
    }
  }

  reset() { this.stars = []; this.punch = 0; }
}

/* ---------------- MODE: BEAT RIPPLES (shockwave rings) ---------------- */
class RipplesViz extends Visualizer {
  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    this.rings = [];
    this.avgBass = 0;
    this.lastSpawn = 0;
    this.orb = 0;
    this.rot = 0;
  }

  draw(audio, now, dt) {
    const ctx = this.ctx, { width, height } = this;
    const m = audio.metrics, c = this.theme.getAccentColors();
    const cx = width / 2, cy = height / 2;
    const minDim = Math.min(width, height), maxR = Math.hypot(width, height) / 2;

    ctx.fillStyle = 'rgba(0,0,0,0.24)';
    ctx.fillRect(0, 0, width, height);

    // Spawn a shockwave on each bass onset (plus a quiet ambient one now and then)
    this.avgBass = Util.lerp(this.avgBass, m.bass, 0.06);
    const onset = m.bass > this.avgBass * 1.35 && m.bass > 0.22 && now - this.lastSpawn > 150;
    const ambient = !m.isSilent && now - this.lastSpawn > 1600;
    if (onset || ambient) {
      this.lastSpawn = now;
      const k = onset ? m.bass : 0.15;
      this.rings.push({ r: minDim * 0.08, speed: 0.55 + k * 1.1, w: 1.5 + k * 6, tone: this.rings.length % 3 });
      if (this.rings.length > 24) this.rings.shift();
    }

    // Rings
    for (let i = this.rings.length - 1; i >= 0; i--) {
      const ring = this.rings[i];
      ring.r += ring.speed * dt * maxR * 0.0016;
      const life = 1 - ring.r / maxR;
      if (life <= 0) { this.rings.splice(i, 1); continue; }
      const col = ring.tone === 0 ? c.accent : ring.tone === 1 ? c.accent2 : c.accent3;
      ctx.strokeStyle = `rgba(${col.r},${col.g},${col.b},${Math.pow(life, 1.3).toFixed(3)})`;
      ctx.lineWidth = Math.max(0.5, ring.w * life);
      this.applyGlow(`rgba(${col.r},${col.g},${col.b},0.8)`, 0.7);
      ctx.beginPath();
      ctx.arc(cx, cy, ring.r, 0, Math.PI * 2);
      ctx.stroke();
    }
    this.clearGlow();

    // Spectrum-shaped ring around the core (mirrored so it's symmetric)
    this.rot += dt * 0.00018;
    const freq = audio.freqData, bins = freq.length, N = 120, base = minDim * 0.16;
    ctx.strokeStyle = `rgba(${c.accent2.r},${c.accent2.g},${c.accent2.b},0.9)`;
    ctx.lineWidth = 2;
    this.applyGlow(`rgba(${c.accent2.r},${c.accent2.g},${c.accent2.b},0.7)`, 0.6);
    ctx.beginPath();
    for (let i = 0; i <= N; i++) {
      const k = i <= N / 2 ? i / (N / 2) : (N - i) / (N / 2);
      const bin = Math.min(bins - 1, Math.floor(Math.pow(k, 1.7) * bins * 0.6));
      const v = Util.clamp(freq[bin] / 255 * audio.sensitivity, 0, 1);
      const ang = (i / N) * Math.PI * 2 + this.rot;
      const rad = base + v * minDim * 0.14;
      const x = cx + Math.cos(ang) * rad, y = cy + Math.sin(ang) * rad;
      if (i === 0) ctx.moveTo(x, y); else ctx.lineTo(x, y);
    }
    ctx.closePath();
    ctx.stroke();
    this.clearGlow();

    // Core orb
    this.orb = Util.lerp(this.orb, m.bass, 1 - Math.exp(-dt / 70));
    const orbR = minDim * 0.06 * (1 + this.orb * 1.1);
    const g = ctx.createRadialGradient(cx, cy, 0, cx, cy, orbR * 2);
    g.addColorStop(0, `rgba(255,255,255,${0.55 + this.orb * 0.4})`);
    g.addColorStop(0.35, `rgba(${c.accent.r},${c.accent.g},${c.accent.b},0.85)`);
    g.addColorStop(1, `rgba(${c.accent.r},${c.accent.g},${c.accent.b},0)`);
    ctx.fillStyle = g;
    ctx.beginPath();
    ctx.arc(cx, cy, orbR * 2, 0, Math.PI * 2);
    ctx.fill();
  }

  reset() { this.rings = []; }
}

/* ---------------- MODE: XY SCOPE (Lissajous / phase scope) ---------------- */
class ScopeViz extends Visualizer {
  draw(audio, now, dt) {
    const ctx = this.ctx, { width, height } = this;
    const c = this.theme.getAccentColors();
    const t = audio.timeData, n = t.length;
    const cx = width / 2, cy = height / 2, R = Math.min(width, height) * 0.44;

    ctx.fillStyle = 'rgba(0,0,0,0.16)';
    ctx.fillRect(0, 0, width, height);

    // Graticule
    ctx.strokeStyle = `rgba(${c.accent.r},${c.accent.g},${c.accent.b},0.10)`;
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.moveTo(cx - R, cy); ctx.lineTo(cx + R, cy);
    ctx.moveTo(cx, cy - R); ctx.lineTo(cx, cy + R);
    ctx.stroke();
    for (const f of [0.5, 1]) { ctx.beginPath(); ctx.arc(cx, cy, R * f, 0, Math.PI * 2); ctx.stroke(); }

    // Plot the signal against a copy of itself delayed by a fraction of the
    // window, rotated 45deg (mid/side style) so mono material forms shapes.
    const d = Math.max(1, Math.floor(n / 12));
    const sens = audio.sensitivity, K = 0.7071;
    ctx.globalCompositeOperation = 'lighter';
    ctx.lineJoin = 'round';
    for (const pass of [0, 1]) {
      const col = pass === 0 ? c.accent : c.accent3;
      ctx.strokeStyle = `rgba(${col.r},${col.g},${col.b},${pass === 0 ? 0.9 : 0.45})`;
      ctx.lineWidth = pass === 0 ? this.settings.get('lineWidth') * 0.7 : 1;
      this.applyGlow(`rgba(${col.r},${col.g},${col.b},0.8)`, pass === 0 ? 0.8 : 0.4);
      ctx.beginPath();
      const off = pass === 0 ? 0 : Math.floor(d / 2);
      for (let i = 0; i < n - d - off; i += 2) {
        const a = ((t[i] - 128) / 128) * sens;
        const b = ((t[i + d + off] - 128) / 128) * sens;
        const x = Util.clamp((a - b) * K, -1.2, 1.2), y = Util.clamp((a + b) * K, -1.2, 1.2);
        if (i === 0) ctx.moveTo(cx + x * R, cy - y * R); else ctx.lineTo(cx + x * R, cy - y * R);
      }
      ctx.stroke();
    }
    ctx.globalCompositeOperation = 'source-over';
    this.clearGlow();
  }
}

class AutoViz extends Visualizer {
  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    this.siblings = null;
    this.labels = null;
    this.onModeSelected = null;

    this.activeKey = 'spectrum';
    this.candidateKey = 'spectrum';
    this.candidateSince = 0;
    this.lastSwitchAt = 0;
    this.minHoldMs = 4000;      // don't leave a mode sooner than this
    this.confirmMs = 1400;      // candidate must stay stable this long before it wins
    this._announced = false;

    this.lastFftAdjust = 0;
    this.fftCooldownMs = 5000;

    // When set, Auto stays on this visualization and only the input tuning
    // (sens / gain / smooth) is automatic — no mode switching.
    this.lockedKey = null;
  }

  /** Wired up by AnimationEngine once every mode exists. */
  attach(siblings, labels, onModeSelected) {
    this.siblings = siblings;
    this.labels = labels;
    this.onModeSelected = onModeSelected;
  }

  _classify(audio, now) {
    const m = audio.metrics;
    if (m.isSilent) return 'waveform2';

    const { bass, mid, treble, energy } = m;
    const bpm = audio.bpm;

    // Strong rhythmic bass with a locked-in beat — alternate between two
    // punchy, bass-reactive modes every ~12s so it doesn't feel static.
    if (bass > 0.5 && bass > treble * 1.25 && bpm > 60) {
      return Math.floor(now / 12000) % 2 === 0 ? 'circular' : 'orchestra1';
    }
    // Dense, percussive, treble-forward material — particles read the
    // transients best.
    if (energy > 0.5 && treble > 0.4) return 'particles';
    // Airy / treble-led material without much low end — the multi-band
    // line graph shows that detail well.
    if (treble > mid && treble > bass && treble > 0.28) return 'linegraph2';
    // Quiet, sparse, mostly-tonal passages — the settled waveform trace.
    if (energy < 0.2) return 'waveform1';
    // Fairly even mix across bands at moderate energy — the classic bars.
    if (Math.abs(bass - mid) < 0.15 && Math.abs(mid - treble) < 0.15) return 'spectrum';
    // Everything else — the full 7-band breakdown.
    return 'orchestra2';
  }

  _autoTuneFft(audio, now) {
    if (!audio.isCapturing || now - this.lastFftAdjust < this.fftCooldownMs) return;
    const { bass, treble } = audio.metrics;
    let target = audio.fftSize;
    if (bass > treble + 0.15) target = 4096;        // more low-end frequency resolution
    else if (treble > bass + 0.15) target = 1024;    // faster response to transients
    else target = 2048;                               // balanced default
    if (target !== audio.fftSize) {
      audio.setFftSize(target);
      this.lastFftAdjust = now;
    }
  }

  draw(audio, now, dt) {
    if (!this.siblings) return;

    if (this.lockedKey) {
      if (!this._announced) {
        this._announced = true;
        this.activeKey = this.lockedKey;
        if (this.onModeSelected) this.onModeSelected(this.activeKey);
      }
      (this.siblings[this.lockedKey] || this.siblings.spectrum).draw(audio, now, dt);
      return;
    }

    this._autoTuneFft(audio, now);

    const desired = this._classify(audio, now);
    if (desired !== this.candidateKey) {
      this.candidateKey = desired;
      this.candidateSince = now;
    }

    const stableLongEnough = (now - this.candidateSince) > this.confirmMs;
    const heldLongEnough = (now - this.lastSwitchAt) > this.minHoldMs;
    if (!this._announced || (this.candidateKey !== this.activeKey && stableLongEnough && heldLongEnough)) {
      this.activeKey = this.candidateKey;
      this.lastSwitchAt = now;
      this._announced = true;
      if (this.onModeSelected) this.onModeSelected(this.activeKey);
    }

    const target = this.siblings[this.activeKey] || this.siblings.spectrum;
    target.draw(audio, now, dt);
  }

  reset() {
    this.activeKey = 'spectrum';
    this.candidateKey = 'spectrum';
    this.candidateSince = 0;
    this.lastSwitchAt = 0;
    this._announced = false;
  }
}

/* ============================================================
   SECTION 6 — ANIMATION ENGINE
   Owns the canvas, the rAF loop, FPS measurement, mode switching,
   high-DPI handling, resize observation, and pause-when-hidden.
   ============================================================ */
class AnimationEngine {
  constructor(canvas, settings, theme, audio) {
    this.canvas = canvas;
    this.ctx = canvas.getContext('2d', { alpha: false, desynchronized: true });
    this.settings = settings;
    this.theme = theme;
    this.audio = audio;

    this.modes = {
      spectrum: new SpectrumBars(this.ctx, settings, theme),
      waveform1: new WaveformViz1(this.ctx, settings, theme),
      waveform2: new WaveformViz2(this.ctx, settings, theme),
      circular: new CircularVisualizer(this.ctx, settings, theme),
      linegraph1: new LineGraphV1(this.ctx, settings, theme),
      linegraph2: new LineGraphV2(this.ctx, settings, theme),
      particles: new ParticleViz(this.ctx, settings, theme),
      orchestra1: new OrchestraModeV1(this.ctx, settings, theme),
      orchestra2: new OrchestraModeV2(this.ctx, settings, theme),
      meterbank: new MeterBankViz(this.ctx, settings, theme),
      meterbank2: new MeterBankV2(this.ctx, settings, theme),
      signalmeter: new SignalMeter(this.ctx, settings, theme),
      spectrum2: new SpectrumBarsBlocks(this.ctx, settings, theme),
      waterfall: new SpectrogramViz(this.ctx, settings, theme),
      warp: new WarpViz(this.ctx, settings, theme),
      ripples: new RipplesViz(this.ctx, settings, theme),
      scope: new ScopeViz(this.ctx, settings, theme),
    };
    // Auto mode delegates to the modes above, so it's wired up after they
    // exist. It's deliberately excluded from modeOrder (the numbered 1-9
    // list) and addressed separately — see UIController, which gives it
    // the "0" slot both on the toolbar and on the keyboard. Meter Bank
    // ("M") and its variants get their own letter slots the same way.
    this.modes.auto = new AutoViz(this.ctx, settings, theme);
    this.modes.auto.attach(this.modes, null, (key) => {
      if (this.onAutoModeChange) this.onAutoModeChange(key);
    });

    this.modeOrder = ['spectrum', 'waveform1', 'waveform2', 'circular', 'linegraph1', 'linegraph2', 'particles', 'orchestra1', 'orchestra2', 'meterbank', 'meterbank2', 'signalmeter', 'waterfall', 'warp', 'ripples', 'scope', 'spectrum2', 'auto'];
    this.currentModeKey = 'spectrum';

    this.running = false;
    this.rafId = null;
    this.lastFrameTime = 0;
    this.fps = 0;
    this._fpsFrames = 0;
    this._fpsAccum = 0;

    this.beatFlashIntensity = 0;

    this._onVisibilityChange = this._onVisibilityChange.bind(this);
    document.addEventListener('visibilitychange', this._onVisibilityChange);

    this._resizeObserver = new ResizeObserver(() => this._handleResize());
  }

  observe(container) {
    this._resizeObserver.observe(container);
    this._handleResize();
  }

  _handleResize() {
    const rect = this.canvas.getBoundingClientRect();
    const dpr = Math.min(window.devicePixelRatio || 1, 2.5);
    const w = Math.max(1, Math.round(rect.width * dpr));
    const h = Math.max(1, Math.round(rect.height * dpr));
    if (this.canvas.width !== w || this.canvas.height !== h) {
      this.canvas.width = w;
      this.canvas.height = h;
      this.ctx.setTransform(1, 0, 0, 1, 0, 0); // reset, we draw in device pixels
      for (const key in this.modes) {
        this.modes[key].resize(w, h, dpr);
      }
    }
  }

  setMode(key) {
    if (!this.modes[key]) return;
    this.currentModeKey = key;
  }

  get currentMode() { return this.modes[this.currentModeKey]; }

  start() {
    if (this.running) return;
    this.running = true;
    this.lastFrameTime = performance.now();
    this._loop(this.lastFrameTime);
  }

  stop() {
    this.running = false;
    if (this.rafId) cancelAnimationFrame(this.rafId);
    this.rafId = null;
    // Clear canvas
    this.ctx.fillStyle = '#000';
    this.ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
  }

  resetAllModes() {
    for (const key in this.modes) this.modes[key].reset();
  }

  triggerBeatFlash() {
    this.beatFlashIntensity = 1;
  }

  _onVisibilityChange() {
    // Don't freeze the render loop while a PiP window is actively showing
    // this canvas — that's the whole point of PiP (keep watching while the
    // tab itself is backgrounded). Only pause when truly hidden with no
    // floating window open.
    if (document.hidden && !document.pictureInPictureElement) {
      if (this.rafId) cancelAnimationFrame(this.rafId);
      this.rafId = null;
    } else if (this.running && !this.rafId) {
      this.lastFrameTime = performance.now();
      this._loop(this.lastFrameTime);
    }
  }

  _loop(now) {
    if (!this.running) return;
    this.rafId = requestAnimationFrame((t) => this._loop(t));

    const dt = now - this.lastFrameTime;

    // Optional FPS cap: keep the rAF chain alive (so timing stays smooth
    // once we do draw) but skip the actual work until enough time has
    // passed toward the target frame interval. 0 = unlimited.
    const targetFps = this.settings.get('targetFps') || 0;
    if (targetFps > 0 && dt < (1000 / targetFps) - 0.5) return;

    this.lastFrameTime = now;

    // FPS measurement (rolling, updated ~4x/sec)
    this._fpsFrames++;
    this._fpsAccum += dt;
    if (this._fpsAccum >= 250) {
      this.fps = Math.round((this._fpsFrames * 1000) / this._fpsAccum);
      this._fpsFrames = 0;
      this._fpsAccum = 0;
    }

    if (!this.audio.isPaused) {
      this.audio.update();
    }

    this.currentMode.draw(this.audio, now, dt);

    if (this.onFrame) this.onFrame(dt);
  }
}

/* ============================================================
   SECTION 7 — UI CONTROLLER
   Wires DOM elements to AudioEngine / AnimationEngine / ThemeManager
   / SettingsManager. Handles start/stop/pause, recording, screenshots,
   keyboard shortcuts, and live readout updates.
   ============================================================ */

/* Per-visualization "looks best" combinations of sensitivity / gain /
   smoothing. Auto mode doesn't just switch which visualization is drawn —
   each one reads best with different input tuning (e.g. particles want a
   punchy, low-smoothing response to transients; bars sit in between). Auto mode dials these in
   itself whenever it settles on a sub-mode, instead of leaving whatever
   the sliders happened to be at. */
const AUTO_TUNE_PRESETS = {
  spectrum: { sensitivity: 1.10, gain: 1.15, smoothing: 0.72 },
  waveform1: { sensitivity: 0.90, gain: 1.00, smoothing: 0.35 },
  waveform2: { sensitivity: 0.95, gain: 1.05, smoothing: 0.40 },
  circular: { sensitivity: 1.20, gain: 1.20, smoothing: 0.68 },
  linegraph1: { sensitivity: 1.00, gain: 1.00, smoothing: 0.60 },
  linegraph2: { sensitivity: 1.05, gain: 1.00, smoothing: 0.55 },
  particles: { sensitivity: 1.40, gain: 1.30, smoothing: 0.30 },
  orchestra1: { sensitivity: 1.15, gain: 1.10, smoothing: 0.70 },
  orchestra2: { sensitivity: 1.10, gain: 1.05, smoothing: 0.75 },
  meterbank: { sensitivity: 1.00, gain: 1.00, smoothing: 0.65 },
  meterbank2: { sensitivity: 1.05, gain: 1.00, smoothing: 0.55 },
  signalmeter: { sensitivity: 1.00, gain: 1.00, smoothing: 0.60 },
  spectrum2: { sensitivity: 1.10, gain: 1.15, smoothing: 0.65 },
  waterfall: { sensitivity: 1.15, gain: 1.10, smoothing: 0.60 },
  warp: { sensitivity: 1.20, gain: 1.15, smoothing: 0.50 },
  ripples: { sensitivity: 1.25, gain: 1.15, smoothing: 0.60 },
  scope: { sensitivity: 1.00, gain: 1.00, smoothing: 0.30 },
};

/* How full the tallest peak should sit (0-1) for each visualization. Bars
   and radial modes look best just under the ceiling; traces and slow graphs
   want more headroom. */
const AUTO_PEAK_TARGET = {
  spectrum: 0.90, circular: 0.85, particles: 0.80, orchestra1: 0.85,
  orchestra2: 0.85, linegraph1: 0.80, linegraph2: 0.80, meterbank: 0.90, meterbank2: 0.92, signalmeter: 0.90, spectrum2: 0.90,
  waveform1: 0.70, waveform2: 0.70,
  waterfall: 0.85, warp: 0.80, ripples: 0.85, scope: 0.70,
};

/* Modes demanding enough on the GPU/CPU to warn about: each does
   meaningfully more per-frame work than the simpler bar/line modes (large
   full-canvas pixel copies, hundreds of individually alpha-blended shapes,
   or several overlapping blur/glow layers). */
const HEAVY_MODES = {
  particles: 'Draws hundreds of individually alpha-blended particles every frame.',
  warp: 'Renders a large moving starfield with glow and a recomputed radial gradient every frame.',
  waterfall: 'Copies and redraws a full-resolution scrolling image buffer every frame.',
  ripples: 'Layers several overlapping blurred glow rings and gradients every frame.',
  scope: 'Uses additive blending and glow across two full traces every frame.',
};

class UIController {
  constructor() {
    this.audio = new AudioEngine();
    this.theme = new ThemeManager();
    this.settings = new SettingsManager();

    this.canvas = document.getElementById('vizCanvas');
    this.stage = document.getElementById('stage');
    this.app = document.getElementById('app');

    this.engine = new AnimationEngine(this.canvas, this.settings, this.theme, this.audio);
    this.engine.observe(this.stage);

    this.mediaRecorder = null;
    this.recordedChunks = [];
    this.isRecording = false;
    this._autoTune = null;
    this._perfWarnKey = null;
    this._autoKey = null;
    this._autoEnergy = 0;
    this._autoState = null;
    this._lastManualMode = 'spectrum';

    this.modeLabels = {
      spectrum: 'Spectrum Bars',
      waveform1: 'Waveform Mode 1',
      waveform2: 'Waveform Mode 2',
      circular: 'Circular Spectrum',
      linegraph1: 'Line Graph Mode 1',
      linegraph2: 'Line Graph Mode 2',
      particles: 'Particle Visualizer',
      orchestra1: 'Orchestra Mode 1',
      orchestra2: 'Orchestra Mode 2',
      meterbank: 'Meter Bank',
      meterbank2: 'Meter Bank 2',
      signalmeter: 'Signal Meter',
      spectrum2: 'Spectrum Blocks',
      waterfall: 'Spectrogram',
      warp: 'Warp Tunnel',
      ripples: 'Beat Ripples',
      scope: 'XY Scope',
      auto: 'Auto Mode',
    };

    this._cacheDom();
    this._buildVizSelector();
    this._bindPerfWarning();
    this._bindThemeSelect();
    this._bindToolbar();
    this._bindSettingsPanel();
    this._bindKeyboard();
    this._bindStart();

    this.audio.beatFlashCallback = () => this.engine.triggerBeatFlash();
    this.audio.onExternalStop = () => this._handleStop();

    this.engine.onFrame = (dt) => this._onFrame(dt);

    // Auto mode picks a sub-mode on its own; when it's the active top-level
    // mode, reflect what it just chose in the mode chip instead of the
    // static "Auto Mode" label.
    this.engine.onAutoModeChange = (key) => {
      if (this.engine.currentModeKey !== 'auto') return;
      this.el.modeChip.textContent = `AUTO → ${this.modeLabels[key]}`;
      this.el.modeChip.classList.add('auto-live');
      this._startAutoTune(key);
    };

    this._renderLoopId = requestAnimationFrame(() => this._idleRenderTick());
  }

  _cacheDom() {
    this.el = {
      startOverlay: document.getElementById('startOverlay'),
      btnStart: document.getElementById('btnStart'),
      startError: document.getElementById('startError'),
      btnPlayPause: document.getElementById('btnPlayPause'),
      iconPlayPause: document.getElementById('iconPlayPause'),
      btnStop: document.getElementById('btnStop'),
      vizSelect: document.getElementById('vizSelect'),
      modeChip: document.getElementById('modeChip'),
      beatFlash: document.getElementById('beatFlash'),
      sliderSensitivity: document.getElementById('sliderSensitivity'),
      sliderGain: document.getElementById('sliderGain'),
      sliderSmoothing: document.getElementById('sliderSmoothing'),
      numSensitivity: document.getElementById('numSensitivity'),
      numGain: document.getElementById('numGain'),
      numSmoothing: document.getElementById('numSmoothing'),
      themeSelect: document.getElementById('themeSelect'),
      btnThemeMode: document.getElementById('btnThemeMode'),
      btnFullscreen: document.getElementById('btnFullscreen'),
      btnPip: document.getElementById('btnPip'),
      btnScreenshot: document.getElementById('btnScreenshot'),
      btnRecord: document.getElementById('btnRecord'),
      btnSettings: document.getElementById('btnSettings'),
      btnCloseSettings: document.getElementById('btnCloseSettings'),
      settingsPanel: document.getElementById('settingsPanel'),
      settingsScrim: document.getElementById('settingsScrim'),
      toolbar: document.getElementById('toolbar'),

      rVolume: document.getElementById('rVolume'),
      rPeakFreq: document.getElementById('rPeakFreq'),
      rFps: document.getElementById('rFps'),
      rLatency: document.getElementById('rLatency'),
      rSampleRate: document.getElementById('rSampleRate'),
      rBpm: document.getElementById('rBpm'),

      selFftSize: document.getElementById('selFftSize'),
      vFftSize: document.getElementById('vFftSize'),
      selTargetFps: document.getElementById('selTargetFps'),
      selLatencyHint: document.getElementById('selLatencyHint'),
      vLatencyHint: document.getElementById('vLatencyHint'),
      rngBarCount: document.getElementById('rngBarCount'),
      rngBandRows: document.getElementById('rngBandRows'),
      vBandRows: document.getElementById('vBandRows'),
      perfWarnScrim: document.getElementById('perfWarnScrim'),
      perfWarnDialog: document.getElementById('perfWarnDialog'),
      perfWarnTitle: document.getElementById('perfWarnTitle'),
      perfWarnBody: document.getElementById('perfWarnBody'),
      chkPerfWarnDontShow: document.getElementById('chkPerfWarnDontShow'),
      btnPerfWarnDismiss: document.getElementById('btnPerfWarnDismiss'),
      vBarCount: document.getElementById('vBarCount'),
      rngPeakHold: document.getElementById('rngPeakHold'),
      vPeakHold: document.getElementById('vPeakHold'),
      chkMirror: document.getElementById('chkMirror'),
      chkMoreLines: document.getElementById('chkMoreLines'),
      rngLineWidth: document.getElementById('rngLineWidth'),
      vLineWidth: document.getElementById('vLineWidth'),
      rngRadius: document.getElementById('rngRadius'),
      vRadius: document.getElementById('vRadius'),
      rngRotSpeed: document.getElementById('rngRotSpeed'),
      vRotSpeed: document.getElementById('vRotSpeed'),
      rngParticleCount: document.getElementById('rngParticleCount'),
      vParticleCount: document.getElementById('vParticleCount'),
      rngGlow: document.getElementById('rngGlow'),
      vGlow: document.getElementById('vGlow'),
      rngBgBlur: document.getElementById('rngBgBlur'),
      vBgBlur: document.getElementById('vBgBlur'),
      rngWaveThick: document.getElementById('rngWaveThick'),
      vWaveThick: document.getElementById('vWaveThick'),
    };
  }

  /* ---------------- VIZ MODE SELECTOR ---------------- */
  _buildVizSelector() {
    const order = this.engine.modeOrder;
    // Regular modes are numbered 1-9 in order; Auto and the Meter Bank /
    // Spectrum / Scope variants are addressed by letter/digit instead
    // (0, M, L, E, W, T, B, X — matching their keyboard shortcuts) rather
    // than continuing the numbering.
    const lettered = {
      auto: { label: '0', cls: 'auto-btn', title: 'Keeps your current mode and auto-tunes sens / gain / smooth (0)' },
      meterbank: { label: 'M', cls: 'meterbank-btn' },
      meterbank2: { label: 'L', cls: 'meterbank-btn' },
      signalmeter: { label: 'V', cls: 'meterbank-btn' },
      spectrum2: { label: 'E', cls: 'extra-btn' },
      waterfall: { label: 'W', cls: 'extra-btn' },
      warp: { label: 'T', cls: 'extra-btn' },
      ripples: { label: 'B', cls: 'extra-btn' },
      scope: { label: 'X', cls: 'extra-btn' },
    };
    let regularIdx = 0;
    order.forEach((key) => {
      const btn = document.createElement('button');
      const special = lettered[key];
      btn.className = 'viz-btn'
        + (special ? ` ${special.cls}` : '')
        + (key === this.engine.currentModeKey ? ' active' : '');
      btn.dataset.mode = key;
      const numLabel = special ? special.label : String(++regularIdx);
      btn.title = special?.title || `${this.modeLabels[key]} (${numLabel})`;
      btn.innerHTML = `<span class="num">${numLabel}</span><span>${this.modeLabels[key]}</span>`;
      btn.addEventListener('click', () => this._setMode(key));
      this.el.vizSelect.appendChild(btn);
    });
  }

  _setMode(key) {
    if (key !== 'auto') {
      this._autoTune = null;
      this._autoKey = null;
      this._lastManualMode = key;
      this._maybeShowPerfWarning(key);
    } else {
      // Auto keeps the visualization you were on and only tunes its input.
      const auto = this.engine.modes.auto;
      auto.reset();
      auto.lockedKey = this._lastManualMode;
      this._autoKey = this._lastManualMode;
      this._autoEnergy = 0;
      this._autoState = null;
      this._maybeShowPerfWarning(this._lastManualMode);
    }
    this.engine.setMode(key);
    this.el.modeChip.classList.remove('auto-live');
    this.el.modeChip.textContent = this.modeLabels[key];
    [...this.el.vizSelect.children].forEach(b => {
      b.classList.toggle('active', b.dataset.mode === key);
    });
  }

  /* ---------------- PERFORMANCE WARNING ----------------
     A small, theme-matched dialog that warns once per mode (persisted via
     localStorage, best-effort) the first time the person switches into
     something meaningfully heavier on the GPU/CPU than the simpler modes.
     "Dismiss" with the checkbox checked (the default) remembers the choice
     so it never nags again for that mode; unchecking it just closes the
     dialog this one time. */
  _bindPerfWarning() {
    const close = () => {
      this.el.perfWarnDialog.classList.remove('open');
      this.el.perfWarnScrim.classList.remove('open');
    };
    const dismiss = () => {
      if (this._perfWarnKey && this.el.chkPerfWarnDontShow.checked) {
        try { localStorage.setItem(`resonix:perfWarnDismissed:${this._perfWarnKey}`, '1'); }
        catch (e) { /* storage unavailable — just won't persist across reloads */ }
      }
      close();
    };
    this.el.btnPerfWarnDismiss.addEventListener('click', dismiss);
    this.el.perfWarnScrim.addEventListener('click', dismiss);
  }

  _maybeShowPerfWarning(key) {
    const reason = HEAVY_MODES[key];
    if (!reason) return;
    let dismissed = false;
    try { dismissed = localStorage.getItem(`resonix:perfWarnDismissed:${key}`) === '1'; }
    catch (e) { /* storage unavailable — fall through and warn anyway */ }
    if (dismissed) return;

    this._perfWarnKey = key;
    this.el.perfWarnTitle.textContent = `${this.modeLabels[key]} is heavier on your GPU/CPU`;
    this.el.perfWarnBody.textContent = reason;
    this.el.chkPerfWarnDontShow.checked = true;
    this.el.perfWarnDialog.classList.add('open');
    this.el.perfWarnScrim.classList.add('open');
  }

  /* ---------------- AUTO MODE INPUT TUNING ----------------
     When Auto settles on a sub-mode, ease sensitivity / gain / smoothing
     toward that mode's preset (AUTO_TUNE_PRESETS) instead of snapping, and
     keep the toolbar sliders in sync so what you see matches what's applied. */
  _startAutoTune(key) {
    const to = AUTO_TUNE_PRESETS[key];
    if (!to) return;
    this._autoTune = {
      from: {
        sensitivity: this.audio.sensitivity,
        gain: this.audio.gain,
        smoothing: this.audio.smoothing,
      },
      to,
      elapsed: 0,
      duration: 1200,
    };
  }

  _updateAutoTune(dt) {
    if (this.engine.currentModeKey !== 'auto') { this._autoTune = null; return; }
    const tune = this._autoTune;
    if (!tune) { this._adaptTuning(dt); return; }

    tune.elapsed += dt;
    const t = Util.easeInOutSine(Util.clamp(tune.elapsed / tune.duration, 0, 1));
    const sensitivity = Util.lerp(tune.from.sensitivity, tune.to.sensitivity, t);
    const gain = Util.lerp(tune.from.gain, tune.to.gain, t);
    const smoothing = Util.lerp(tune.from.smoothing, tune.to.smoothing, t);

    this.audio.setSensitivity(sensitivity);
    this.audio.setGain(gain);
    this.audio.setSmoothing(smoothing);

    this.el.sliderSensitivity.value = sensitivity;
    this.el.numSensitivity.value = sensitivity.toFixed(2);
    this.el.sliderGain.value = gain;
    this.el.numGain.value = gain.toFixed(2);
    this.el.sliderSmoothing.value = smoothing;
    this.el.numSmoothing.value = smoothing.toFixed(2);

    if (t >= 1) this._autoTune = null;
  }

  /* Closed-loop tuning once the preset has settled. Three separate jobs so
     the loops don't fight each other:
       gain        (slow)   keeps the raw signal RMS at a healthy level
       sensitivity (medium) keeps the tallest peak near this mode's target,
                            backing off fast if it clips
       smoothing   (slow)   less smoothing for percussive material, more for
                            steady/tonal material
     Everything is bounded around the mode's preset and frozen in silence. */
  _adaptTuning(dt) {
    const preset = AUTO_TUNE_PRESETS[this._autoKey];
    const m = this.audio.metrics;
    if (!preset || !this.audio.isCapturing || this.audio.isPaused || !m || m.isSilent) return;
    dt = Math.min(dt, 100);

    const st = this._autoState || (this._autoState = {
      peakEnv: m.peak, rmsEnv: m.rms, flux: 0, prevEnergy: m.energy,
    });

    // Envelopes: instant attack, slow release (peak); plain EMA (rms, flux)
    st.peakEnv = Math.max(m.peak, st.peakEnv - dt * 0.0002);
    st.rmsEnv = Util.lerp(st.rmsEnv, m.rms, 1 - Math.exp(-dt / 400));
    st.flux = Util.lerp(st.flux, Math.abs(m.energy - st.prevEnergy), 1 - Math.exp(-dt / 300));
    st.prevEnergy = m.energy;

    // --- Sensitivity: peak envelope -> target (multiplicative, deadzone) ---
    const peakTarget = AUTO_PEAK_TARGET[this._autoKey] ?? 0.85;
    let sens = this.audio.sensitivity;
    const clipping = st.peakEnv > 0.98;
    const perr = (peakTarget - st.peakEnv) / peakTarget;
    if (clipping || Math.abs(perr) > 0.06) {
      const rate = clipping ? 0.0016 : 0.0005;
      sens *= 1 + Util.clamp(perr, -0.5, 0.5) * rate * dt;
    }
    sens = Util.clamp(sens, Math.max(0.2, preset.sensitivity * 0.5), Math.min(3, preset.sensitivity * 2));

    // --- Gain: raw RMS -> healthy level, narrow band around the preset ---
    let gain = this.audio.gain;
    const rerr = (0.18 - st.rmsEnv) / 0.18;
    if (Math.abs(rerr) > 0.2) gain *= 1 + Util.clamp(rerr, -0.5, 0.5) * 0.00012 * dt;
    gain = Util.clamp(gain, preset.gain * 0.7, Math.min(4, preset.gain * 1.6));

    // --- Smoothing: transient density -> less/more smoothing ---
    const fluxNorm = Util.clamp(st.flux / 0.04, 0, 1);
    const smoothTarget = Util.clamp(preset.smoothing + (0.5 - fluxNorm) * 0.24, 0, 0.95);
    const smoothing = Util.lerp(this.audio.smoothing, smoothTarget, 1 - Math.exp(-dt / 1500));

    this.audio.setSensitivity(sens);
    this.audio.setGain(gain);
    this.audio.setSmoothing(smoothing);
    this.el.sliderSensitivity.value = sens;
    this.el.numSensitivity.value = sens.toFixed(2);
    this.el.sliderGain.value = gain;
    this.el.numGain.value = gain.toFixed(2);
    this.el.sliderSmoothing.value = smoothing;
    this.el.numSmoothing.value = smoothing.toFixed(2);
  }

  /* ---------------- THEME ---------------- */
  _bindThemeSelect() {
    this.theme.populateSelect(this.el.themeSelect);
    this.el.themeSelect.addEventListener('change', (e) => {
      this.theme.apply(e.target.value);
    });

    this.el.btnThemeMode.addEventListener('click', () => {
      this.theme.toggleLightMode();
    });
  }

  /* ---------------- START / STOP / PAUSE ---------------- */
  _bindStart() {
    this.el.btnStart.addEventListener('click', () => this._handleStartClick());
  }

  async _handleStartClick() {
    this.el.startError.textContent = '';

    if (!this.audio.isSupported) {
      this.el.startError.textContent = 'Your browser does not support tab audio capture (getDisplayMedia). Try Chrome, Edge, or Opera.';
      return;
    }

    this.el.btnStart.disabled = true;
    this.el.btnStart.style.opacity = '0.6';

    try {
      await this.audio.start();
      this._onCaptureStarted();
    } catch (err) {
      console.error(err);
      if (err && err.name === 'NotAllowedError') {
        this.el.startError.textContent = 'Permission was denied. Click "Start capture" and choose a tab with audio.';
      } else if (err && err.message === 'NO_AUDIO_TRACK') {
        this.el.startError.textContent = 'No audio track found — make sure "Share tab audio" is checked in the share dialog.';
      } else if (err && err.message === 'UNSUPPORTED') {
        this.el.startError.textContent = 'Tab audio capture is not supported in this browser.';
      } else {
        this.el.startError.textContent = 'Could not start capture. Please try again.';
      }
    } finally {
      this.el.btnStart.disabled = false;
      this.el.btnStart.style.opacity = '1';
    }
  }

  _onCaptureStarted() {
    this.el.startOverlay.classList.add('hidden');
    this.el.btnPlayPause.disabled = false;
    this.el.btnStop.disabled = false;
    this.el.rSampleRate.textContent = (this.audio.sampleRate / 1000).toFixed(1) + ' kHz';
    this.el.rLatency.textContent = this.audio.latencyMs + ' ms';
    this.engine.resetAllModes();
    this.engine.start();
    this._setPlayPauseIcon(true);
  }

  _bindToolbar() {
    this.el.btnPlayPause.addEventListener('click', () => this._togglePause());
    this.el.btnStop.addEventListener('click', () => this._handleStop());

    this._bindTunableSlider(this.el.sliderSensitivity, this.el.numSensitivity, (v) => this.audio.setSensitivity(v));
    this._bindTunableSlider(this.el.sliderGain, this.el.numGain, (v) => this.audio.setGain(v));
    this._bindTunableSlider(this.el.sliderSmoothing, this.el.numSmoothing, (v) => {
      this.audio.setSmoothing(v);
      this.settings.set('smoothing', v);
    });

    this.el.btnFullscreen.addEventListener('click', () => this._toggleFullscreen());
    this.el.btnPip.addEventListener('click', () => this._togglePiP());
    this.el.btnScreenshot.addEventListener('click', () => this._takeScreenshot());
    this.el.btnRecord.addEventListener('click', () => this._toggleRecording());

    if (!this._pipSupported()) {
      this.el.btnPip.disabled = true;
      this.el.btnPip.style.opacity = '0.4';
      this.el.btnPip.style.cursor = 'not-allowed';
      this.el.btnPip.title = 'Picture-in-Picture is not supported in this browser';
    }
  }

  /**
   * Keeps a range slider and its numeric twin in sync both ways — drag the
   * slider or type an exact value into the number field, either one updates
   * the other and calls onChange with the clamped result. Typed values are
   * clamped/committed on blur or Enter so an in-progress edit (like an
   * empty field, or "1." while typing "1.5") doesn't get forced back mid-keystroke.
   */
  _bindTunableSlider(slider, number, onChange) {
    const min = parseFloat(slider.min);
    const max = parseFloat(slider.max);
    const decimals = (slider.step.split('.')[1] || '').length;

    const apply = (value, { fromNumber = false } = {}) => {
      const clamped = Util.clamp(value, min, max);
      slider.value = clamped;
      // Don't stomp on what's being typed (e.g. "1." or a trailing zero)
      // while the number field itself is the source of the change.
      if (!fromNumber) number.value = clamped.toFixed(decimals);
      onChange(clamped);
      return clamped;
    };

    slider.addEventListener('input', () => apply(parseFloat(slider.value)));

    number.addEventListener('input', () => {
      const v = parseFloat(number.value);
      if (!Number.isNaN(v)) apply(v, { fromNumber: true });
    });

    // On blur/Enter, normalize whatever's in the box (clamp it, fill in a
    // default if it was left empty or invalid) so the field always ends up
    // showing a valid, in-range number.
    const commit = () => {
      const v = parseFloat(number.value);
      apply(Number.isNaN(v) ? parseFloat(slider.value) : v);
    };
    number.addEventListener('change', commit);
    number.addEventListener('keydown', (e) => {
      if (e.key === 'Enter') { commit(); number.blur(); }
    });

    // Seed the number field from the slider's initial value.
    number.value = parseFloat(slider.value).toFixed(decimals);
  }

  _togglePause() {
    if (!this.audio.isCapturing) return;
    if (this.audio.isPaused) {
      this.audio.resume();
      this._setPlayPauseIcon(true);
    } else {
      this.audio.pause();
      this._setPlayPauseIcon(false);
    }
  }

  _setPlayPauseIcon(isPlaying) {
    this.el.iconPlayPause.innerHTML = isPlaying
      ? '<rect x="5" y="4" width="4" height="16" rx="1" fill="currentColor"/><rect x="15" y="4" width="4" height="16" rx="1" fill="currentColor"/>'
      : '<path d="M6 4l14 8-14 8V4z" fill="currentColor"/>';
  }

  _handleStop() {
    this.audio.stop();
    this.engine.stop();
    this.el.btnPlayPause.disabled = true;
    this.el.btnStop.disabled = true;
    this._setPlayPauseIcon(true);
    this.el.startOverlay.classList.remove('hidden');
    this.el.rVolume.textContent = '— %';
    this.el.rPeakFreq.textContent = '— Hz';
    this.el.rBpm.textContent = '—';
    this.el.rSampleRate.textContent = '— kHz';
    this.el.rLatency.textContent = '— ms';
    if (this.isRecording) this._toggleRecording();
  }

  /* ---------------- PER-FRAME UI UPDATES ---------------- */
  _onFrame(dt) {
    this._updateAutoTune(dt);
    const m = this.audio.metrics;
    this.el.rVolume.textContent = Math.round(m.volume) + ' %';
    this.el.rPeakFreq.textContent = Util.formatHz(m.peakFreq) + ' Hz';
    this.el.rFps.textContent = this.engine.fps || '—';
    this.el.rBpm.textContent = this.audio.bpm > 0 ? this.audio.bpm : '—';

    // Beat flash decay
    if (this.engine.beatFlashIntensity > 0) {
      this.engine.beatFlashIntensity *= 0.88;
      this.el.beatFlash.style.opacity = this.engine.beatFlashIntensity.toFixed(3);
      if (this.engine.beatFlashIntensity < 0.01) this.engine.beatFlashIntensity = 0;
    }
  }

  /** Lightweight tick that keeps idle UI (e.g. before capture starts) responsive without the heavy audio loop. */
  _idleRenderTick() {
    requestAnimationFrame(() => this._idleRenderTick());
  }

  /* ---------------- SETTINGS PANEL ---------------- */
  _bindSettingsPanel() {
    const open = () => {
      this.el.settingsPanel.classList.add('open');
      this.el.settingsScrim.classList.add('open');
    };
    const close = () => {
      this.el.settingsPanel.classList.remove('open');
      this.el.settingsScrim.classList.remove('open');
    };
    this.el.btnSettings.addEventListener('click', open);
    this.el.btnCloseSettings.addEventListener('click', close);
    this.el.settingsScrim.addEventListener('click', close);

    // FFT size
    this.el.selFftSize.addEventListener('change', (e) => {
      const size = parseInt(e.target.value, 10);
      this.audio.setFftSize(size);
      this.el.vFftSize.textContent = size;
    });

    // Target FPS (render loop cap — 0 = unlimited)
    this.el.selTargetFps.addEventListener('change', (e) => {
      this.settings.set('targetFps', parseInt(e.target.value, 10));
    });

    // Audio latency hint — takes effect on the next capture start
    this.el.selLatencyHint.addEventListener('change', (e) => {
      const hint = e.target.value;
      this.settings.set('latencyHint', hint);
      this.audio.setLatencyHint(hint);
      const labels = { interactive: 'Interactive', balanced: 'Balanced', playback: 'Playback' };
      this.el.vLatencyHint.textContent = labels[hint] || hint;
    });

    // Bar count
    this.el.rngBarCount.addEventListener('input', (e) => {
      const v = parseInt(e.target.value, 10);
      this.settings.set('barCount', v);
      this.el.vBarCount.textContent = v;
    });

    // Peak hold
    this.el.rngPeakHold.addEventListener('input', (e) => {
      const v = parseInt(e.target.value, 10);
      this.settings.set('peakHoldTime', v);
      this.el.vPeakHold.textContent = v;
    });

    // Mirror mode
    this.el.chkMirror.addEventListener('change', (e) => {
      this.settings.set('mirrorMode', e.target.checked);
    });

    // Row count for Orchestra Mode 2 & Line Graph 2 (7-40)
    this.el.rngBandRows.addEventListener('input', (e) => {
      const v = parseInt(e.target.value, 10);
      this.settings.set('bandRows', v);
      this.el.vBandRows.textContent = v;
    });

    // More lines (Line Graph modes 1 & 2: classic 3-band vs full 7-band)
    this.el.chkMoreLines.addEventListener('change', (e) => {
      this.settings.set('moreLines', e.target.checked);
    });

    // Line width
    this.el.rngLineWidth.addEventListener('input', (e) => {
      const v = parseFloat(e.target.value);
      this.settings.set('lineWidth', v);
      this.el.vLineWidth.textContent = v.toFixed(1);
    });

    // Radius
    this.el.rngRadius.addEventListener('input', (e) => {
      const v = parseInt(e.target.value, 10);
      this.settings.set('radius', v);
      this.el.vRadius.textContent = v;
    });

    // Rotation speed
    this.el.rngRotSpeed.addEventListener('input', (e) => {
      const v = parseFloat(e.target.value);
      this.settings.set('rotationSpeed', v);
      this.el.vRotSpeed.textContent = v.toFixed(2);
    });

    // Particle count
    this.el.rngParticleCount.addEventListener('input', (e) => {
      const v = parseInt(e.target.value, 10);
      this.settings.set('particleCount', v);
      this.el.vParticleCount.textContent = v;
    });

    // Glow intensity
    this.el.rngGlow.addEventListener('input', (e) => {
      const v = parseInt(e.target.value, 10);
      this.settings.set('glowIntensity', v);
      this.el.vGlow.textContent = v;
    });

    // Background blur (applied to the .stage backdrop via CSS var)
    this.el.rngBgBlur.addEventListener('input', (e) => {
      const v = parseInt(e.target.value, 10);
      this.settings.set('bgBlur', v);
      this.el.vBgBlur.textContent = v;
      document.querySelector('.bg-glow').style.filter = `blur(${v * 2.2}px)`;
    });

    // Wave thickness (used by waveform mode as additional thickness multiplier)
    this.el.rngWaveThick.addEventListener('input', (e) => {
      const v = parseFloat(e.target.value);
      this.settings.set('waveThickness', v);
      this.el.vWaveThick.textContent = v.toFixed(1);
      this.settings.set('lineWidth', v);
      this.el.vLineWidth.textContent = v.toFixed(1);
      this.el.rngLineWidth.value = v;
    });
  }

  /* ---------------- FULLSCREEN ---------------- */
  _toggleFullscreen() {
    if (!document.fullscreenElement) {
      this.app.requestFullscreen().catch(() => { });
    } else {
      document.exitFullscreen().catch(() => { });
    }
  }

  /* ---------------- PICTURE-IN-PICTURE ----------------
     Standard video-element PiP only ever shows a <video>, so we pipe the
     visualization canvas into a hidden, muted video via captureStream()
     (the same technique already used for recording) and request PiP on
     that. The floating window then shows just the graph — no topbar,
     toolbar, or chip — and keeps updating live since the stream tracks
     the canvas in real time. */
  _pipSupported() {
    return !!(document.pictureInPictureEnabled
      && this.canvas.captureStream
      && window.HTMLVideoElement
      && HTMLVideoElement.prototype.requestPictureInPicture);
  }

  async _togglePiP() {
    if (!this._pipSupported()) return;

    if (document.pictureInPictureElement) {
      try { await document.exitPictureInPicture(); } catch (e) { /* ignore */ }
      return;
    }

    if (!this._pipVideo) {
      const video = document.createElement('video');
      video.muted = true;
      video.playsInline = true;
      video.style.cssText = 'position:fixed; top:-9999px; left:-9999px; width:1px; height:1px;';
      document.body.appendChild(video);
      video.addEventListener('leavepictureinpicture', () => {
        this.el.btnPip.classList.remove('active');
        // No visibilitychange event fires just from closing the PiP window,
        // so re-check now: if the tab is still backgrounded, the render
        // loop should go back to being paused.
        this.engine._onVisibilityChange();
      });
      this._pipVideo = video;
    }

    try {
      if (!this._pipStream) {
        this._pipStream = this.canvas.captureStream(30);
        this._pipVideo.srcObject = this._pipStream;
      }
      await this._pipVideo.play();
      await this._pipVideo.requestPictureInPicture();
      this.el.btnPip.classList.add('active');
    } catch (err) {
      console.error('PiP failed:', err);
    }
  }

  /* ---------------- SCREENSHOT ---------------- */
  _takeScreenshot() {
    if (!this.audio.isCapturing) return;
    Util.downloadCanvasPNG(this.canvas, `signal-${this.engine.currentModeKey}-${Date.now()}.png`);
    this._flashToolbarButton(this.el.btnScreenshot);
  }

  _flashToolbarButton(btn) {
    btn.style.color = 'var(--accent)';
    setTimeout(() => { btn.style.color = ''; }, 300);
  }

  /* ---------------- RECORDING ---------------- */
  _toggleRecording() {
    if (!this.audio.isCapturing) return;
    if (this.isRecording) {
      this.mediaRecorder.stop();
      return;
    }
    const stream = this.canvas.captureStream(60);
    let mimeType = 'video/webm;codecs=vp9';
    if (!MediaRecorder.isTypeSupported(mimeType)) mimeType = 'video/webm';

    this.mediaRecorder = new MediaRecorder(stream, { mimeType, videoBitsPerSecond: 6_000_000 });
    this.recordedChunks = [];

    this.mediaRecorder.ondataavailable = (e) => {
      if (e.data && e.data.size > 0) this.recordedChunks.push(e.data);
    };
    this.mediaRecorder.onstop = () => {
      const blob = new Blob(this.recordedChunks, { type: mimeType });
      const url = URL.createObjectURL(blob);
      const link = document.getElementById('downloadLink');
      link.href = url;
      link.download = `signal-recording-${Date.now()}.webm`;
      link.click();
      setTimeout(() => URL.revokeObjectURL(url), 4000);
      this.isRecording = false;
      this.el.toolbar.classList.remove('recording');
    };

    this.mediaRecorder.start();
    this.isRecording = true;
    this.el.toolbar.classList.add('recording');
  }

  /* ---------------- KEYBOARD SHORTCUTS ---------------- */
  _bindKeyboard() {
    document.addEventListener('keydown', (e) => {
      // Ignore shortcuts while typing in an input/select
      const tag = document.activeElement.tagName;
      if (tag === 'INPUT' || tag === 'SELECT' || tag === 'TEXTAREA') return;

      switch (e.key.toLowerCase()) {
        case ' ':
          e.preventDefault();
          this._togglePause();
          break;
        case 'f':
          this._toggleFullscreen();
          break;
        case 'p':
          this._togglePiP();
          break;
        case 's':
          this._takeScreenshot();
          break;
        case 'r':
          this._toggleRecording();
          break;
        case '1': this._setMode('spectrum'); break;
        case '2': this._setMode('waveform1'); break;
        case '3': this._setMode('waveform2'); break;
        case '4': this._setMode('circular'); break;
        case '5': this._setMode('linegraph1'); break;
        case '6': this._setMode('linegraph2'); break;
        case '7': this._setMode('particles'); break;
        case '8': this._setMode('orchestra1'); break;
        case '9': this._setMode('orchestra2'); break;
        case 'm': this._setMode('meterbank'); break;
        case 'l': this._setMode('meterbank2'); break;
        case 'v': this._setMode('signalmeter'); break;
        case 'e': this._setMode('spectrum2'); break;
        case 'w': this._setMode('waterfall'); break;
        case 't': this._setMode('warp'); break;
        case 'b': this._setMode('ripples'); break;
        case 'x': this._setMode('scope'); break;
        case '0': this._setMode('auto'); break;
        default: break;
      }
    });
  }
}

/* ============================================================
   SECTION 8 — BOOTSTRAP
   ============================================================ */
document.addEventListener('DOMContentLoaded', () => {
  window.__signalApp = new UIController();
});