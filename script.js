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
    this.beatCount = 0;        // increments on every detected beat (visualizers diff it)
    this.beatStrength = 0;     // 0.25-1, how far the last beat rose above the average

    // Stereo analysis: the signal is also split into L/R and fed to two small
    // analysers. They are only read while a mode asks for them (requestStereo).
    this.splitter = null;
    this.analyserL = null;
    this.analyserR = null;
    this.freqL = null; this.freqR = null;
    this.timeL = null; this.timeR = null;
    this._stereoUntil = 0;
    this._lr = new Float32Array(2);

    // Calibrated metering side-chain for Meter Bank 2 (built on demand)
    this._mb = null;
    this._meterUntil = 0;

    // Spectral feature state
    this.prevFreq = null;
    this.logBin = null;

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
      flux: 0,          // spectral flux (positive spectral change this frame)
      fluxAvg: 0,       // slow average of flux, for relative transient detection
      centroid: 0.4,    // spectral centroid, 0 (low) - 1 (bright), log-scaled
      stereo: { l: 0, r: 0, balance: 0, width: 0.5, corr: 0.8, active: false },
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
    this._setupStereo();
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
    this.prevFreq = new Uint8Array(binCount);
    this.logBin = new Float32Array(binCount);
    for (let i = 0; i < binCount; i++) this.logBin[i] = Math.log2(Math.max(1, this.binToFreq(i)));
  }

  _setupStereo() {
    try {
      const ac = this.audioCtx;
      this.splitter = ac.createChannelSplitter(2);
      this.analyserL = ac.createAnalyser();
      this.analyserR = ac.createAnalyser();
      for (const a of [this.analyserL, this.analyserR]) {
        a.fftSize = 1024;
        a.smoothingTimeConstant = 0.5;
        a.minDecibels = -100;
        a.maxDecibels = -6;
      }
      this.gainNode.connect(this.splitter);
      this.splitter.connect(this.analyserL, 0);
      this.splitter.connect(this.analyserR, 1);
      this.freqL = new Uint8Array(this.analyserL.frequencyBinCount);
      this.freqR = new Uint8Array(this.analyserR.frequencyBinCount);
      this.timeL = new Uint8Array(1024);
      this.timeR = new Uint8Array(1024);
    } catch (e) {
      this._teardownStereo();
    }
  }

  _teardownStereo() {
    try { if (this.splitter) this.splitter.disconnect(); } catch (e) { /* noop */ }
    try { if (this.analyserL) this.analyserL.disconnect(); } catch (e) { /* noop */ }
    try { if (this.analyserR) this.analyserR.disconnect(); } catch (e) { /* noop */ }
    this.splitter = this.analyserL = this.analyserR = null;
    this.freqL = this.freqR = this.timeL = this.timeR = null;
    this.metrics.stereo.active = false;
  }

  /** Modes that draw stereo information call this every frame; the L/R
   *  analysers are only read while a request is fresh. */
  requestStereo() { this._stereoUntil = performance.now() + 400; }

  /* ---------------- PRECISION METERING (used by Meter Bank 2) ----------------
     A calibrated side-chain tapped straight off the capture source — i.e.
     BEFORE the GAIN slider — so every number is a real dBFS reading and clip
     detection looks at the actual normalized sample values, not at whatever
     the visual gain happens to be. It is built lazily the first time a mode
     asks for it (requestMeters) and torn down again a couple of seconds after
     the last request, so other modes never pay for it.

       source -> stereo upmix -> splitter -> L/R x { 4096 FFT  (bands < 500 Hz, time data),
                                                     1024 FFT  (bands >= 500 Hz),
                                                     K-weighting (shelf + RLB high-pass) -> 2048 time data }

     All analysers run with smoothingTimeConstant = 0, so the viz applies its
     own (per-band) ballistics on top of raw, un-smoothed frames.
     Conventions: band / RMS levels are "sine full-scale = 0 dB" (AES17-style),
     peaks are true sample peaks, loudness is BS.1770 K-weighted (-0.691 offset). */
  requestMeters() {
    this._meterUntil = performance.now() + 600;
    if (!this._mb && this.audioCtx && this.sourceNode) this._setupMeters();
    return !!this._mb;
  }

  _setupMeters() {
    try {
      const ac = this.audioCtx;
      const mk = (fft) => {
        const a = ac.createAnalyser();
        a.fftSize = fft;
        a.smoothingTimeConstant = 0;
        a.minDecibels = -120;
        a.maxDecibels = 0;
        return a;
      };
      const mb = {
        input: ac.createGain(),
        splitter: ac.createChannelSplitter(2),
        loA: [mk(4096), mk(4096)],
        hiA: [mk(1024), mk(1024)],
        kA: [mk(2048), mk(2048)],
        kNodes: [],
        fLo: [new Float32Array(2048), new Float32Array(2048)],
        fHi: [new Float32Array(512), new Float32Array(512)],
        tLo: [new Float32Array(4096), new Float32Array(4096)],
        tK: [new Float32Array(2048), new Float32Array(2048)],
        bands: null, sr: 0,
        use: null, b0: null, b1: null,
        pow: null,                       // [band*2 + ch] mean-square amplitude (sine FS = 1)
        peak: new Float32Array(2),       // true sample peak per channel (linear)
        ms: new Float32Array(2),         // time-domain mean-square per channel
        kms: 0,                          // K-weighted mean-square, L + R summed
        clip: false,
      };
      // Mono sources get up-mixed to both channels instead of leaving R silent.
      mb.input.channelCount = 2;
      mb.input.channelCountMode = 'explicit';
      mb.input.channelInterpretation = 'speakers';
      mb.input.connect(mb.splitter);
      for (let ch = 0; ch < 2; ch++) {
        mb.splitter.connect(mb.loA[ch], ch);
        mb.splitter.connect(mb.hiA[ch], ch);
        const shelf = ac.createBiquadFilter();   // BS.1770 stage 1: head-related high shelf
        shelf.type = 'highshelf';
        shelf.frequency.value = 1681.97;
        shelf.gain.value = 4.0;
        const hp = ac.createBiquadFilter();      // BS.1770 stage 2: RLB high-pass
        hp.type = 'highpass';
        hp.frequency.value = 38.13;
        hp.Q.value = -6.0;                       // Web Audio high-pass Q is in dB (0.5 linear)
        mb.splitter.connect(shelf, ch);
        shelf.connect(hp);
        hp.connect(mb.kA[ch]);
        mb.kNodes.push(shelf, hp);
      }
      this.sourceNode.connect(mb.input);
      this._mb = mb;
    } catch (e) {
      this._teardownMeters();
    }
  }

  _teardownMeters() {
    const mb = this._mb;
    this._mb = null;
    if (!mb) return;
    try { if (this.sourceNode) this.sourceNode.disconnect(mb.input); } catch (e) { /* noop */ }
    const all = [mb.input, mb.splitter, ...mb.loA, ...mb.hiA, ...mb.kA, ...mb.kNodes];
    for (const n of all) { try { n.disconnect(); } catch (e) { /* noop */ } }
  }

  /** Works out which FFT bins feed each band. Called again only when the band
   *  list or sample rate changes. */
  _prepareMeterBands(bands) {
    const mb = this._mb, n = bands.length, sr = this.sampleRate;
    mb.bands = bands;
    mb.sr = sr;
    mb.use = new Uint8Array(n);
    mb.b0 = new Uint16Array(n);
    mb.b1 = new Uint16Array(n);
    mb.pow = new Float32Array(n * 2);
    for (let i = 0; i < n; i++) {
      const b = bands[i];
      const useHi = b.lo >= 500 ? 1 : 0;
      const N = useHi ? 1024 : 4096;
      const binHz = sr / N;
      const maxBin = N / 2 - 1;
      let b0 = Math.ceil(b.lo / binHz);
      let b1 = Math.ceil(b.hi / binHz) - 1;
      if (b1 < b0) b0 = b1 = Math.round(((b.lo + b.hi) / 2) / binHz);
      mb.use[i] = useHi;
      mb.b0[i] = Util.clamp(b0, 1, maxBin);
      mb.b1[i] = Util.clamp(b1, mb.b0[i], maxBin);
    }
  }

  /** Reads one frame of calibrated measurements for `bands` (the Meter Bank 2
   *  band list). Returns the shared meter state object (read it, don't keep
   *  it), or null when nothing is being captured. */
  updateMeters(bands, dtMs) {
    if (!this.requestMeters()) return null;
    const mb = this._mb;
    if (mb.bands !== bands || mb.sr !== this.sampleRate) this._prepareMeterBands(bands);

    // Blackman window: mean(w^2) = 0.3046. With the analyser's 1/N scaling,
    // amplitude^2 of a band = 4 * (sum of bin powers) / 0.3046 (a full-scale
    // sine therefore reads exactly 1.0 = 0 dB).
    const K = 4 / 0.3046;
    for (let ch = 0; ch < 2; ch++) {
      mb.loA[ch].getFloatFrequencyData(mb.fLo[ch]);
      mb.hiA[ch].getFloatFrequencyData(mb.fHi[ch]);
      const fLo = mb.fLo[ch], fHi = mb.fHi[ch];
      for (let i = 0; i < bands.length; i++) {
        const f = mb.use[i] ? fHi : fLo;
        let s = 0;
        for (let k = mb.b0[i], e = mb.b1[i]; k <= e; k++) {
          const d = f[k];
          if (d > -130) s += Math.exp(d * 0.23025851);   // 10^(d/10)
        }
        mb.pow[i * 2 + ch] = s * K;
      }
    }

    // Time domain: true sample peak over (at least) everything since the last
    // frame, so a one-sample overload between frames can't slip past.
    const scan = Util.clamp(Math.ceil(this.sampleRate * (dtMs / 1000) * 1.25), 256, 4096);
    let pkMax = 0, kSum = 0;
    for (let ch = 0; ch < 2; ch++) {
      const t = mb.tLo[ch];
      mb.loA[ch].getFloatTimeDomainData(t);
      let pk = 0, ss = 0;
      for (let i = t.length - scan; i < t.length; i++) { const v = t[i]; const a = v < 0 ? -v : v; if (a > pk) pk = a; }
      for (let i = t.length - 2048; i < t.length; i++) ss += t[i] * t[i];
      mb.peak[ch] = pk;
      mb.ms[ch] = ss / 2048;
      if (pk > pkMax) pkMax = pk;

      const tk = mb.tK[ch];
      mb.kA[ch].getFloatTimeDomainData(tk);
      let ks = 0;
      for (let i = 0; i < tk.length; i++) ks += tk[i] * tk[i];
      kSum += ks / tk.length;
    }
    mb.kms = kSum;
    mb.clip = pkMax >= 0.999;
    return mb;
  }

  /** Averaged L/R energy (0-1 each) for a Hz range. Returns a shared 2-slot
   *  array [left, right] — copy values out, don't hold on to it. */
  getBandLR(loHz, hiHz) {
    const out = this._lr;
    out[0] = 0; out[1] = 0;
    if (!this.freqL || !this.sampleRate) return out;
    const bins = this.freqL.length;
    const lo = Util.clamp(Math.round(loHz * 1024 / this.sampleRate), 0, bins - 1);
    const hi = Util.clamp(Math.round(hiHz * 1024 / this.sampleRate), lo, bins - 1);
    let l = 0, r = 0;
    for (let i = lo; i <= hi; i++) { l += this.freqL[i]; r += this.freqR[i]; }
    const cnt = hi - lo + 1;
    out[0] = l / cnt / 255;
    out[1] = r / cnt / 255;
    return out;
  }

  _computeStereo() {
    const a = this.analyserL, b = this.analyserR;
    if (!a || !b) return;
    a.getByteTimeDomainData(this.timeL);
    b.getByteTimeDomainData(this.timeR);
    a.getByteFrequencyData(this.freqL);
    b.getByteFrequencyData(this.freqR);
    const L = this.timeL, R = this.timeR, n = L.length;
    let ll = 0, rr = 0, lr = 0, mm = 0, ss = 0;
    for (let i = 0; i < n; i++) {
      const l = (L[i] - 128) / 128, r = (R[i] - 128) / 128;
      ll += l * l; rr += r * r; lr += l * r;
      const mid = (l + r) * 0.5, side = (l - r) * 0.5;
      mm += mid * mid; ss += side * side;
    }
    const rmsL = Math.sqrt(ll / n), rmsR = Math.sqrt(rr / n);
    const e = ll * rr;
    const corr = e > 1e-9 ? lr / Math.sqrt(e) : 1;
    const tot = mm + ss;
    const width = tot > 1e-9 ? Util.clamp(Math.sqrt(ss / tot) * 1.6, 0, 1) : 0;
    const bal = (rmsR - rmsL) / (rmsR + rmsL + 1e-4);
    const s = this.metrics.stereo, k = 0.25;
    s.l = rmsL; s.r = rmsR;
    s.balance += (bal - s.balance) * k;
    s.width += (width - s.width) * k;
    s.corr += (corr - s.corr) * k;
    s.active = true;
  }

  /** Spectral flux + centroid, computed from the same FFT frame as everything else. */
  _computeFeatures() {
    const f = this.freqData, prev = this.prevFreq, lb = this.logBin;
    if (!f || !prev || !lb || prev.length !== f.length) return;
    const n = f.length;
    let pos = 0, wsum = 0, tot = 0;
    for (let i = 1; i < n; i++) {
      const v = f[i];
      const d = v - prev[i];
      if (d > 0) pos += d;
      prev[i] = v;
      tot += v;
      wsum += v * lb[i];
    }
    const m = this.metrics;
    const fl = Math.min(4, (pos / (n * 255)) * 40);
    m.flux = fl;
    m.fluxAvg += (fl - m.fluxAvg) * 0.04;
    if (tot > 40) {
      const norm = (wsum / tot - 5.3) / (13.8 - 5.3); // ~40 Hz .. ~14 kHz, log
      m.centroid += (Util.clamp(norm, 0, 1) - m.centroid) * 0.12;
    }
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
    this._teardownMeters();
    this._teardownStereo();
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
    this._computeFeatures();
    if (this.analyserL && performance.now() < this._stereoUntil) this._computeStereo();
    if (this._mb && performance.now() > this._meterUntil + 2500) this._teardownMeters();
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
      this.beatCount++;
      this.beatStrength = Util.clamp((energy / Math.max(avg, 0.02) - 1) / 0.9, 0.25, 1);
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
      orchestraStyle: 'flow', // Orchestra Mode 2 rendering style
      bandRows: 7, // Row count for Orchestra Mode 2 & Line Graph 2 (7 = named bands, 8-15 = log-spaced slices)
      targetFps: 0, // 0 = unlimited (draw every rAF tick); otherwise caps the render loop
      latencyHint: 'interactive', // AudioContext latencyHint — applied on next capture start
      mb2Mode: 'peakrms', // Meter Bank 2: spectrum | rms | peak | peakrms | stereo | precision
      mb2PeakHold: 450, // Meter Bank 2: ms a peak marker stays put before it starts to fall
      mb2PeakFall: 40, // Meter Bank 2: peak marker fall rate once released (dB per second)
      mb2ExtCtrl: false, // Meter Bank 2: false = calibrated (ignores SENS/GAIN/SMOOTH), true = sliders apply
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

  // Row count follows settings.bandRows once "more lines" is on (7-15); the
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
    const rowCountSetting = Util.clamp(Math.round(this.settings.get('bandRows') || 7), 7, 15);
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

/* ---------------- MODE 5: PARTICLE VISUALIZER (Spectral Fireflies) ----------------
   Full redesign — the old version was just uniform drifting dots nudged by
   three blended band scalars (bass/mid/treble), so nothing about where a
   particle was or what it looked like actually corresponded to anything in
   the music. Now:
    - Every particle is assigned a point along the log-scaled spectrum and
      samples that exact frequency bin every frame, so its size/brightness
      directly reflects that part of the mix, not a generic blend.
    - Color follows the same assignment (low = accent, mid = accent3, high
      = accent2), the same idea the Spectrogram mode uses, so color has
      meaning instead of being random per particle.
    - Ambient particles drift upward like embers and fade in/out over their
      lifetime instead of just wrapping at the edges forever.
    - Real bass onsets (not just "bass is loud", an actual transient —
      same onset test Beat Ripples uses) trigger a radial burst of fresh,
      faster, brighter particles from the center, so the mode visibly
      reacts to hits instead of just ambiently shimmering. */
class ParticleViz extends Visualizer {
  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    this.particles = [];
    this.avgBass = 0;
    this.lastBurst = 0;
  }

  /** freqT (0-1): where this particle sits along the spectrum (biased low
   *  for burst particles, since they're born from a bass hit). */
  _spawn(freqT, isBurst) {
    if (isBurst) {
      const angle = Math.random() * Math.PI * 2;
      const speed = 1 + Math.random() * 2.6;
      return {
        x: this.width / 2, y: this.height * 0.55,
        vx: Math.cos(angle) * speed, vy: Math.sin(angle) * speed,
        freqT, isBurst: true,
        age: 0, maxAge: 600 + Math.random() * 500,
        size: 1.4 + Math.random() * 2.2,
      };
    }
    return {
      x: Math.random() * this.width, y: this.height + 10 + Math.random() * 30,
      vx: (Math.random() - 0.5) * 0.12, vy: -(0.22 + Math.random() * 0.4),
      freqT, isBurst: false,
      age: 0, maxAge: 4000 + Math.random() * 3500,
      size: 1 + Math.random() * 1.7,
      wobble: Math.random() * Math.PI * 2,
    };
  }

  _ensure(count) {
    while (this.particles.length < count) this.particles.push(this._spawn(Math.random(), false));
  }

  /** Low = accent, mid = accent3, high = accent2 — same register-to-color
   *  idea as the Spectrogram mode, so a particle's color tells you roughly
   *  what part of the mix it's showing. */
  _colorFor(freqT, colors) {
    if (freqT < 0.5) {
      const t = freqT * 2;
      return {
        r: Util.lerp(colors.accent.r, colors.accent3.r, t),
        g: Util.lerp(colors.accent.g, colors.accent3.g, t),
        b: Util.lerp(colors.accent.b, colors.accent3.b, t),
      };
    }
    const t = (freqT - 0.5) * 2;
    return {
      r: Util.lerp(colors.accent3.r, colors.accent2.r, t),
      g: Util.lerp(colors.accent3.g, colors.accent2.g, t),
      b: Util.lerp(colors.accent3.b, colors.accent2.b, t),
    };
  }

  draw(audio, now, dt) {
    const ctx = this.ctx;
    const { width, height } = this;
    const count = this.settings.get('particleCount');
    const colors = this.theme.getAccentColors();
    this._ensure(count);

    // Live state only: wipe the previous frame completely (no motion-blur
    // overpaint), so nothing from earlier frames lingers on screen.
    ctx.clearRect(0, 0, width, height);

    const m = audio.metrics;
    this.avgBass = Util.lerp(this.avgBass, m.bass, 0.05);
    const onset = m.bass > this.avgBass * 1.4 && m.bass > 0.26 && now - this.lastBurst > 160;
    if (onset) {
      this.lastBurst = now;
      const burstCount = Math.round(10 + m.bass * 34);
      for (let i = 0; i < burstCount; i++) this.particles.push(this._spawn(Math.random() * 0.35, true));
      const cap = Math.round(count * 1.6);
      if (this.particles.length > cap) this.particles.splice(0, this.particles.length - cap);
    }

    const freq = audio.freqData, binCount = freq.length;
    const burstPts = []; // collected this frame, for the constellation lines below
    const next = [];

    for (const p of this.particles) {
      p.age += dt;
      const lifeT = p.age / p.maxAge;
      if (lifeT >= 1) {
        if (!p.isBurst) next.push(this._spawn(Math.random(), false)); // ambient density stays constant
        continue;
      }

      if (p.isBurst) {
        p.vx *= 0.985; p.vy *= 0.985;
        p.vy += dt * 0.0011; // gentle gravity pulls the burst back down
      } else {
        p.wobble += dt * 0.0015;
        p.x += Math.sin(p.wobble) * 0.15;
      }
      p.x += p.vx * dt * 0.06;
      p.y += p.vy * dt * 0.06;

      if (p.x < -10) p.x = width + 10;
      if (p.x > width + 10) p.x = -10;
      if (!p.isBurst && p.y < -10) { next.push(this._spawn(Math.random(), false)); continue; }

      const bin = Math.min(binCount - 1, Math.floor(Math.pow(p.freqT, 1.7) * binCount));
      const e = Util.clamp((freq[bin] / 255) * audio.sensitivity, 0, 1);

      const fade = p.isBurst
        ? (1 - lifeT)
        : Math.min(1, lifeT * 6) * Math.min(1, (1 - lifeT) * 2.5); // fade in, hold, fade out
      const alpha = p.isBurst ? (0.5 + e * 0.5) * fade : (0.2 + e * 0.75) * fade;
      const size = p.size * (p.isBurst ? (1 + e * 1.3) : (0.6 + e * 1.8));
      const c = this._colorFor(p.freqT, colors);

      if (p.isBurst) {
        // Cheap halo (a second, larger, fainter fill) instead of shadowBlur —
        // true glow on hundreds of particles would be the single biggest
        // cost in this mode; reserving it for the much smaller burst set
        // keeps the hit-impact without the frame-rate tax.
        ctx.fillStyle = `rgba(${c.r},${c.g},${c.b},${alpha * 0.25})`;
        ctx.beginPath();
        ctx.arc(p.x, p.y, size * 2.4, 0, Math.PI * 2);
        ctx.fill();
        burstPts.push(p);
      }

      ctx.fillStyle = `rgba(${c.r},${c.g},${c.b},${alpha})`;
      ctx.beginPath();
      ctx.arc(p.x, p.y, size, 0, Math.PI * 2);
      ctx.fill();

      next.push(p);
    }
    this.particles = next;

    // Constellation lines between nearby burst particles only — a bounded,
    // small set, so this stays cheap even though it's an O(n^2)-shaped scan.
    if (burstPts.length > 1) {
      ctx.strokeStyle = `rgba(${colors.accent2.r},${colors.accent2.g},${colors.accent2.b},0.2)`;
      ctx.lineWidth = 1;
      ctx.beginPath();
      const maxDist = Math.min(width, height) * 0.14;
      for (let i = 0; i < burstPts.length; i++) {
        for (let j = i + 1; j < burstPts.length; j++) {
          const a = burstPts[i], b = burstPts[j];
          const dx = a.x - b.x, dy = a.y - b.y;
          if (dx * dx + dy * dy < maxDist * maxDist) {
            ctx.moveTo(a.x, a.y);
            ctx.lineTo(b.x, b.y);
          }
        }
      }
      ctx.stroke();
    }
  }

  reset() { this.particles = []; this.avgBass = 0; }
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

/* ---------------- MODE 7: ORCHESTRA MODE 2 (one living, interconnected system) ----------------
   Same rows, labels, Hz ranges and meter column as before — but the rows are
   no longer six independent graphs:

   Audio features -> per-band attack/release -> visual physics -> canvas

   - Each band family has its own look AND its own temporal response
     (Bass: slow, heavy, thick  ...  Brilliance: instant, hair-thin, sparkling).
   - Rows are coupled: neighbours bleed into each other, bass sends a slow
     upward wave through the stack, beats launch a shockwave from the
     foundation row through every band, and when many bands are active at
     once they pull into one shared arch (the "formation").
   - A central energy field sits behind the stack and follows loudness, bass,
     beats, stereo width/correlation and the spectral centroid.
   - Stereo: per-band L/R balance tilts each curve, stereo width spreads the
     energy across the row (mono collapses toward the centre), and particles
     drift to the side they came from.
   - Particles live in one pooled struct-of-arrays (no per-frame allocation),
     are drawn in batched additive passes, and inherit motion from the curves.
   - Quality adapts to frame time: particles thin out on slow devices
     and come back when there is headroom.

   Rendering stays on the 2D canvas the rest of the app (PiP, screenshots,
   recording) is built on, with pooled buffers and batched draws. */
const ORCH2_CAT = { sub: 0, bass: 1, lowmid: 2, mid: 3, highmid: 4, presence: 5, brilliance: 6 };
// Per-60fps-frame attack / release coefficients, slow -> instant by band family.
const ORCH2_ATK = [0.16, 0.20, 0.27, 0.40, 0.55, 0.75, 0.93];
const ORCH2_REL = [0.040, 0.050, 0.075, 0.130, 0.220, 0.380, 0.620];
// How long a per-band transient "ping" lingers (per-60fps-frame retention).
const ORCH2_TRANS_KEEP = [0.93, 0.92, 0.90, 0.88, 0.84, 0.80, 0.74];
const ORCH2_TAU = Math.PI * 2;

const ORCH2_STYLES = {
  flow: { fill: 1.00, parts: 1.0, core: 1.0, react: 1.0, pts: 48, additive: true },
  aurora: { fill: 0.90, parts: 0.35, core: 0.85, react: 1.0, pts: 56, additive: true, aurora: true },
  particles: { fill: 0.12, parts: 2.6, core: 0.9, react: 1.1, pts: 48, additive: true, stream: true },
  field: { fill: 0.95, parts: 0.7, core: 2.1, react: 1.0, pts: 48, additive: true, field: true },
  minimal: { fill: 0.10, parts: 0.18, core: 0.4, react: 0.8, pts: 28, additive: false, minimal: true },
  reactive: { fill: 1.05, parts: 1.8, core: 1.5, react: 1.7, pts: 48, additive: true },
};

// dt-independent version of a "per 60fps frame" smoothing coefficient.
function orchK(k60, dN) { return 1 - Math.pow(1 - k60, dN); }

class OrchestraModeV2 extends OrchestraBase {
  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    this.MAXPTS = 64;
    this.PCAP = 1100;
    this.SH = 6;   // simultaneous shockwaves
    this.RN = 3;   // simultaneous core rings

    // Reused scratch buffers (never reallocated per frame)
    this._xs = new Float32Array(this.MAXPTS);
    this._ya = new Float32Array(this.MAXPTS);
    this._yb = new Float32Array(this.MAXPTS);
    this._yc = new Float32Array(this.MAXPTS);
    this._yd = new Float32Array(this.MAXPTS);
    this._tmp = new Float32Array(this.MAXPTS);
    this._bell = new Float32Array(this.MAXPTS);
    this._dash = [3, 3];

    // Particle pool (struct of arrays)
    const P = this.PCAP;
    this.pX = new Float32Array(P); this.pY = new Float32Array(P);
    this.pVX = new Float32Array(P); this.pVY = new Float32Array(P);
    this.pLife = new Float32Array(P); this.pMax = new Float32Array(P);
    this.pSize = new Float32Array(P); this.pPh = new Float32Array(P);
    this.pCol = new Uint8Array(P); this.pKind = new Uint8Array(P); this.pKey = new Uint8Array(P);
    this.pCursor = 0;
    this._pCap = 300;

    this.shPos = new Float32Array(this.SH);
    this.shStr = new Float32Array(this.SH);
    this.ringR = new Float32Array(this.RN);
    this.ringA = new Float32Array(this.RN);

    this._f = {}; // per-frame context, filled in draw()
    this._bands = null;
    this._bandsKey = 0;
    this.rowCount = 0;
    this._resetGlobals();
    this._ensureRows(7);
  }

  _resetGlobals() {
    this.loud = 0; this.bassE = 0; this.midE = 0; this.trebE = 0; this.fluxEnv = 0;
    this.kick = 0; this.kickT = 0; this.flash = 0; this.flashT = 0;
    this.coreE = 0; this.corePulse = 0; this.corePulseT = 0;
    this.stWidth = 0.5; this.corr = 0.8; this.centroid = 0.4; this.form = 0;
    this.qual = 1; this.qualT = 0; this.dtAvg = 16.7;
    this._beatSeen = -1; this._pendingBeat = 0;
    this._lastN = 0;
    this.shStr.fill(0); this.ringA.fill(0); this.pLife.fill(0); this.pCursor = 0;
  }

  _ensureRows(rc) {
    if (rc === this.rowCount) return;
    this.rowCount = rc;
    const M = this.MAXPTS;
    const mk = () => new Float32Array(rc);
    this.bandSmoothed = mk(); this.bandPeaks = mk(); this.bandPeakHold = mk();
    this.rowFast = mk(); this.rowSlow = mk(); this.rowTrans = mk();
    this.rowBal = mk(); this.rowShock = mk(); this.rowCool = mk(); this.rowBurst = mk();
    this.emitAcc = mk();
    this.rowCat = new Uint8Array(rc);
    const grid = () => Array.from({ length: rc }, () => new Float32Array(M));
    this.samples = grid(); this.disp = grid(); this.prevDisp = grid(); this.envelope = grid();
  }

  resize(w, h, dpr) {
    super.resize(w, h, dpr);
    this.pLife.fill(0);
  }

  _buildBell(n) {
    for (let p = 0; p < n; p++) {
      const u = p / (n - 1) - 0.5;
      this._bell[p] = 0.55 + 0.45 * Math.exp(-(u * u) / 0.07);
    }
  }

  /* ---------- small drawing helpers (typed-array curves, no object churn) ---------- */
  _rgba(c, a) {
    return `rgba(${c.r | 0},${c.g | 0},${c.b | 0},${a < 0 ? 0 : a > 1 ? 1 : +a.toFixed(3)})`;
  }
  _mixRgba(c1, c2, t, a) {
    return `rgba(${(c1.r + (c2.r - c1.r) * t) | 0},${(c1.g + (c2.g - c1.g) * t) | 0},${(c1.b + (c2.b - c1.b) * t) | 0},${a < 0 ? 0 : a > 1 ? 1 : +a.toFixed(3)})`;
  }
  _a(a) { const v = a * this._f.bright; return v > 1 ? 1 : v; }

  _curveTo(ctx, xs, ys, n) {
    for (let i = 1; i < n - 1; i++) {
      ctx.quadraticCurveTo(xs[i], ys[i], (xs[i] + xs[i + 1]) * 0.5, (ys[i] + ys[i + 1]) * 0.5);
    }
    ctx.lineTo(xs[n - 1], ys[n - 1]);
  }
  _curveRev(ctx, xs, ys, n) {
    for (let k = n - 2; k >= 1; k--) {
      ctx.quadraticCurveTo(xs[k], ys[k], (xs[k] + xs[k - 1]) * 0.5, (ys[k] + ys[k - 1]) * 0.5);
    }
    ctx.lineTo(xs[0], ys[0]);
  }
  _linePath(ctx, xs, ys, n) {
    ctx.beginPath();
    ctx.moveTo(xs[0], ys[0]);
    this._curveTo(ctx, xs, ys, n);
  }
  _fillPath(ctx, xs, ys, n, baseY) {
    ctx.beginPath();
    ctx.moveTo(xs[0], baseY);
    ctx.lineTo(xs[0], ys[0]);
    this._curveTo(ctx, xs, ys, n);
    ctx.lineTo(xs[n - 1], baseY);
    ctx.closePath();
  }
  _bandPath(ctx, xs, top, bot, n) {
    ctx.beginPath();
    ctx.moveTo(xs[0], top[0]);
    this._curveTo(ctx, xs, top, n);
    ctx.lineTo(xs[n - 1], bot[n - 1]);
    this._curveRev(ctx, xs, bot, n);
    ctx.closePath();
  }
  _blur(a, n, passes) {
    const t = this._tmp;
    for (let k = 0; k < passes; k++) {
      t[0] = a[0]; t[n - 1] = a[n - 1];
      for (let p = 1; p < n - 1; p++) t[p] = a[p - 1] * 0.25 + a[p] * 0.5 + a[p + 1] * 0.25;
      for (let p = 0; p < n; p++) a[p] = t[p];
    }
  }
  // out[p] = baseY - interp(D, p + shift) * scale * H
  _shifted(D, n, shift, scale, baseY, H, out) {
    for (let p = 0; p < n; p++) {
      let f = p + shift;
      f = f < 0 ? 0 : f > n - 1 ? n - 1 : f;
      const i0 = f | 0, i1 = i0 + 1 < n ? i0 + 1 : i0, t = f - i0;
      out[p] = baseY - (D[i0] * (1 - t) + D[i1] * t) * scale * H;
    }
  }

  /* ---------- events ---------- */
  _startShock(pos, str) {
    let slot = 0, weakest = 1e9;
    for (let s = 0; s < this.SH; s++) {
      if (this.shStr[s] <= 0.02) { slot = s; weakest = -1; break; }
      if (this.shStr[s] < weakest) { weakest = this.shStr[s]; slot = s; }
    }
    this.shPos[slot] = pos;
    this.shStr[slot] = Math.min(1.4, str);
  }

  _spawn(x, y, vx, vy, life, size, col, kind) {
    const idx = this.pCursor;
    this.pCursor = (idx + 1) % this._pCap;
    this.pX[idx] = x; this.pY[idx] = y; this.pVX[idx] = vx; this.pVY[idx] = vy;
    this.pLife[idx] = life; this.pMax[idx] = life; this.pSize[idx] = size;
    this.pPh[idx] = Math.random() * ORCH2_TAU;
    this.pCol[idx] = col; this.pKind[idx] = kind;
  }

  _onBeat(str) {
    const f = this._f, st = f.st;
    const s = Util.clamp(0.35 + str * 0.65, 0.35, 1);
    this.kickT = Math.max(this.kickT, s);
    this.corePulseT = Math.max(this.corePulseT, 0.55 + 0.45 * s);
    this.flashT = Math.max(this.flashT, s);
    this._startShock(-0.8, s * st.react);
    for (let k = 0; k < this.RN; k++) {
      if (this.ringA[k] < 0.02) { this.ringR[k] = f.coreR * 0.3; this.ringA[k] = 0.6 * s; break; }
    }
    const cnt = Math.round((8 + 20 * s) * st.parts * this.qual);
    for (let q = 0; q < cnt; q++) {
      const ang = Math.random() * ORCH2_TAU;
      const sp = (90 + 170 * Math.random()) * f.ds * (0.7 + 0.5 * s);
      const ca = Math.cos(ang), sa = Math.sin(ang);
      this._spawn(f.cx + ca * f.coreR * 0.15, f.cy + sa * f.coreR * 0.15,
        ca * sp, sa * sp, 0.6 + 0.6 * Math.random(), (1.3 + 1.2 * Math.random()) * f.ds, 0, 2);
    }
  }

  /* ---------- main frame ---------- */
  draw(audio, now, dt) {
    const ctx = this.ctx;
    const W = this.width, Ht = this.height;
    const colors = this.theme.getAccentColors();
    const styleKey = this.settings.get('orchestraStyle');
    const st = ORCH2_STYLES[styleKey] || ORCH2_STYLES.flow;
    const react = st.react;

    const rowSetting = Util.clamp(Math.round(this.settings.get('bandRows') || 7), 7, 15);
    if (!this._bands || this._bandsKey !== rowSetting) {
      this._bands = rowSetting === 7 ? audio.bandDefs : audio.getDynamicBands(rowSetting);
      this._bandsKey = rowSetting;
    }
    const bands = this._bands;
    this._ensureRows(bands.length);
    const rc = bands.length;
    const n = st.pts;
    if (n !== this._lastN) { this._lastN = n; this._buildBell(n); }

    const dms = Util.clamp(dt || 16.7, 4, 50);
    const dts = dms / 1000, dN = dms / 16.667;
    const ds = Math.max(1, this.dpr * 0.8);
    this._dash[0] = 3 * ds; this._dash[1] = 3 * ds;

    // --- adaptive quality: thin out particles if frames get slow ---
    const cap = this.settings.get('targetFps') || 0;
    const budget = cap > 0 ? 1000 / cap : 16.7;
    this.dtAvg += (dms - this.dtAvg) * 0.05;
    this.qualT += dms;
    if (this.qualT > 700) {
      this.qualT = 0;
      if (this.dtAvg > Math.max(26, budget * 1.5) && this.qual > 0.3) this.qual = Math.max(0.3, this.qual - 0.15);
      else if (this.dtAvg < Math.max(19, budget * 1.15) && this.qual < 1) this.qual = Math.min(1, this.qual + 0.05);
    }
    const pc = this.settings.get('particleCount') || 600;
    this._pCap = Math.max(60, Math.min(this.PCAP, Math.round(pc * 0.55 * (0.35 + 0.65 * this.qual) * Math.max(1, st.parts * 0.7))));
    if (this.pCursor >= this._pCap) this.pCursor = 0;

    // --- audio features -> smoothed global state ---
    audio.requestStereo();
    const m = audio.metrics, sens = audio.sensitivity, sm = m.stereo;
    if (this._beatSeen < 0 || audio.beatCount < this._beatSeen) this._beatSeen = audio.beatCount;
    else if (audio.beatCount !== this._beatSeen) { this._beatSeen = audio.beatCount; this._pendingBeat = audio.beatStrength; }

    const loudT = Util.clamp(m.rms * sens * 3.2, 0, 1);
    this.loud += (loudT - this.loud) * orchK(loudT > this.loud ? 0.25 : 0.015, dN); // slow decay into silence
    this.bassE += (m.bass - this.bassE) * orchK(m.bass > this.bassE ? 0.30 : 0.06, dN);
    this.midE += (m.mid - this.midE) * orchK(m.mid > this.midE ? 0.30 : 0.08, dN);
    this.trebE += (m.treble - this.trebE) * orchK(m.treble > this.trebE ? 0.50 : 0.15, dN);
    const fluxRel = Util.clamp((m.flux / (m.fluxAvg + 0.03) - 1) * 0.5, 0, 1);
    this.fluxEnv = Math.max(fluxRel, this.fluxEnv * Math.pow(0.88, dN));
    if (sm.active) {
      this.stWidth += (sm.width - this.stWidth) * orchK(0.08, dN);
      this.corr += (sm.corr - this.corr) * orchK(0.08, dN);
    }
    this.centroid += (m.centroid - this.centroid) * orchK(0.05, dN);

    // --- geometry ---
    const rowGap = 7;
    const rowHeight = (Ht - rowGap * (rc - 1)) / rc;
    const leftColW = Math.min(150, W * 0.22);
    const rightColW = Math.min(150, W * 0.21);
    const centerX = leftColW, centerW = W - leftColW - rightColW;
    const nyquist = (audio.sampleRate || 44100) / 2;
    const step = centerW / (n - 1);
    for (let p = 0; p < n; p++) this._xs[p] = centerX + p * step;

    const f = this._f;
    f.ctx = ctx; f.st = st; f.n = n; f.ds = ds; f.now = now; f.dts = dts; f.dN = dN;
    f.centerX = centerX; f.centerW = centerW; f.W = W; f.H = Ht;
    f.cx = centerX + centerW / 2;
    f.cy = Ht * (0.5 + (this.centroid - 0.5) * 0.16);
    f.coreR = Math.min(centerW * 0.34, Ht * 0.46);
    f.colors = colors;

    // --- beat event + envelopes with real attack/decay ---
    if (this._pendingBeat > 0) { this._onBeat(this._pendingBeat); this._pendingBeat = 0; }
    this.kickT *= Math.pow(0.86, dN);
    this.kick += (this.kickT - this.kick) * orchK(this.kickT > this.kick ? 0.35 : 0.10, dN);
    this.corePulseT *= Math.pow(0.90, dN);
    this.corePulse += (this.corePulseT - this.corePulse) * orchK(this.corePulseT > this.corePulse ? 0.30 : 0.07, dN);
    this.flashT *= Math.pow(0.88, dN);
    this.flash += (this.flashT - this.flash) * orchK(this.flashT > this.flash ? 0.40 : 0.10, dN);
    const coreT = Util.clamp(this.loud * 0.75 + this.bassE * 0.45, 0, 1);
    this.coreE += (coreT - this.coreE) * orchK(coreT > this.coreE ? 0.20 : 0.012, dN);
    f.bright = 1 + this.flash * 0.35 * react + this.loud * 0.12 + (this.centroid - 0.5) * 0.10;

    // --- shockwaves travelling from the foundation up through every band ---
    const speed = rc / 0.85;
    for (let s = 0; s < this.SH; s++) {
      if (this.shStr[s] <= 0.02) continue;
      this.shPos[s] += speed * dts;
      this.shStr[s] *= Math.pow(0.5, dts);
      if (this.shPos[s] > rc + 2) this.shStr[s] = 0;
    }
    this.rowShock.fill(0);
    const shW = Math.max(1.2, rc * 0.1);
    for (let s = 0; s < this.SH; s++) {
      if (this.shStr[s] <= 0.02) continue;
      for (let i = 0; i < rc; i++) {
        const d = (i - this.shPos[s]) / shW;
        if (d > -3 && d < 3) this.rowShock[i] += this.shStr[s] * Math.exp(-d * d);
      }
    }

    // ===== PASS A: per-row analysis (energy, transients, stereo, per-point samples) =====
    let active = 0;
    for (let i = 0; i < rc; i++) {
      const band = bands[i];
      const ci = ORCH2_CAT[band.icon] === undefined ? 3 : ORCH2_CAT[band.icon];
      this.rowCat[i] = ci;
      const raw = Util.clamp(audio.getBandEnergy(band.lo, band.hi) / 255 * sens, 0, 1.2);

      // Meter value keeps the original response so the dB/% readouts behave as before.
      const prev = this.bandSmoothed[i];
      const smoothed = prev + (raw - prev) * orchK(raw > prev ? 0.45 : 0.12, dN);
      this.bandSmoothed[i] = smoothed;
      if (smoothed >= this.bandPeaks[i]) {
        this.bandPeaks[i] = smoothed;
        this.bandPeakHold[i] = now + 900;
      } else if (now > this.bandPeakHold[i]) {
        this.bandPeaks[i] = Math.max(smoothed, this.bandPeaks[i] - 0.006);
      }

      // Instantaneous level + transient (fast level vs slow baseline)
      let fast = this.rowFast[i];
      fast += (raw - fast) * orchK(raw > fast ? 0.85 : 0.35, dN);
      this.rowFast[i] = fast;
      let slow = this.rowSlow[i];
      slow += (raw - slow) * orchK(0.05, dN);
      this.rowSlow[i] = slow;
      const trNow = Util.clamp((raw - slow - 0.02) * 3.4, 0, 1);
      const trPrev = this.rowTrans[i];
      this.rowTrans[i] = Math.max(trNow, trPrev * Math.pow(ORCH2_TRANS_KEEP[ci], dN));
      this.rowCool[i] -= dts;
      if (trNow > 0.55 && trPrev < 0.45 && this.rowCool[i] <= 0) {
        this.rowCool[i] = 0.14;
        this.rowBurst[i] = trNow;
        if (react > 1.2 && ci <= 3) this._startShock(i - 0.6, 0.45 * trNow);
      }
      if (fast > 0.22) active++;

      // Stereo balance for this band (-1 left .. +1 right)
      const lr = audio.getBandLR(band.lo, band.hi);
      const bt = (lr[1] - lr[0]) / (lr[1] + lr[0] + 0.004);
      this.rowBal[i] += (bt - this.rowBal[i]) * orchK(0.12, dN);

      // Per-point samples across an extended slice of the spectrum (same
      // mapping as before) with a band-specific attack/release.
      const bandSpan = band.hi - band.lo;
      const extLo = i === 0 ? 0 : Math.max(0, band.lo - bandSpan * 0.25);
      const extHi = i === rc - 1 ? nyquist : band.hi + bandSpan * 0.25;
      const span = extHi - extLo;
      const atk = orchK(ORCH2_ATK[ci], dN), rel = orchK(ORCH2_REL[ci], dN);
      const S = this.samples[i], E = this.envelope[i];
      for (let p = 0; p < n; p++) {
        const rp = audio.getBandEnergy(extLo + (p / n) * span, extLo + ((p + 1) / n) * span) / 255 * sens;
        const sp = S[p];
        S[p] = sp + (rp - sp) * (rp > sp ? atk : rel);
        if (S[p] >= E[p]) E[p] = S[p];
        else E[p] = Math.max(S[p], E[p] - 0.008 * dN);
      }
    }

    // Formation: when many bands are active together they pull into one structure
    const act = active / rc;
    const formT = Util.clamp((act - 0.35) / 0.5, 0, 1);
    this.form += (formT - this.form) * orchK(formT > this.form ? 0.10 : 0.04, dN);
    f.form = this.form;

    // ===== PASS B: displayed curves (coupling, shock, kick, stereo, formation) =====
    const kickAmt = this.kick * react;
    const couple = 0.06 + 0.10 * this.form;
    const widthMix = Util.clamp(0.2 + this.stWidth * 1.1, 0.2, 1);
    const bell = this._bell;
    for (let i = 0; i < rc; i++) {
      const ci = this.rowCat[i];
      const S = this.samples[i], D = this.disp[i];
      const Sa = this.samples[i > 0 ? i - 1 : i], Sb = this.samples[i < rc - 1 ? i + 1 : i];
      const nTrans = 0.5 * (this.rowTrans[i > 0 ? i - 1 : i] + this.rowTrans[i < rc - 1 ? i + 1 : i]);
      const gain = 1 + 0.28 * this.rowShock[i] + (ci <= 1 ? 0.30 : 0.08) * kickAmt + 0.15 * nTrans;
      const lift = this.bassE * 0.07 * Math.sin(now * 0.0032 - i * 0.75);
      const bal = this.rowBal[i];
      const fast = this.rowFast[i];
      for (let p = 0; p < n; p++) {
        const u = p / (n - 1);
        let v = S[p] + couple * 0.5 * (Sa[p] + Sb[p]);
        v *= gain;
        v *= 1 + bal * (u - 0.5) * 1.1;                                   // left/right tilt
        v *= bell[p] + (1 - bell[p]) * widthMix;                          // mono collapses to centre
        v *= 1 + 0.18 * this.form * Math.sin(Math.PI * u);                // shared formation arch
        if (ci === 2) v += 0.05 * fast * Math.sin(u * ORCH2_TAU * 1.15 + now * 0.0007);
        if (st.field) { const d = (u - 0.5) / 0.2; v *= 1 + 0.4 * this.coreE * Math.exp(-d * d); }
        v += lift;
        D[p] = v < 0 ? 0 : v > 1.25 ? 1.25 : v;
      }
      if (ci <= 1) this._blur(D, n, ci === 0 ? 3 : 2);
      else if (ci === 2) this._blur(D, n, 2);
    }

    // ===== DRAW =====
    ctx.clearRect(0, 0, W, Ht);
    ctx.lineJoin = 'round';
    ctx.lineCap = 'round';
    this._drawCore(colors);

    const meterBarHeight = 12;
    for (let i = 0; i < rc; i++) {
      const band = bands[i];
      const y = i * (rowHeight + rowGap);
      const ci = this.rowCat[i];
      const c = ci <= 1 ? colors.accent : ci <= 4 ? colors.accent3 : colors.accent2;
      const smoothed = this.bandSmoothed[i];

      ctx.fillStyle = this._rgba(colors.accent, 0.035 + 0.05 * Math.min(1, this.rowShock[i]) + 0.02 * this.flash);
      this._roundRect(ctx, 0, y, W, rowHeight, 8);
      ctx.fill();
      // soft tint on the meter side that follows this band's instant energy
      ctx.fillStyle = this._rgba(c, 0.05 * this.rowFast[i]);
      ctx.fillRect(W - rightColW, y + 2, rightColW - 4, rowHeight - 4);

      this._drawLeftColumn(ctx, band, y, rowHeight, colors, smoothed);

      ctx.save();
      ctx.beginPath();
      ctx.rect(centerX, y + 3, centerW, rowHeight - 6);
      ctx.clip();
      this._renderRow(i, y, rowHeight, colors, c);
      ctx.restore();

      this._emitRow(i, y, rowHeight, c);
      this.prevDisp[i].set(this.disp[i]);

      this._drawBandMeter(ctx, W, rightColW, y, rowHeight, i, smoothed, this.bandPeaks[i], colors, c, meterBarHeight);
    }

    this._updateParticles(dts, centerX, centerX + centerW, Ht);
    this._drawParticles(colors);
  }

  /* ---------- central energy field ---------- */
  _drawCore(colors) {
    const f = this._f, ctx = this.ctx, st = f.st, ds = f.ds;
    const cx = f.cx, cy = f.cy, R = f.coreR;
    const e = this.coreE, pulse = this.corePulse;
    const r = R * (0.16 + 0.48 * e + 0.28 * this.bassE) + R * 0.42 * pulse;
    const a = Util.clamp((0.04 + 0.26 * e + 0.30 * pulse + 0.10 * this.flash) * st.core, 0, 0.75);
    const t = this.centroid;
    const squash = 1 + Util.clamp(this.stWidth * (1.1 - 0.6 * Math.max(0, this.corr)), 0, 1.2) * 0.9;

    // faint vertical "spine" that ties the rows together when the formation is strong
    if (this.form > 0.05 && !st.minimal) {
      const g = ctx.createLinearGradient(0, 0, 0, f.H);
      g.addColorStop(0, this._mixRgba(colors.accent, colors.accent2, 0, 0));
      g.addColorStop(0.5, this._mixRgba(colors.accent, colors.accent2, t, 0.10 * this.form));
      g.addColorStop(1, this._mixRgba(colors.accent, colors.accent2, 1, 0));
      ctx.fillStyle = g;
      ctx.fillRect(cx - 1.5 * ds, 0, 3 * ds, f.H);
    }

    if (a >= 0.01) {
      ctx.save();
      ctx.translate(cx, cy);
      ctx.scale(squash, 1);
      const g = ctx.createRadialGradient(0, 0, 0, 0, 0, Math.max(2, r));
      g.addColorStop(0, `rgba(${Math.min(255, (colors.accent.r + (colors.accent2.r - colors.accent.r) * t + 90) | 0)},${Math.min(255, (colors.accent.g + (colors.accent2.g - colors.accent.g) * t + 90) | 0)},${Math.min(255, (colors.accent.b + (colors.accent2.b - colors.accent.b) * t + 90) | 0)},${+(a * 0.9).toFixed(3)})`);
      g.addColorStop(0.35, this._mixRgba(colors.accent, colors.accent2, t, a * 0.5));
      g.addColorStop(1, this._mixRgba(colors.accent, colors.accent2, t, 0));
      ctx.fillStyle = g;
      ctx.beginPath();
      ctx.arc(0, 0, Math.max(2, r), 0, ORCH2_TAU);
      ctx.fill();

      if (st.field) {   // concentric field lines
        ctx.lineWidth = ds;
        for (let k = 1; k <= 2; k++) {
          ctx.strokeStyle = this._mixRgba(colors.accent, colors.accent2, t, (0.05 + 0.10 * e) / k);
          ctx.beginPath();
          ctx.arc(0, 0, r * (1 + k * 0.7), 0, ORCH2_TAU);
          ctx.stroke();
        }
      }
      // beat shockwave rings
      ctx.lineWidth = 1.2 * ds;
      for (let k = 0; k < this.RN; k++) {
        if (this.ringA[k] < 0.02) continue;
        this.ringR[k] += f.coreR * 1.4 * f.dts;
        this.ringA[k] *= Math.pow(0.25, f.dts);
        ctx.strokeStyle = this._mixRgba(colors.accent, colors.accent2, t, this.ringA[k] * 0.6 * st.core);
        ctx.beginPath();
        ctx.arc(0, 0, this.ringR[k], 0, ORCH2_TAU);
        ctx.stroke();
      }
      ctx.restore();
    } else {
      for (let k = 0; k < this.RN; k++) this.ringA[k] = 0;
    }
  }

  /* ---------- one row: look depends on the band family ---------- */
  _renderRow(i, y, rh, colors, c) {
    const F = this._f, ctx = F.ctx, st = F.st, n = F.n, ds = F.ds, now = F.now;
    const ci = this.rowCat[i], D = this.disp[i];
    const xs = this._xs, ya = this._ya, yb = this._yb, yc = this._yc, yd = this._yd;
    const baseY = y + rh - 5, topY = y + 5, H = rh - 12;
    const energy = this.rowFast[i], tr = this.rowTrans[i];
    const kick = this.kick * st.react;
    const fillK = st.fill;

    for (let p = 0; p < n; p++) ya[p] = baseY - D[p] * H;

    if (st.minimal) {
      ctx.fillStyle = this._rgba(c, 0.10);
      this._fillPath(ctx, xs, ya, n, baseY);
      ctx.fill();
      ctx.strokeStyle = this._rgba(c, this._a(0.85));
      ctx.lineWidth = Math.max(1, ds);
      this._linePath(ctx, xs, ya, n);
      ctx.stroke();
      return;
    }

    if (st.aurora) { this._renderAurora(i, y, rh, colors, c, baseY, H); return; }

    const add = st.additive;
    const stream = !!st.stream;

    switch (ci) {
      case 0:
      case 1: { // FOUNDATION: thick, smooth, big, glowing underneath
        if (!stream) {
          const g = ctx.createLinearGradient(0, topY, 0, baseY);
          g.addColorStop(0, this._rgba(c, this._a((0.55 + 0.25 * kick) * fillK)));
          g.addColorStop(1, this._rgba(c, 0.04));
          ctx.fillStyle = g;
          this._fillPath(ctx, xs, ya, n, baseY);
          ctx.fill();
        }
        this._linePath(ctx, xs, ya, n);
        if (add) ctx.globalCompositeOperation = 'lighter';
        ctx.strokeStyle = this._rgba(c, this._a(stream ? 0.05 : 0.10 + 0.10 * kick));
        ctx.lineWidth = ds * (7 + 4 * kick);
        ctx.stroke();
        ctx.globalCompositeOperation = 'source-over';
        ctx.strokeStyle = this._rgba(c, this._a(stream ? 0.35 : 0.95));
        ctx.lineWidth = ds * (stream ? 1.2 : 2.3 + 1.1 * kick);
        ctx.stroke();
        break;
      }
      case 2: { // LOW MID: broad flowing hills and valleys
        if (!stream) {
          const g = ctx.createLinearGradient(0, topY, 0, baseY);
          g.addColorStop(0, this._rgba(c, this._a(0.60 * fillK)));
          g.addColorStop(1, this._rgba(c, 0.04));
          ctx.fillStyle = g;
          this._fillPath(ctx, xs, ya, n, baseY);
          ctx.fill();
        }
        this._linePath(ctx, xs, ya, n);
        ctx.strokeStyle = this._rgba(c, this._a(stream ? 0.30 : 0.92));
        ctx.lineWidth = ds * (stream ? 1 : 1.8);
        ctx.stroke();
        break;
      }
      case 3: { // MID: several interacting waveform layers
        const ph = now * 0.0011 + i;
        const amp = 0.8 + 3.4 * (0.3 + this.midE) + 2 * this.fluxEnv;
        this._shifted(D, n, Math.sin(ph) * amp, 0.84, baseY, H, yb);
        this._shifted(D, n, Math.cos(ph * 1.53 + 1.7) * amp * 1.5, 0.66, baseY, H, yc);
        if (!stream) {
          const g = ctx.createLinearGradient(0, topY, 0, baseY);
          g.addColorStop(0, this._rgba(c, this._a(0.45 * fillK)));
          g.addColorStop(1, this._rgba(c, 0.03));
          ctx.fillStyle = g;
          this._fillPath(ctx, xs, ya, n, baseY);
          ctx.fill();
          ctx.fillStyle = this._rgba(colors.accent2, 0.09 + 0.10 * this.fluxEnv);   // the "weave" between layers
          this._bandPath(ctx, xs, ya, yb, n);
          ctx.fill();
        }
        if (add) ctx.globalCompositeOperation = 'lighter';
        ctx.lineWidth = ds * 1.1;
        ctx.strokeStyle = this._rgba(colors.accent, this._a(0.35));
        this._linePath(ctx, xs, yc, n); ctx.stroke();
        ctx.lineWidth = ds * 1.3;
        ctx.strokeStyle = this._rgba(colors.accent2, this._a(0.55));
        this._linePath(ctx, xs, yb, n); ctx.stroke();
        ctx.globalCompositeOperation = 'source-over';
        ctx.lineWidth = ds * 1.6;
        ctx.strokeStyle = this._rgba(c, this._a(stream ? 0.35 : 0.95));
        this._linePath(ctx, xs, ya, n); ctx.stroke();
        break;
      }
      case 4: { // HIGH MID: thin, fast, energetic ribbons
        const th = ds * (0.5 + 2.2 * tr + 1.2 * energy);
        const wob = ds * (0.4 + 2.5 * tr);
        for (let p = 0; p < n; p++) {
          const w = Math.sin(p * 0.9 + now * 0.012) * wob;
          yb[p] = ya[p] + w - th - D[p] * ds;
          yc[p] = ya[p] + w + th + D[p] * ds;
        }
        if (add) ctx.globalCompositeOperation = 'lighter';
        ctx.fillStyle = this._rgba(c, this._a((0.20 + 0.30 * tr) * (stream ? 0.4 : 1)));
        this._bandPath(ctx, xs, yb, yc, n);
        ctx.fill();
        // a second ribbon, phase-shifted, so they braid
        this._shifted(D, n, Math.sin(now * 0.004 + i) * 2.5, 0.9, baseY, H, yd);
        ctx.strokeStyle = this._rgba(colors.accent2, this._a(0.45));
        ctx.lineWidth = ds;
        this._linePath(ctx, xs, yd, n); ctx.stroke();
        ctx.globalCompositeOperation = 'source-over';
        ctx.strokeStyle = this._rgba(c, this._a(0.95));
        ctx.lineWidth = ds * 1.1;
        for (let p = 0; p < n; p++) yb[p] = ya[p] + Math.sin(p * 0.9 + now * 0.012) * wob;
        this._linePath(ctx, xs, yb, n); ctx.stroke();
        break;
      }
      case 5: { // PRESENCE: fine line; particles follow it (see _emitRow)
        if (!stream) {
          ctx.fillStyle = this._rgba(c, this._a(0.28 * fillK));
          this._fillPath(ctx, xs, ya, n, baseY);
          ctx.fill();
        }
        ctx.strokeStyle = this._rgba(c, this._a(stream ? 0.25 : 0.65));
        ctx.lineWidth = ds * 0.9;
        this._linePath(ctx, xs, ya, n); ctx.stroke();
        break;
      }
      default: { // BRILLIANCE: hair-thin luminous lines (stars come from _emitRow)
        if (add) ctx.globalCompositeOperation = 'lighter';
        this._linePath(ctx, xs, ya, n);
        ctx.strokeStyle = this._rgba(c, this._a(0.09));
        ctx.lineWidth = ds * 3.2;
        ctx.stroke();
        ctx.strokeStyle = this._rgba(c, this._a(stream ? 0.30 : 0.95));
        ctx.lineWidth = Math.max(1, ds * 0.8);
        ctx.stroke();
        this._shifted(D, n, Math.sin(now * 0.009 + i) * 1.5, 0.94, baseY, H, yb);
        for (let p = 0; p < n; p++) yb[p] -= 1.6 * ds;
        ctx.strokeStyle = this._rgba(colors.accent3, this._a(0.35));
        ctx.lineWidth = Math.max(1, ds * 0.6);
        this._linePath(ctx, xs, yb, n); ctx.stroke();
        ctx.globalCompositeOperation = 'source-over';
        break;
      }
    }

    // peak-hold ceiling (kept from the original, hairline now) on the lower bands
    if (ci <= 3 && !stream) {
      const E = this.envelope[i];
      for (let p = 0; p < n; p++) yd[p] = baseY - E[p] * H;
      ctx.setLineDash(this._dash);
      ctx.strokeStyle = this._rgba(colors.accent2, 0.35);
      ctx.lineWidth = Math.max(1, ds * 0.7);
      this._linePath(ctx, xs, yd, n); ctx.stroke();
      ctx.setLineDash([]);
    }
  }

  // AURORA: luminous flowing ribbons instead of filled graphs
  _renderAurora(i, y, rh, colors, c, baseY, H) {
    const F = this._f, ctx = F.ctx, st = F.st, n = F.n, ds = F.ds, now = F.now;
    const ci = this.rowCat[i], xs = this._xs, ya = this._ya;
    const energy = this.rowFast[i];
    const kick = this.kick * st.react;
    const flow = H * 0.06 * (0.25 + energy);
    for (let p = 0; p < n; p++) {
      ya[p] += Math.sin((p / (n - 1)) * ORCH2_TAU * 1.4 + now * 0.0007 * (1 + ci * 0.15) + i * 0.9) * flow;
    }
    const g = ctx.createLinearGradient(0, baseY - H, 0, baseY);
    g.addColorStop(0, this._rgba(c, this._a(0.30 * st.fill)));
    g.addColorStop(1, this._rgba(c, 0));
    ctx.fillStyle = g;
    this._fillPath(ctx, xs, ya, n, baseY);
    ctx.fill();

    const hg = ctx.createLinearGradient(F.centerX, 0, F.centerX + F.centerW, 0);
    const other = ci <= 4 ? colors.accent2 : colors.accent;
    hg.addColorStop(0, this._rgba(c, 1));
    hg.addColorStop(0.5, this._mixRgba(c, other, 0.5, 1));
    hg.addColorStop(1, this._rgba(other, 1));
    ctx.globalCompositeOperation = 'lighter';
    ctx.strokeStyle = hg;
    this._linePath(ctx, xs, ya, n);
    const k = ci <= 1 ? 1 + 0.6 * kick : 1;
    const widths = [9 * k, 5, 2.2, 1.0], alphas = [0.05, 0.09, 0.32, 0.9];
    for (let w = 0; w < 4; w++) {
      ctx.globalAlpha = this._a(alphas[w]);
      ctx.lineWidth = ds * widths[w];
      ctx.stroke();
    }
    ctx.globalAlpha = 1;
    ctx.globalCompositeOperation = 'source-over';
  }

  /* ---------- particles inherit motion from the curves ---------- */
  _emitRow(i, y, rh, c) {
    const F = this._f, st = F.st, n = F.n, ds = F.ds;
    const k = st.parts * this.qual;
    if (k <= 0.02) return;
    const ci = this.rowCat[i];
    const D = this.disp[i], PD = this.prevDisp[i], xs = this._xs;
    const baseY = y + rh - 5, H = rh - 12;
    const e = this.rowFast[i], tr = this.rowTrans[i];
    const colIdx = ci <= 1 ? 0 : ci <= 4 ? 1 : 2;
    const bal = this.rowBal[i];

    let rate = 0;
    if (ci === 5) rate = 5 + 55 * e + 70 * this.fluxEnv;
    else if (ci === 6) rate = 6 + 70 * e + 140 * tr;
    else if (st.stream) rate = (ci <= 1 ? 3 : 5) + 30 * e;
    else if (ci === 4) rate = 40 * tr;
    else if (ci === 3 && st.react > 1.2) rate = 25 * tr;
    rate *= k;
    this.emitAcc[i] += rate * F.dts;
    let cnt = this.emitAcc[i] | 0;
    if (cnt > 6) { cnt = 6; this.emitAcc[i] = 0; } else this.emitAcc[i] -= cnt;

    for (let q = 0; q < cnt; q++) {
      let p = 0;
      for (let t = 0; t < 3; t++) { p = (Math.random() * n) | 0; if (D[p] > Math.random() * 0.8) break; }
      const px = xs[p], py = baseY - D[p] * H;
      const slope = D[p + 1 < n ? p + 1 : p] - D[p > 0 ? p - 1 : p];
      const dv = D[p] - PD[p];
      const vy = -((ci === 6 ? 30 + 90 * Math.random() : 14 + 34 * Math.random()) * ds) - Math.max(0, dv) * H * 40;
      const vx = (Math.random() - 0.5) * 14 * ds - slope * H * 3 + bal * 55 * ds;
      const life = ci === 6 ? 0.35 + 0.55 * Math.random() : 0.5 + 0.5 * Math.random();
      const size = (ci === 6 ? 0.9 + 0.8 * Math.random() : ci === 5 ? 1.2 : 1.5) * ds;
      this._spawn(px, py, vx, vy, life, size, colIdx, ci === 6 ? 1 : 0);
    }

    // Transient burst: sparks leave from the tallest point of the spike
    if (this.rowBurst[i] > 0) {
      const b = this.rowBurst[i];
      this.rowBurst[i] = 0;
      if (ci >= 3 || st.react > 1.2) {
        let pk = 0;
        for (let p = 1; p < n; p++) if (D[p] > D[pk]) pk = p;
        const num = Math.round((3 + 6 * b) * k);
        for (let q = 0; q < num; q++) {
          this._spawn(xs[pk], baseY - D[pk] * H,
            (Math.random() - 0.5) * 80 * ds + bal * 70 * ds, -(110 + 150 * Math.random()) * ds,
            0.3 + 0.4 * Math.random(), (1 + Math.random()) * ds, colIdx, 3);
        }
      }
    }
  }

  _updateParticles(dts, left, right, bottom) {
    const drag = Math.pow(0.12, dts);
    for (let i = 0; i < this.PCAP; i++) {
      if (this.pLife[i] <= 0) continue;
      this.pLife[i] -= dts;
      if (this.pLife[i] <= 0) continue;
      if (this.pKind[i] === 2) { this.pVX[i] *= drag; this.pVY[i] *= drag; }
      this.pX[i] += this.pVX[i] * dts;
      this.pY[i] += this.pVY[i] * dts;
      if (this.pX[i] < left || this.pX[i] > right || this.pY[i] < -10 || this.pY[i] > bottom + 10) this.pLife[i] = 0;
    }
  }

  _drawParticles(colors) {
    const F = this._f, ctx = this.ctx, ds = F.ds, now = F.now;
    let live = 0, stars = 0;
    for (let i = 0; i < this.PCAP; i++) {
      if (this.pLife[i] <= 0) { this.pKey[i] = 255; continue; }
      let a = this.pLife[i] / this.pMax[i];
      if (this.pKind[i] === 1) { a *= 0.6 + 0.4 * Math.sin(this.pPh[i] + now * 0.012); if (this.pSize[i] > 1.7 * ds) stars++; }
      const b = a > 0.75 ? 3 : a > 0.5 ? 2 : a > 0.25 ? 1 : 0;
      this.pKey[i] = this.pCol[i] * 4 + b;
      live++;
    }
    if (!live) return;
    ctx.save();
    ctx.beginPath();
    ctx.rect(F.centerX, 0, F.centerW, F.H);
    ctx.clip();
    if (F.st.additive) ctx.globalCompositeOperation = 'lighter';
    const palette = [colors.accent, colors.accent3, colors.accent2];
    const alphaOf = [0.18, 0.38, 0.62, 0.9];
    for (let col = 0; col < 3; col++) {
      for (let b = 0; b < 4; b++) {
        const key = col * 4 + b;
        const style = this._rgba(palette[col], this._a(alphaOf[b]));
        ctx.beginPath();
        let any = false;
        for (let i = 0; i < this.PCAP; i++) {
          if (this.pKey[i] !== key) continue;
          const s = this.pSize[i];
          ctx.rect(this.pX[i] - s * 0.5, this.pY[i] - s * 0.5, s, s);
          any = true;
        }
        if (any) { ctx.fillStyle = style; ctx.fill(); }
        if (stars > 0 && col === 2) {
          ctx.beginPath();
          let anyStar = false;
          for (let i = 0; i < this.PCAP; i++) {
            if (this.pKey[i] !== key || this.pKind[i] !== 1 || this.pSize[i] <= 1.7 * ds) continue;
            const s = this.pSize[i] * 1.4, x = this.pX[i], y = this.pY[i];
            ctx.moveTo(x - s, y); ctx.lineTo(x + s, y);
            ctx.moveTo(x, y - s); ctx.lineTo(x, y + s);
            anyStar = true;
          }
          if (anyStar) { ctx.strokeStyle = style; ctx.lineWidth = Math.max(1, ds * 0.7); ctx.stroke(); }
        }
      }
    }
    ctx.restore();
  }

  /* Right column: the original dB/% bar, now paired with a vertical meter that
     shows the band's instantaneous energy (fast, un-smoothed) and flashes on
     transients. The numbers stay, but quieter. */
  _drawBandMeter(ctx, width, rightColW, y, rowHeight, i, smoothed, peak, colors, c, barHeight) {
    const fast = Util.clamp(this.rowFast[i], 0, 1), tr = this.rowTrans[i];
    const vx = width - rightColW + 3, vw = 5, vy = y + 4, vh = rowHeight - 8;
    ctx.fillStyle = this._rgba(colors.accent, 0.10);
    this._roundRect(ctx, vx, vy, vw, vh, 2.5);
    ctx.fill();
    if (fast > 0.01) {
      const fh = Math.max(2, vh * fast);
      ctx.fillStyle = this._rgba(c, 0.9);
      this._roundRect(ctx, vx, vy + vh - fh, vw, fh, 2.5);
      ctx.fill();
      ctx.fillStyle = this._rgba(colors.accent2, 0.25 + 0.7 * tr);
      ctx.fillRect(vx, vy + vh - fh, vw, 2);
    }

    const meterX = width - rightColW + 16;
    const meterW = rightColW - 30;
    const meterY = y + rowHeight / 2 - barHeight / 2;
    ctx.fillStyle = this._rgba(colors.accent, 0.12);
    this._roundRect(ctx, meterX, meterY, meterW, barHeight, barHeight / 2);
    ctx.fill();
    ctx.fillStyle = this._rgba(c, 0.9);
    this._roundRect(ctx, meterX, meterY, Math.max(0, meterW * Util.clamp(smoothed, 0, 1)), barHeight, barHeight / 2);
    ctx.fill();
    const peakX = meterX + meterW * Util.clamp(peak, 0, 1);
    ctx.fillStyle = this._rgba(colors.accent2, 0.95);
    ctx.fillRect(peakX - 1, meterY - 2, 2, barHeight + 4);

    const db = smoothed > 0.001 ? (20 * Math.log10(smoothed)).toFixed(0) : '-∞';
    ctx.font = '500 10px "JetBrains Mono", monospace';
    ctx.fillStyle = this._rgba(colors.accent, 0.5);
    ctx.textAlign = 'right';
    ctx.fillText(`${db}dB  ${Math.round(smoothed * 100)}%`, width - 14, meterY + barHeight + 10);
    ctx.textAlign = 'left';
  }

  reset() {
    this._resetGlobals();
    for (const a of [this.bandSmoothed, this.bandPeaks, this.bandPeakHold, this.rowFast, this.rowSlow,
    this.rowTrans, this.rowBal, this.rowShock, this.rowCool, this.rowBurst, this.emitAcc]) a.fill(0);
    for (const g of [this.samples, this.disp, this.prevDisp, this.envelope]) for (const arr of g) arr.fill(0);
    this._beatSeen = -1;
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

/* ---------------- MODE: METER BANK 2 (precision multi-band meter) ----------------
   The advanced counterpart to Meter Bank: same horizontal segmented rows,
   labels and Hz ranges, but driven by calibrated measurements (see
   AudioEngine.updateMeters) instead of the cosmetic spectrum bytes.

   Per band:   RMS fill (band-specific attack/release) + peak marker with hold
               and a timed decay + short-lived transient marker +
               zone-coloured segments (normal -> critical).
   Master:     L/R meters, shared dB scale, CLIP latch, PEAK / RMS / LUFS / DYN.
   Controls:   SENS/GAIN/SMOOTH button (default OFF = calibrated, sliders ignored).
   Modes:      Spectrum, RMS, Peak, Peak + RMS (default), Stereo, Precision —
               picked from the pills at the top or Settings -> Meter Bank 2.

   Performance: one canvas, no DOM. Segment tracks are prebuilt Path2Ds (one
   fill per zone per row), colours come from a palette rebuilt only when the
   theme colour changes, all state lives in typed arrays allocated once, and
   readout strings are only rebuilt ~15x/sec. No blur/shadow effects. */
const MB2 = {
  MODES: ['spectrum', 'rms', 'peak', 'peakrms', 'stereo', 'precision'],
  LABELS: {
    spectrum: ['SPECTRUM', 'SPEC'], rms: ['RMS', 'RMS'], peak: ['PEAK', 'PK'],
    peakrms: ['PEAK + RMS', 'PK+RMS'], stereo: ['STEREO', 'ST'], precision: ['PRECISION', 'PREC'],
  },
  MIN_DB: -60,
  MAX_SEG: 120,
  TICKS: [-60, -48, -36, -24, -12, -6, 0],
  // Per band: [attack ms, release ms, transient threshold dB above the slow average].
  // Bass is slow, treble is fast — closer to how those ranges actually move.
  RESPONSE: {
    'Sub Bass': [90, 450, 6.0], 'Bass 1': [80, 420, 5.5], 'Bass 2': [70, 380, 5.5], 'Bass 3': [60, 340, 5.5],
    'Low Mid': [45, 260, 5.5], 'Mid': [40, 240, 5.5], 'High Mid': [20, 200, 6.0],
    'Presence': [12, 120, 6.5], 'Brilliance': [6, 90, 7.0],
  },
  DEFAULT_RESPONSE: [40, 240, 5.5],
  // Level zones by dBFS: Normal < -24 <= Elevated < -12 <= High < -6 <= Near clipping < -1 <= Critical
  ZONE_EDGES: [-24, -12, -6, -1],
  ZONE_BASE: [0.55, 0.68, 0.78, 0.90, 1.0], // resting intensity of a lit segment per zone
  AMBER: [255, 176, 32],
  RED: [255, 59, 74],
  MASTER_ATTACK: 40, MASTER_RELEASE: 300,
  PEAKENV_FALL_DB_S: 60, // Peak-mode fill
  CLIP_LATCH_MS: 3500,
  LUFS_TAU_MS: 3000,
  // Neutral points for the SENS / GAIN / SMOOTH sliders when they are enabled:
  // 1.0 / 1.0 / 0.78 (the engine defaults) leave the meter exactly as calibrated.
  NEUTRAL_SMOOTH: 0.78,
  CTL_LABEL: ['SENS/GAIN/SMOOTH', 'CTRL'],
};

const mb2Frac = (db) => { const f = (db - MB2.MIN_DB) / -MB2.MIN_DB; return f < 0 ? 0 : f > 1 ? 1 : f; };

class MeterBankV2 extends OrchestraBase {
  constructor(ctx, settings, theme) {
    super(ctx, settings, theme);
    this._bands = null;
    this._n = 0;

    // Palette / style strings (rebuilt only when theme colours change)
    this._palKey = new Int16Array(6).fill(-1);
    this._pal = new Array(40).fill('');
    this._sty = {
      track: ['', '', '', '', ''], glow: '', grid: '', gridHi: '', txtDim: '', txtMid: '', txtBright: '',
      marker: 'rgba(255,255,255,0.92)', clipOn: 'rgba(255,59,74,0.95)', clipGhost: '', pillOn: '', pillBorderOn: '',
      pillBorder: '', balLow: '', balMid: '', balHigh: '', trackNeutral: '',
    };

    // Cached geometry (rebuilt when the layout changes)
    this._geo = { row: null, lane: null, master: null };
    this._layoutKey = '';
    this._pillW = new Float32Array(6);
    this._hit = new Float32Array(24);      // 6 pills x [x, y, w, h]
    this._clipRect = new Float32Array(4);
    this._ctlRect = new Float32Array(4);    // SENS/GAIN/SMOOTH enable button
    this._ctlLbl = { on: '', off: '' };
    this.L = { k: 1, stripX: 0, stripW: 0, rowsY: 0, rowH: 0, rowGap: 0, masterY: 0, masterH: 0, laneH: 0, lanesTop: 0, segH: 0, leftW: 0, narrow: false };

    // Master state (index 0 = L, 1 = R)
    this.mMs = new Float32Array(2);
    this.mRmsDb = new Float32Array(2).fill(-120);
    this.mHold = new Float32Array(2).fill(-120);
    this.mHoldT = new Float64Array(2);
    this.statPk = -120; this.statPkT = 0;
    this.statRms = -120; this.lufsMs = 0;
    this.clipUntil = 0; this.clipCount = 0;
    this.shares = new Float32Array(3).fill(1 / 3);

    this._textAt = 0;
    this.txt = { pk: '—', rms: '—', lufs: '—', dyn: '—', pkU: '—', rmsU: '—', dynU: '—' };
    this._lastDt = 16;
    this._lh = new Float32Array(3);
  }

  _alloc(n) {
    this._n = n;
    const n3 = n * 3;
    this.ms = new Float32Array(n3);
    this.rmsDb = new Float32Array(n3).fill(-120);
    this.inst = new Float32Array(n3).fill(-120);
    this.hold = new Float32Array(n3).fill(-120);
    this.holdT = new Float64Array(n3);
    this.pkEnv = new Float32Array(n3).fill(-120);
    this.slow = new Float32Array(n);
    this.armed = new Uint8Array(n).fill(1);
    this.trig = new Float32Array(n);
    this.lastTrig = new Float64Array(n);
    this.grp = new Uint8Array(n);
    this.resp = new Array(n);
    this.hzTxt = new Array(n);
    this.rmsTxt = new Array(n).fill('-∞ dB');
    this.pkTxt = new Array(n).fill('');
    this.crestTxt = new Array(n).fill('');
    this.balance = new Float32Array(n);
    for (let i = 0; i < n; i++) {
      const b = this._bands[i];
      this.resp[i] = MB2.RESPONSE[b.name] || MB2.DEFAULT_RESPONSE;
      this.grp[i] = /^(Sub|Bass)/.test(b.name) ? 0 : /Mid$/.test(b.name) ? 1 : 2;
      this.hzTxt[i] = `${b.lo}–${b.hi >= 1000 ? (b.hi / 1000) + 'k' : b.hi} Hz`;
    }
  }

  /* ---------------- public bits used by the UI ---------------- */
  clearClip() { this.clipUntil = 0; }

  _hitAt(x, y) {
    const h = this._hit;
    for (let m = 0; m < 6; m++) {
      const o = m * 4;
      if (h[o + 2] > 0 && x >= h[o] && x <= h[o] + h[o + 2] && y >= h[o + 1] && y <= h[o + 1] + h[o + 3]) return m;
    }
    const c = this._clipRect;
    if (c[2] > 0 && x >= c[0] && x <= c[0] + c[2] && y >= c[1] && y <= c[1] + c[3]) return 100;
    const t = this._ctlRect;
    if (t[2] > 0 && x >= t[0] && x <= t[0] + t[2] && y >= t[1] && y <= t[1] + t[3]) return 101;
    return -1;
  }
  hitTest(x, y) { return this._hitAt(x, y) >= 0; }
  onPointer(x, y) {
    const h = this._hitAt(x, y);
    if (h < 0) return false;
    if (h === 100) this.clearClip();
    else if (h === 101) this.settings.set('mb2ExtCtrl', !this.settings.get('mb2ExtCtrl'));
    else this.settings.set('mb2Mode', MB2.MODES[h]);
    return true;
  }

  /* ---------------- palette ---------------- */
  _ensurePalette(colors) {
    const a = colors.accent, b = colors.accent3, key = this._palKey;
    if (key[0] === a.r && key[1] === a.g && key[2] === a.b && key[3] === b.r && key[4] === b.g && key[5] === b.b) return;
    key[0] = a.r; key[1] = a.g; key[2] = a.b; key[3] = b.r; key[4] = b.g; key[5] = b.b;
    const lift = (c) => [Math.min(255, c.r + (255 - c.r) * 0.2) | 0, Math.min(255, c.g + (255 - c.g) * 0.2) | 0, Math.min(255, c.b + (255 - c.b) * 0.2) | 0];
    const zc = [[a.r, a.g, a.b], lift(a), [b.r, b.g, b.b], MB2.AMBER, MB2.RED];
    const trackA = [0.07, 0.07, 0.08, 0.10, 0.12];
    for (let z = 0; z < 5; z++) {
      const c = zc[z];
      for (let lv = 0; lv < 8; lv++) this._pal[z * 8 + lv] = `rgba(${c[0]},${c[1]},${c[2]},${(0.16 + 0.84 * lv / 7).toFixed(3)})`;
      this._sty.track[z] = `rgba(${c[0]},${c[1]},${c[2]},${trackA[z]})`;
    }
    const s = this._sty;
    s.glow = `rgba(${a.r},${a.g},${a.b},0.045)`;
    s.grid = `rgba(${a.r},${a.g},${a.b},0.055)`;
    s.gridHi = `rgba(${a.r},${a.g},${a.b},0.12)`;
    s.txtDim = `rgba(${a.r},${a.g},${a.b},0.42)`;
    s.txtMid = `rgba(${a.r},${a.g},${a.b},0.65)`;
    s.txtBright = `rgba(${Math.min(255, a.r + 40)},${Math.min(255, a.g + 40)},${Math.min(255, a.b + 40)},0.94)`;
    s.clipGhost = `rgba(${a.r},${a.g},${a.b},0.22)`;
    s.pillOn = `rgba(${a.r},${a.g},${a.b},0.20)`;
    s.pillBorderOn = `rgba(${a.r},${a.g},${a.b},0.70)`;
    s.pillBorder = `rgba(${a.r},${a.g},${a.b},0.16)`;
    s.balLow = `rgba(${a.r},${a.g},${a.b},0.8)`;
    s.balMid = `rgba(${b.r},${b.g},${b.b},0.8)`;
    s.balHigh = `rgba(${colors.accent2.r},${colors.accent2.g},${colors.accent2.b},0.8)`;
    s.trackNeutral = `rgba(${a.r},${a.g},${a.b},0.12)`;
  }

  /* ---------------- measurement + ballistics ---------------- */
  _step(audio, now, dt) {
    const bands = this._bands, n = this._n;
    const mb = audio.updateMeters(bands, dt);
    const holdMs = this.settings.get('mb2PeakHold') || 450;
    const fall = (this.settings.get('mb2PeakFall') || 40) * dt / 1000;
    const envFall = MB2.PEAKENV_FALL_DB_S * dt / 1000;
    const ms = this.ms, rmsDb = this.rmsDb, inst = this.inst, hold = this.hold, holdT = this.holdT;
    const pkEnv = this.pkEnv;
    const slowC = 1 - Math.exp(-dt / 260), trigDecay = Math.exp(-dt / 120);

    // SENS / GAIN / SMOOTH only count when the button is on; off = calibrated.
    // SENS x GAIN offsets every level; SMOOTH stretches/shrinks the meter's own
    // response times (neutral at the engine defaults, so 'on' at defaults = no change).
    let g = 1, tm = 1;
    if (this.settings.get('mb2ExtCtrl')) {
      g = Math.max(0, (audio.sensitivity == null ? 1 : audio.sensitivity) * (audio.gain == null ? 1 : audio.gain));
      const s = Util.clamp(audio.smoothing == null ? MB2.NEUTRAL_SMOOTH : audio.smoothing, 0.05, 0.98);
      tm = Util.clamp(Math.log(MB2.NEUTRAL_SMOOTH) / Math.log(s), 0.15, 12);
    }
    const g2 = g * g;

    for (let i = 0; i < n; i++) {
      const pL = mb ? mb.pow[i * 2] * g2 : 0, pR = mb ? mb.pow[i * 2 + 1] * g2 : 0;
      const resp = this.resp[i];
      const ca = 1 - Math.exp(-dt / (resp[0] * tm)), cr = 1 - Math.exp(-dt / (resp[1] * tm));
      for (let j = 0; j < 3; j++) {
        const k = i * 3 + j;
        const p = j === 0 ? pL : j === 1 ? pR : (pL + pR) * 0.5;
        const m = ms[k];
        const nm = m + (p - m) * (p > m ? ca : cr);
        ms[k] = nm;
        const x = p > 1e-12 ? 10 * Math.log10(p) : -120;
        const r = nm > 1e-12 ? 10 * Math.log10(nm) : -120;
        inst[k] = x;
        rmsDb[k] = r;
        const c = x > r ? x : r;                       // a peak is never below the RMS it rides on
        // Peak hold: instant attack, hold, then a steady fall.
        if (c >= hold[k]) { hold[k] = c; holdT[k] = now + holdMs; }
        else if (now > holdT[k]) { const h = hold[k] - fall; hold[k] = h > c ? h : c; }
        // Peak-mode envelope (fast attack, quick release)
        if (c >= pkEnv[k]) pkEnv[k] = c; else { const e = pkEnv[k] - envFall; pkEnv[k] = e > c ? e : c; }
      }
      // Transient detection on the mix: a sudden jump over the slow average
      const pm = (pL + pR) * 0.5, xm = inst[i * 3 + 2];
      const slowDb = this.slow[i] > 1e-12 ? 10 * Math.log10(this.slow[i]) : -120;
      const rise = xm - slowDb;
      if (this.armed[i] && rise > resp[2] && xm > -50 && now - this.lastTrig[i] > 90) {
        this.trig[i] = 1; this.lastTrig[i] = now; this.armed[i] = 0;
      } else {
        this.trig[i] *= trigDecay;
        if (!this.armed[i] && rise < resp[2] * 0.5) this.armed[i] = 1;
      }
      this.slow[i] += (pm - this.slow[i]) * slowC;
      const b = (pR - pL) / (pR + pL + 1e-9);
      this.balance[i] += (b - this.balance[i]) * 0.15;
    }

    // ----- master -----
    const ca = 1 - Math.exp(-dt / (MB2.MASTER_ATTACK * tm)), cr = 1 - Math.exp(-dt / (MB2.MASTER_RELEASE * tm));
    let pkNow = -120;
    for (let c = 0; c < 2; c++) {
      const pk = mb ? mb.peak[c] * g : 0;
      const x = pk > 1e-6 ? 20 * Math.log10(pk) : -120;
      if (x > pkNow) pkNow = x;
      const m = mb ? 2 * mb.ms[c] * g2 : 0;               // sine FS = 1.0 -> 0 dB, same scale as the bands
      const sm = this.mMs[c];
      const nm = sm + (m - sm) * (m > sm ? ca : cr);
      this.mMs[c] = nm;
      const r = nm > 1e-12 ? 10 * Math.log10(nm) : -120;
      this.mRmsDb[c] = r;
      const cand = x > r ? x : r;
      if (cand >= this.mHold[c]) { this.mHold[c] = cand; this.mHoldT[c] = now + holdMs; }
      else if (now > this.mHoldT[c]) { const h = this.mHold[c] - fall; this.mHold[c] = h > cand ? h : cand; }
    }
    // headline PEAK stat: holds ~2 s, then eases down
    if (pkNow >= this.statPk) { this.statPk = pkNow; this.statPkT = now + 2000; }
    else if (now > this.statPkT) { const h = this.statPk - 10 * dt / 1000; this.statPk = h > pkNow ? h : pkNow; }
    const avg = 0.5 * (this.mMs[0] + this.mMs[1]);
    this.statRms = avg > 1e-12 ? 10 * Math.log10(avg) : -120;
    // LUFS (K-weighted, ~3 s window, -70 LUFS absolute gate)
    if (mb) {
      const kms = mb.kms * g2;
      if (kms > 1e-12 && -0.691 + 10 * Math.log10(kms) > -70) {
        this.lufsMs = this.lufsMs === 0 ? kms : this.lufsMs + (kms - this.lufsMs) * (1 - Math.exp(-dt / MB2.LUFS_TAU_MS));
      }
      // Real clip detection: actual sample values at/over 0.999 of full scale.
      if (mb.clip) { this.clipUntil = now + MB2.CLIP_LATCH_MS; this.clipCount++; }
    }
    // overall spectral balance (low / mid / high share of band energy)
    let lo = 0, mi = 0, hi = 0;
    for (let i = 0; i < n; i++) { const e = ms[i * 3 + 2]; if (this.grp[i] === 0) lo += e; else if (this.grp[i] === 1) mi += e; else hi += e; }
    const tot = lo + mi + hi;
    if (tot > 1e-9) {
      const sc = 1 - Math.exp(-dt / 250);
      this.shares[0] += (lo / tot - this.shares[0]) * sc;
      this.shares[1] += (mi / tot - this.shares[1]) * sc;
      this.shares[2] += (hi / tot - this.shares[2]) * sc;
    }
  }

  _refreshText(now) {
    if (now - this._textAt < 66) return;
    this._textAt = now;
    const f1 = (db) => (db <= -99 ? '-∞' : db.toFixed(1));
    for (let i = 0; i < this._n; i++) {
      const k = i * 3 + 2;
      this.rmsTxt[i] = `${f1(this.rmsDb[k])} dB`;
      this.pkTxt[i] = `PEAK ${f1(this.hold[k])} dB`;
      const crest = this.hold[k] - this.rmsDb[k];
      this.crestTxt[i] = this.rmsDb[k] <= -99 ? '' : `CF ${crest.toFixed(1)}`;
    }
    const t = this.txt;
    const silent = this.statPk <= -99 || this.statRms <= -99;
    t.pk = f1(this.statPk);
    t.rms = f1(this.statRms);
    t.lufs = this.lufsMs > 1e-9 ? (-0.691 + 10 * Math.log10(this.lufsMs)).toFixed(1) : '-∞';
    t.dyn = silent ? '—' : Math.max(0, this.statPk - this.statRms).toFixed(1);
    t.pkU = this.statPk <= -99 ? t.pk : t.pk + ' dB';
    t.rmsU = this.statRms <= -99 ? t.rms : t.rms + ' dB';
    t.dynU = silent ? t.dyn : t.dyn + ' dB';
  }

  /* ---------------- geometry ---------------- */
  _makeGeo(stripW, segH, k) {
    const segCount = Util.clamp(Math.round(stripW / (10.5 * k)), 28, MB2.MAX_SEG);
    const pitch = stripW / segCount;
    const gap = Math.max(1, pitch * 0.22);
    const segW = pitch - gap;
    const zone = new Uint8Array(segCount);
    const paths = [new Path2D(), new Path2D(), new Path2D(), new Path2D(), new Path2D()];
    const e = MB2.ZONE_EDGES;
    for (let s = 0; s < segCount; s++) {
      const d = MB2.MIN_DB + (-MB2.MIN_DB) * ((s + 0.5) / segCount);
      const z = d < e[0] ? 0 : d < e[1] ? 1 : d < e[2] ? 2 : d < e[3] ? 3 : 4;
      zone[s] = z;
      paths[z].rect(s * pitch, 0, segW, segH);
    }
    return { segCount, pitch, segW, segH, zone, paths, w: stripW, h: segH, k };
  }

  /** Returns the cached geometry for a slot, rebuilding only if the size changed. */
  _useGeo(slot, stripW, segH, k) {
    const cur = this._geo[slot];
    if (cur && cur.w === stripW && cur.h === segH && cur.k === k) return cur;
    return (this._geo[slot] = this._makeGeo(stripW, segH, k));
  }

  _computeLayout(W, H, k, ctx) {
    const L = this.L;
    const cssH = H / k;
    L.k = k;
    L.narrow = W / k < 720;
    L.leftW = Math.min(170 * k, W * 0.26);
    const readoutW = 64 * k;
    L.stripX = L.leftW;
    L.stripW = Math.max(60 * k, W - L.leftW - readoutW - 10 * k);
    const hdrH = 40 * k;
    L.masterH = (cssH < 470 ? 64 : 86) * k;
    L.masterY = hdrH;
    L.laneH = (cssH < 470 ? 12 : 15) * k;
    const lanesTotal = L.laneH * 2 + 4 * k;
    L.lanesTop = L.masterY + (L.masterH - (lanesTotal + 14 * k)) / 2 + 2 * k;
    const n = this._n;
    L.rowGap = (n > 10 ? 3 : 5) * k;
    L.rowsY = L.masterY + L.masterH + 6 * k;
    L.rowH = (H - L.rowsY - 4 * k - L.rowGap * (n - 1)) / n;
    L.segH = Util.clamp(L.rowH * 0.5, 8 * k, 22 * k);

    // pill widths depend on font + narrow flag, so measure only when layout changes
    ctx.font = `600 ${9 * k}px "JetBrains Mono", monospace`;
    let x = W - 14 * k;
    const py = 10 * k, ph = 20 * k;
    for (let m = 5; m >= 0; m--) {
      const label = MB2.LABELS[MB2.MODES[m]][L.narrow ? 1 : 0];
      const w = ctx.measureText(label).width + 16 * k;
      this._pillW[m] = w;
      x -= w;
      this._hit[m * 4] = x; this._hit[m * 4 + 1] = py; this._hit[m * 4 + 2] = w; this._hit[m * 4 + 3] = ph;
      x -= 5 * k;
    }
    // SENS/GAIN/SMOOTH enable button, sized for its longer ("OFF") state so it never jitters
    const base = MB2.CTL_LABEL[L.narrow ? 1 : 0];
    this._ctlLbl.on = `${base} · ON`;
    this._ctlLbl.off = `${base} · OFF`;
    const cw = ctx.measureText(this._ctlLbl.off).width + 16 * k;
    this._ctlRect[0] = x - 5 * k - cw; this._ctlRect[1] = py; this._ctlRect[2] = cw; this._ctlRect[3] = ph;
  }

  /* ---------------- drawing ---------------- */
  /** One segmented strip. `fill` is a 0..1 fraction of the dB scale. */
  _strip(ctx, geo, x, y, fill, trans, forceTop) {
    const sc = geo.segCount, pitch = geo.pitch, segW = geo.segW, segH = geo.segH, zone = geo.zone, pal = this._pal, sty = this._sty;
    ctx.save();
    ctx.translate(x, y);
    for (let z = 0; z < 5; z++) { ctx.fillStyle = sty.track[z]; ctx.fill(geo.paths[z]); }
    const head = fill * sc;
    if (head > 0.2) { ctx.fillStyle = sty.glow; ctx.fillRect(-2, -3, head * pitch + 4, segH + 6); }
    const headSeg = Math.floor(head);
    const base = MB2.ZONE_BASE;
    let last = '';
    for (let s = 0; s < sc; s++) {
      let cover = head - s;
      cover = cover <= 0 ? 0 : cover >= 1 ? 1 : cover;
      let i = 0;
      if (cover > 0) {
        i = cover * base[zone[s]];
        if (trans > 0.02 && s >= headSeg - 5) i += 0.4 * trans;   // brief lift of the segments at the head
      }
      if (forceTop && s >= sc - 5) i = 1;
      if (i > 1) i = 1;
      if (i < 0.04) continue;                                    // live level only — no afterglow from earlier frames
      const st = pal[zone[s] * 8 + (i >= 1 ? 7 : (i * 8) | 0)];
      if (st !== last) { ctx.fillStyle = st; last = st; }
      ctx.fillRect(s * pitch, 0, segW, segH);
    }
    ctx.restore();
  }

  _stat(ctx, label, val, sx, sy, colW, k) {
    ctx.fillStyle = this._sty.txtDim; ctx.textAlign = 'left'; ctx.fillText(label, sx, sy);
    ctx.fillStyle = this._sty.txtBright; ctx.textAlign = 'right'; ctx.fillText(val, sx + colW, sy);
  }

  _zoneOf(db) {
    const e = MB2.ZONE_EDGES;
    return db < e[0] ? 0 : db < e[1] ? 1 : db < e[2] ? 2 : db < e[3] ? 3 : 4;
  }

  _holdMarker(ctx, x, y, w, segH, holdDb, k, withArrow) {
    const f = (holdDb - MB2.MIN_DB) / -MB2.MIN_DB;
    if (f < 0.02) return;
    const mx = x + (f > 1 ? 1 : f) * w;
    const z = this._zoneOf(holdDb);
    ctx.fillStyle = z >= 3 ? this._pal[z * 8 + 7] : this._sty.marker;
    ctx.fillRect(mx - 1 * k, y - 2 * k, 2 * k, segH + 4 * k);
    if (withArrow) {
      ctx.beginPath();
      ctx.moveTo(mx, y + segH + 2.5 * k);
      ctx.lineTo(mx - 3 * k, y + segH + 7 * k);
      ctx.lineTo(mx + 3 * k, y + segH + 7 * k);
      ctx.closePath();
      ctx.fill();
    }
  }

  draw(audio, now, dt) {
    const ctx = this.ctx;
    const W = this.width, H = this.height;
    const k = Math.max(0.75, this.dpr || 1);
    dt = Util.clamp(dt || this._lastDt, 1, 100);
    this._lastDt = dt;
    if (!this._bands) { this._bands = audio.getMeterBank2Bands(); this._alloc(this._bands.length); }
    const colors = this.theme.getAccentColors();
    this._ensurePalette(colors);

    let mode = this.settings.get('mb2Mode');
    if (MB2.MODES.indexOf(mode) < 0) mode = 'peakrms';

    if (!audio.isPaused) this._step(audio, now, dt);
    this._refreshText(now);

    const key = `${W}|${H}|${k}`;
    if (key !== this._layoutKey) { this._layoutKey = key; this._computeLayout(W, H, k, ctx); }
    const L = this.L, sty = this._sty, pal = this._pal, n = this._n;
    const geoRow = this._useGeo('row', L.stripW, L.segH, k);
    const geoLane = this._useGeo('lane', L.stripW, Math.max(3 * k, (L.segH - 1.5 * k) / 2), k);
    const geoMaster = this._useGeo('master', L.stripW, L.laneH, k);

    const stereoMode = mode === 'stereo';
    const showHold = mode !== 'rms';
    const showTrans = mode === 'peakrms' || mode === 'precision' || mode === 'peak';
    const showPeakTxt = mode === 'peak' || mode === 'peakrms' || mode === 'precision';
    const showBal = mode === 'stereo' || mode === 'precision';
    const precision = mode === 'precision';
    const clipActive = now < this.clipUntil;
    const frac = mb2Frac;

    ctx.clearRect(0, 0, W, H);
    ctx.textBaseline = 'middle';

    // ===== header: meter-mode pills =====
    const cur = MB2.MODES.indexOf(mode);
    ctx.font = `600 ${9 * k}px "JetBrains Mono", monospace`;
    ctx.textAlign = 'center';
    for (let m = 0; m < 6; m++) {
      const o = m * 4, px = this._hit[o], py = this._hit[o + 1], pw = this._hit[o + 2], ph = this._hit[o + 3];
      const on = m === cur;
      this._roundRect(ctx, px, py, pw, ph, ph / 2);
      if (on) { ctx.fillStyle = sty.pillOn; ctx.fill(); }
      ctx.strokeStyle = on ? sty.pillBorderOn : sty.pillBorder;
      ctx.lineWidth = Math.max(1, k * 0.8);
      ctx.stroke();
      ctx.fillStyle = on ? sty.txtBright : sty.txtDim;
      ctx.fillText(MB2.LABELS[MB2.MODES[m]][L.narrow ? 1 : 0], px + pw / 2, py + ph / 2 + 0.5 * k);
    }
    {
      const cr = this._ctlRect, ext = !!this.settings.get('mb2ExtCtrl');
      this._roundRect(ctx, cr[0], cr[1], cr[2], cr[3], cr[3] / 2);
      if (ext) { ctx.fillStyle = sty.pillOn; ctx.fill(); }
      ctx.strokeStyle = ext ? sty.pillBorderOn : sty.pillBorder;
      ctx.lineWidth = Math.max(1, k * 0.8);
      ctx.stroke();
      ctx.fillStyle = ext ? sty.txtBright : sty.txtDim;
      ctx.fillText(ext ? this._ctlLbl.on : this._ctlLbl.off, cr[0] + cr[2] / 2, cr[1] + cr[3] / 2 + 0.5 * k);
    }
    ctx.textAlign = 'left';

    // ===== dB grid (behind everything) + scale under the master =====
    const lanesBottom = L.lanesTop + L.laneH * 2 + 4 * k;
    const gridBottom = L.rowsY + n * (L.rowH + L.rowGap) - L.rowGap;
    ctx.lineWidth = Math.max(1, k * 0.8);
    ctx.beginPath();
    ctx.strokeStyle = sty.grid;
    for (let t = 0; t < MB2.TICKS.length - 1; t++) {
      const gx = Math.round(L.stripX + frac(MB2.TICKS[t]) * L.stripW) + 0.5;
      ctx.moveTo(gx, lanesBottom + 2 * k); ctx.lineTo(gx, gridBottom);
    }
    ctx.stroke();
    ctx.font = `500 ${8.5 * k}px "JetBrains Mono", monospace`;
    ctx.textAlign = 'center';
    for (let t = 0; t < MB2.TICKS.length; t++) {
      const db = MB2.TICKS[t];
      const gx = L.stripX + frac(db) * L.stripW;
      ctx.fillStyle = db >= -6 ? sty.txtMid : sty.txtDim;
      ctx.fillText(db === 0 ? '0 dB' : String(db), gx, lanesBottom + 9 * k);
      ctx.fillRect(Math.round(gx) - 0.5 * k, lanesBottom + 1.5 * k, Math.max(1, k * 0.8), 2.5 * k);
    }
    ctx.textAlign = 'left';

    // ===== master section =====
    const mx = 14 * k;
    ctx.font = `700 ${10.5 * k}px "Space Grotesk", sans-serif`;
    ctx.fillStyle = sty.txtBright;
    ctx.fillText('MASTER', mx, L.masterY + 11 * k);
    // CLIP indicator (also the clear button)
    const cw = 34 * k, ch = 14 * k, cx = mx + 62 * k, cy = L.masterY + 4 * k;
    this._clipRect[0] = cx; this._clipRect[1] = cy; this._clipRect[2] = cw; this._clipRect[3] = ch;
    ctx.font = `700 ${8.5 * k}px "JetBrains Mono", monospace`;
    ctx.textAlign = 'center';
    if (clipActive) {
      ctx.fillStyle = sty.clipOn;
      this._roundRect(ctx, cx, cy, cw, ch, 3 * k);
      ctx.fill();
      ctx.fillStyle = '#fff';
    } else {
      ctx.fillStyle = sty.clipGhost;
    }
    ctx.fillText('CLIP', cx + cw / 2, cy + ch / 2 + 0.5 * k);
    ctx.textAlign = 'left';

    // compact statistics (2 x 2)
    const stacked = L.masterH >= 80 * k;
    const yR1 = L.masterY + 25 * k;
    ctx.font = `500 ${9 * k}px "JetBrains Mono", monospace`;
    let statsBottom;
    if (stacked) {
      const w = L.leftW - mx - 28 * k, step = 11.5 * k, t = this.txt;
      this._stat(ctx, 'PEAK', t.pkU, mx, yR1, w, k);
      this._stat(ctx, 'RMS', t.rmsU, mx, yR1 + step, w, k);
      this._stat(ctx, 'LUFS', t.lufs, mx, yR1 + step * 2, w, k);
      this._stat(ctx, 'DYNAMIC', t.dynU, mx, yR1 + step * 3, w, k);
      statsBottom = yR1 + step * 3;
    } else {
      const colW = (L.leftW - mx - 22 * k) / 2, t = this.txt;
      this._stat(ctx, 'PEAK', t.pk, mx, yR1, colW, k);
      this._stat(ctx, 'RMS', t.rms, mx + colW, yR1, colW, k);
      this._stat(ctx, 'LUFS', t.lufs, mx, yR1 + 12 * k, colW, k);
      this._stat(ctx, 'DYN', t.dyn, mx + colW, yR1 + 12 * k, colW, k);
      statsBottom = yR1 + 12 * k;
    }
    ctx.textAlign = 'left';
    if (precision && stacked) {
      // overall spectral balance: a thin low | mid | high split, only in Precision
      const by = statsBottom + 9 * k, bw = L.leftW - mx - 28 * k, bh = 4 * k;
      ctx.fillStyle = sty.trackNeutral;
      ctx.fillRect(mx, by, bw, bh);
      const s0 = this.shares[0] * bw, s1 = this.shares[1] * bw;
      ctx.fillStyle = sty.balLow; ctx.fillRect(mx, by, Math.max(0, s0 - 1), bh);
      ctx.fillStyle = sty.balMid; ctx.fillRect(mx + s0, by, Math.max(0, s1 - 1), bh);
      ctx.fillStyle = sty.balHigh; ctx.fillRect(mx + s0 + s1, by, Math.max(0, bw - s0 - s1), bh);
      ctx.font = `500 ${7.5 * k}px "JetBrains Mono", monospace`;
      ctx.fillStyle = sty.txtDim;
      ctx.fillText('LOW · MID · HIGH', mx, by + bh + 7 * k);
    }

    // master L / R lanes
    for (let c = 0; c < 2; c++) {
      const ly = L.lanesTop + c * (L.laneH + 4 * k);
      this._strip(ctx, geoMaster, L.stripX, ly, frac(this.mRmsDb[c]), 0, clipActive);
      this._holdMarker(ctx, L.stripX, ly, L.stripW, L.laneH, this.mHold[c], k, false);
      ctx.font = `600 ${8.5 * k}px "JetBrains Mono", monospace`;
      ctx.fillStyle = sty.txtMid;
      ctx.textAlign = 'right';
      ctx.fillText(c === 0 ? 'L' : 'R', L.stripX - 6 * k, ly + L.laneH / 2 + 0.5 * k);
      ctx.textAlign = 'left';
    }
    const mpk = Math.max(this.mHold[0], this.mHold[1]);
    ctx.font = `500 ${9 * k}px "JetBrains Mono", monospace`;
    ctx.fillStyle = mpk >= -3 ? pal[this._zoneOf(mpk) * 8 + 7] : sty.txtMid;
    ctx.fillText(mpk <= -99 ? '-∞ dB' : `${mpk.toFixed(1)} dB`, L.stripX + L.stripW + 8 * k, L.lanesTop + L.laneH + 2 * k);

    // ===== band rows =====
    const bands = this._bands;
    const showHz = L.rowH >= 22 * k;
    const lineCount = 1 + (showHz ? 1 : 0) + (showPeakTxt && L.rowH >= 42 * k ? 1 : 0);
    for (let i = 0; i < n; i++) {
      const band = bands[i];
      const y = L.rowsY + i * (L.rowH + L.rowGap);
      const cyRow = y + L.rowH / 2;
      const km = i * 3 + 2;
      const level = frac(this.rmsDb[km]);

      // --- left column: glyph, name, Hz, (peak)
      ctx.fillStyle = `rgba(${colors.accent.r},${colors.accent.g},${colors.accent.b},${0.5 + level * 0.5})`;
      ctx.save();
      ctx.scale(k, k);
      this._drawBandGlyph(ctx, 16, cyRow / k, band.icon, colors, level);
      ctx.restore();
      const lh = this._lh;
      lh[0] = 13 * k; lh[1] = 11 * k; lh[2] = 11 * k;
      let blockH = 0;
      for (let l = 0; l < lineCount; l++) blockH += lh[l];
      let ty = cyRow - blockH / 2 + lh[0] / 2;
      ctx.font = `600 ${12 * k}px "Space Grotesk", sans-serif`;
      ctx.fillStyle = sty.txtBright;
      ctx.fillText(band.name, 40 * k, ty);
      ctx.font = `400 ${9 * k}px "JetBrains Mono", monospace`;
      if (showHz) { ty += (lh[0] + lh[1]) / 2; ctx.fillStyle = sty.txtDim; ctx.fillText(this.hzTxt[i], 40 * k, ty); }
      if (lineCount > 2) { ty += lh[1] / 2 + lh[2] / 2; ctx.fillStyle = sty.txtMid; ctx.fillText(this.pkTxt[i], 40 * k, ty); }

      // --- the strip(s)
      const sy = cyRow - L.segH / 2;
      if (stereoMode) {
        const laneH = geoLane.segH;
        for (let c = 0; c < 2; c++) {
          const ly = sy + c * (laneH + 1.5 * k);
          const kk = i * 3 + c;
          this._strip(ctx, geoLane, L.stripX, ly, frac(this.rmsDb[kk]), 0, false);
          this._holdMarker(ctx, L.stripX, ly, L.stripW, laneH, this.hold[kk], k, false);
        }
        ctx.font = `600 ${7.5 * k}px "JetBrains Mono", monospace`;
        ctx.fillStyle = sty.txtDim;
        ctx.textAlign = 'right';
        ctx.fillText('L', L.stripX - 5 * k, sy + laneH / 2);
        ctx.fillText('R', L.stripX - 5 * k, sy + laneH * 1.5 + 1.5 * k);
        ctx.textAlign = 'left';
      } else {
        const fillDb = mode === 'peak' ? this.pkEnv[km] : this.rmsDb[km];
        const tr = showTrans ? this.trig[i] : 0;
        this._strip(ctx, geoRow, L.stripX, sy, frac(fillDb), tr, false);
        if (showHold) this._holdMarker(ctx, L.stripX, sy, L.stripW, L.segH, this.hold[km], k, L.rowH >= 36 * k);
        if (tr > 0.05) {
          // transient marker: a small dot just past the strip, fading in ~0.25 s
          ctx.globalAlpha = Math.min(1, tr);
          ctx.fillStyle = sty.marker;
          ctx.beginPath();
          ctx.arc(L.stripX + L.stripW + 6 * k, cyRow, 2.6 * k, 0, Math.PI * 2);
          ctx.fill();
          ctx.globalAlpha = 1;
        }
      }

      // --- right readout (RMS dB), + crest / balance in Precision / Stereo
      const rx = W - 6 * k;
      ctx.font = `500 ${9.5 * k}px "JetBrains Mono", monospace`;
      ctx.textAlign = 'right';
      const two = (showBal || precision) && L.rowH >= 34 * k;
      const three = two && precision && !stereoMode && L.rowH >= 46 * k;
      ctx.fillStyle = sty.txtBright;
      ctx.fillText(this.rmsTxt[i], rx, three ? cyRow - 11 * k : two ? cyRow - 7 * k : cyRow);
      if (two) {
        if (three && this.crestTxt[i]) {
          ctx.font = `400 ${8 * k}px "JetBrains Mono", monospace`;
          ctx.fillStyle = sty.txtDim;
          ctx.fillText(this.crestTxt[i], rx, cyRow + 1 * k);
        }
        if (showBal) {
          const bw = 34 * k, bx = rx - bw, by = cyRow + (three ? 11 : 8) * k;
          ctx.fillStyle = sty.trackNeutral;
          ctx.fillRect(bx, by, bw, 3 * k);
          ctx.fillStyle = sty.txtMid;
          ctx.fillRect(bx + bw / 2 - 0.5 * k, by - 1.5 * k, Math.max(1, k), 6 * k);          // centre tick
          const dot = bx + bw / 2 + Util.clamp(this.balance[i], -1, 1) * (bw / 2 - 2 * k);
          ctx.fillStyle = sty.txtBright;
          ctx.fillRect(dot - 2 * k, by - 1 * k, 4 * k, 5 * k);
        }
      }
      ctx.textAlign = 'left';
    }
  }

  reset() {
    if (this._n) {
      this.ms.fill(0); this.rmsDb.fill(-120); this.inst.fill(-120); this.hold.fill(-120); this.holdT.fill(0);
      this.pkEnv.fill(-120); this.slow.fill(0); this.armed.fill(1); this.trig.fill(0);
      this.lastTrig.fill(0); this.balance.fill(0);
      this.rmsTxt.fill('-∞ dB'); this.pkTxt.fill(''); this.crestTxt.fill('');
    }
    this.mMs.fill(0); this.mRmsDb.fill(-120); this.mHold.fill(-120); this.mHoldT.fill(0);
    this.statPk = -120; this.statPkT = 0; this.statRms = -120; this.lufsMs = 0;
    this.clipUntil = 0; this.clipCount = 0;
    this.shares.fill(1 / 3);
    this.txt.pk = this.txt.rms = this.txt.lufs = this.txt.dyn = this.txt.pkU = this.txt.rmsU = this.txt.dynU = '—';
    this._textAt = 0;
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

    ctx.clearRect(0, 0, width, height);

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

    ctx.clearRect(0, 0, width, height);

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

    ctx.clearRect(0, 0, width, height);

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
    // Capped device-pixel-ratio for the canvas buffer. Lite Mode lowers
    // this to 1 (a real resolution cut — fewer pixels to fill every frame,
    // less GPU/RAM), normal use caps it at 2.5 to avoid wasting fill-rate
    // on displays with absurdly high DPR.
    this.dprCap = 2.5;

    // Modes with clickable on-canvas controls (Meter Bank 2's mode pills and
    // CLIP indicator) expose hitTest/onPointer in canvas pixel coordinates.
    this._pointerTarget = () => {
      let m = this.currentMode;
      if (m && m === this.modes.auto && m.siblings) m = m.siblings[m.activeKey] || m;
      return m && m.onPointer ? m : null;
    };
    const toCanvas = (e) => {
      const r = canvas.getBoundingClientRect();
      return [(e.clientX - r.left) * (canvas.width / Math.max(1, r.width)), (e.clientY - r.top) * (canvas.height / Math.max(1, r.height))];
    };
    canvas.addEventListener('click', (e) => {
      const m = this._pointerTarget();
      if (!m) return;
      const [x, y] = toCanvas(e);
      m.onPointer(x, y);
    });
    canvas.addEventListener('mousemove', (e) => {
      const m = this._pointerTarget();
      if (!m) { if (canvas.style.cursor) canvas.style.cursor = ''; return; }
      const [x, y] = toCanvas(e);
      const over = m.hitTest(x, y);
      const want = over ? 'pointer' : '';
      if (canvas.style.cursor !== want) canvas.style.cursor = want;
    });
  }

  observe(container) {
    this._resizeObserver.observe(container);
    this._handleResize();
  }

  /** Forces the next _handleResize to actually reallocate the canvas even
   *  if its CSS size hasn't changed, by invalidating the cached buffer size. */
  setDprCap(cap) {
    this.dprCap = cap;
    this.canvas.width = 0;
    this._handleResize();
  }

  _handleResize() {
    const rect = this.canvas.getBoundingClientRect();
    const dpr = Math.min(window.devicePixelRatio || 1, this.dprCap);
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
  particles: 'Draws hundreds of individually alpha-blended, frequency-sampled particles every frame, plus halo fills and burst connections on bass hits.',
  warp: 'Renders a large moving starfield with glow and a recomputed radial gradient every frame.',
  waterfall: 'Copies and redraws a full-resolution scrolling image buffer every frame.',
  ripples: 'Layers several overlapping blurred glow rings and gradients every frame.',
  scope: 'Uses additive blending and glow across two full traces every frame.',
  orchestra2: 'Layers trails, additive glow strokes, a central energy field and a pooled particle system across every band row each frame. Pick the Minimal style in Settings for a much lighter version.',
};

/* The small set of visualizations Lite Mode restricts you to — each is a
   handful of strokes/fills per frame with no glow-heavy gradients, no
   per-frame full-canvas pixel copies, and no hundreds-of-shapes overdraw,
   so they stay cheap even at higher frame rates. */
const LITE_MODES = ['spectrum', 'waveform1', 'linegraph1', 'meterbank'];

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
    this.liteMode = false;
    this._litePrev = null;
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
      btnLiteMode: document.getElementById('btnLiteMode'),
      liteBadge: document.getElementById('liteBadge'),
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
      selOrchStyle: document.getElementById('selOrchStyle'),
      vOrchStyle: document.getElementById('vOrchStyle'),
      selLatencyHint: document.getElementById('selLatencyHint'),
      vLatencyHint: document.getElementById('vLatencyHint'),
      rngBarCount: document.getElementById('rngBarCount'),
      rngBandRows: document.getElementById('rngBandRows'),
      selMb2Mode: document.getElementById('selMb2Mode'),
      rngMb2Hold: document.getElementById('rngMb2Hold'),
      vMb2Hold: document.getElementById('vMb2Hold'),
      rngMb2Fall: document.getElementById('rngMb2Fall'),
      chkMb2Ext: document.getElementById('chkMb2Ext'),
      vMb2Fall: document.getElementById('vMb2Fall'),
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
      if (LITE_MODES.includes(key)) btn.classList.add('lite-allowed');
      btn.addEventListener('click', () => this._setMode(key));
      this.el.vizSelect.appendChild(btn);
    });
  }

  _setMode(key) {
    if (this.liteMode && key !== 'auto' && !LITE_MODES.includes(key)) return; // locked to the lite set
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
    this.el.btnLiteMode.addEventListener('click', () => this._setLiteMode(!this.liteMode));
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

    // Orchestra Mode 2 rendering style
    this.el.selOrchStyle.addEventListener('change', (e) => {
      const opt = e.target.options[e.target.selectedIndex];
      this.settings.set('orchestraStyle', e.target.value);
      this.el.vOrchStyle.textContent = opt ? opt.textContent.replace('Orchestra — ', '') : e.target.value;
    });

    // Meter Bank 2: meter mode (also switchable from the pills on the canvas),
    // peak-hold time and peak fall rate
    this.el.selMb2Mode.addEventListener('change', (e) => this.settings.set('mb2Mode', e.target.value));
    this.settings.on('mb2Mode', (v) => { if (this.el.selMb2Mode.value !== v) this.el.selMb2Mode.value = v; });
    this.el.chkMb2Ext.addEventListener('change', (e) => this.settings.set('mb2ExtCtrl', e.target.checked));
    this.settings.on('mb2ExtCtrl', (v) => { if (this.el.chkMb2Ext.checked !== !!v) this.el.chkMb2Ext.checked = !!v; });
    this.el.rngMb2Hold.addEventListener('input', (e) => {
      const v = parseInt(e.target.value, 10);
      this.settings.set('mb2PeakHold', v);
      this.el.vMb2Hold.textContent = v;
    });
    this.el.rngMb2Fall.addEventListener('input', (e) => {
      const v = parseInt(e.target.value, 10);
      this.settings.set('mb2PeakFall', v);
      this.el.vMb2Fall.textContent = v;
    });

    // Row count for Orchestra Mode 2 & Line Graph 2 (7-15)
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

  /* ---------------- LITE MODE ----------------
     Turns down everything that costs real GPU/CPU/RAM and restricts the
     mode toolbar to LITE_MODES, remembering whatever was active first so
     it can all be put back exactly when toggled off. Doesn't touch
     anything the person didn't ask to change (sensitivity, gain, theme,
     etc.) — only the specific knobs that actually drive resource use. */
  _setLiteMode(on) {
    this.liteMode = on;
    document.body.classList.toggle('lite-mode', on);
    this.el.btnLiteMode.classList.toggle('active', on);
    this.el.btnLiteMode.setAttribute('aria-pressed', on ? 'true' : 'false');
    this.el.vizSelect.classList.toggle('lite-active', on);
    this.el.liteBadge.hidden = !on;

    if (on) {
      this._litePrev = {
        targetFps: this.settings.get('targetFps'),
        fftSize: this.audio.fftSize,
        glowIntensity: this.settings.get('glowIntensity'),
        dprCap: this.engine.dprCap,
      };

      // Render loop: cap frame rate (fewer draws/sec = less CPU+GPU)
      this.settings.set('targetFps', 30);
      this.el.selTargetFps.value = '30';

      // Analysis: a smaller FFT is noticeably cheaper per frame
      this.audio.setFftSize(1024);
      this.el.selFftSize.value = '1024';
      this.el.vFftSize.textContent = '1024';

      // Glow (shadowBlur) is one of the more GPU-expensive canvas ops used
      // throughout the modes — zero it out while lite
      this.settings.set('glowIntensity', 0);
      this.el.rngGlow.value = 0;
      this.el.vGlow.textContent = 0;

      // Canvas resolution: this is the big one — a real pixel-count cut,
      // especially on high-DPR displays
      this.engine.setDprCap(1);

      if (!LITE_MODES.includes(this.engine.currentModeKey)) this._setMode('spectrum');
    } else if (this._litePrev) {
      const prev = this._litePrev;
      this.settings.set('targetFps', prev.targetFps);
      this.el.selTargetFps.value = String(prev.targetFps);

      this.audio.setFftSize(prev.fftSize);
      this.el.selFftSize.value = String(prev.fftSize);
      this.el.vFftSize.textContent = prev.fftSize;

      this.settings.set('glowIntensity', prev.glowIntensity);
      this.el.rngGlow.value = prev.glowIntensity;
      this.el.vGlow.textContent = prev.glowIntensity;

      this.engine.setDprCap(prev.dprCap);
      this._litePrev = null;
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
        case 'z':
          this._setLiteMode(!this.liteMode);
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
        case 'c': this.engine.modes.meterbank2.clearClip(); break; // clear Meter Bank 2's CLIP latch
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