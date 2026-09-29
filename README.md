# SIGNAL-> Music Visualizer 

A local, no-backend, no-framework audio visualizer that captures **browser tab audio**
and renders it in real time across eleven visualization modes, plus an Auto mode
that picks (and tunes) one for you. Built with plain HTML, CSS, and vanilla
JavaScript — no build step, no dependencies.

Everything happens on-device. Audio is analyzed in the browser via the Web
Audio API and never leaves the machine. Window

---

## How it works

1. Click **Start capture**.
2. The browser's native tab picker appears — choose a tab.
3. Check **"Share tab audio"** in that dialog.
4. The visualizer connects instantly and starts rendering.
5. Click **Stop** (square icon) to disconnect everything cleanly.

The captured audio is analyzed but **not** played back out of your speakers —
since the source tab is already producing sound, looping it back through
would create an echo. SIGNAL only listens; the original tab keeps playing
normally on its own.

---

## Visualization modes

| # | Mode | Description |
|---|------|--------------|
| 1 | **Spectrum Bars** | Classic log-scaled FFT bars with rounded tops, peak-hold indicators, adaptive smoothing, and optional mirror mode. |
| 2 | **Waveform Mode 1** | Smooth bezier oscilloscope trace of the raw time-domain signal, with glow and adjustable thickness. |
| 3 | **Waveform Mode 2** | Same oscilloscope trace, resampled to fixed-position points that ease toward the signal instead of jittering sample-to-sample. |
| 4 | **Circular Spectrum** | Radial FFT bars rotating around a bass-reactive center pulse, with a particle ring driven by treble. |
| 5 | **Line Graph Mode 1** | A sweeping bass/mid/treble cursor trace. Everything the sweep has already passed (to the left) stays visible the whole way back to the start of the pass; nothing to the right of the cursor is drawn, since those points haven't been swept yet this lap — so the trail is as long as the sweep itself, with no stale line left over from the previous pass. |
| 6 | **Line Graph Mode 2** | Fixed-position traces reshaping live in place. |
| 7 | **Particle Visualizer** | Drifting particle field — bass controls particle size, treble controls velocity, mid controls color blend. |
| 8 | **Orchestra Mode 1** | Seven-band meter bank where each row's filled waveform scrolls — a continuous, seismograph-style feed of recent energy. |
| 9 | **Orchestra Mode 2** | Same seven-band layout, sampled at fixed x-positions so each silhouette reshapes live in place, now with extra breathing room — wider meter column, chunkier bars, taller row gaps. Each row extends its sampling range into its neighboring bands (the top row reaches all the way to Nyquist) and overlays two extra lines above/below the live silhouette: a dashed envelope tracing recent peaks and a dotted line tracing recent troughs, so the full recent range of each band is visible at a glance. |
| M | **Meter Bank** | A clean, full-width bar-meter panel — one row per band (Sub Bass through Brilliance), each with a smoothed fill, a peak-hold tick, and a live dB/% readout, with no waveform column competing for space. |
| V | **Vitals Graph** | A focused 4-row instrument panel — just the headline numbers: overall Volume, dominant Frequency (log-scaled across the audible range), Bass, and Sub Bass. Swept the same way as Line Graph Mode 1. |
| 0 | **Auto Mode** | Watches the live band energy, beat detection, and BPM and automatically switches between the modes above to suit what's playing (settles in rather than flickering), while also nudging the analyser's FFT size — larger for bass-heavy/tonal material, smaller for treble-heavy/percussive material. |

Switch modes anytime with the toolbar (the mode selector wraps to fit every
button, however many there are, so nothing is ever hidden or clipped) or the
number keys **1–9**, plus **M** for Meter Bank, **V** for Vitals, and **0** for Auto.

---

## Controls

**Toolbar:** Play/Pause, Stop, mode selector, Sensitivity / Gain / Smoothing
sliders — each paired with a numeric field so you can type an exact value
instead of dragging; the two stay in sync either way — theme picker,
Screenshot, Record.

**Settings panel** (gear icon): FFT size, bar count, peak-hold time, mirror
mode, line width, a "more lines" toggle for the two Line Graph modes (classic
3-band bass/mid/treble vs. the full 7-band breakdown, Sub Bass through
Brilliance), circular radius & rotation speed, particle count, glow
intensity, background blur, wave thickness, and a **Performance** section
with a target-FPS cap (Unlimited, 144, 120, 90, 60, 30 — throttles the
render loop without touching audio analysis) and an audio-latency mode
(Interactive / Balanced / Playback, matching the Web Audio `latencyHint`;
applies the next time capture is started).

**Fullscreen** (`F` or the fullscreen button) is visuals-only: the top bar,
toolbar, and mode label all hide, leaving just the canvas edge-to-edge.
Every keyboard shortcut still works while hidden — `Esc` (or `F` again)
exits back to the normal view.

**Keyboard shortcuts:**

| Key | Action |
|-----|--------|
| `Space` | Pause / Resume |
| `F` | Fullscreen |
| `1`–`9` | Switch visualization mode |
| `M` | Meter Bank mode |
| `V` | Vitals Graph mode |
| `0` | Auto mode |
| `S` | Screenshot (PNG) |
| `R` | Start / stop recording (WebM) |
| `Esc` | Exit fullscreen |

---

## Themes

Cyber Purple · Neon Blue · Synthwave · Aurora · Matrix Green · Fire · Ocean ·
Sunset · Monochrome · **Phosphor** (default — an oscilloscope-green/amber
instrument-panel look). Each theme is a set of CSS custom properties; switching
is instant and re-tints both the UI chrome and the canvas drawing (canvas reads
live accent colors from computed CSS each frame).

A separate light/dark toggle sits next to the theme picker.

---

## Performance notes

- All per-frame buffers (`Uint8Array`/`Float32Array` for FFT, waveform, and
  per-mode smoothing/peak state) are allocated once and reused — no per-frame
  allocation in the hot path.
- Canvas size tracks the container via `ResizeObserver` and is capped at
  2.5x device pixel ratio to avoid runaway buffer sizes on high-DPI displays.
- Rendering pauses automatically when the tab is hidden (`visibilitychange`)
  and resumes cleanly when it becomes visible again.
- FPS is measured with a rolling accumulator and shown live in the top bar.

---

## Project structure

```
index.html       Markup: top bar, canvas stage, toolbar, settings panel
style.css        Theming (CSS variables), glassmorphism chrome, responsive layout
script.js        AudioEngine, ThemeManager, SettingsManager, AnimationEngine,
                 11 visualizer classes + AutoViz, UIController
assets/
  icons/         (reserved — current icon set is inline SVG, no files needed)
  themes/        (reserved — themes are pure CSS variables, no files needed)
README.md
```

### Code organization (`script.js`)

- `AudioEngine` — `getDisplayMedia` capture, Web Audio graph, FFT/waveform
  buffers, band-energy analysis, beat/BPM detection, silence detection.
- `ThemeManager` — theme registry and live accent-color reads for canvas.
- `SettingsManager` — single source of truth for tunable parameters.
- `Visualizer` (base) + `SpectrumBars`, `WaveformViz1`/`WaveformViz2`,
  `CircularVisualizer`, `LineGraphV1`/`LineGraphV2`, `ParticleViz`,
  `VitalsGraph` — one class per mode. `OrchestraBase` extends `Visualizer`
  with the icon/label/meter drawing shared by `OrchestraModeV1` (scrolling
  history), `OrchestraModeV2` (fixed-position, static layout, triple-line
  rows — live silhouette plus dashed peak envelope and dotted trough line —
  with an extended sampling range and extra room), and `MeterBankViz` (a
  roomy, waveform-free bar-meter panel across all seven bands).
- `AutoViz` — also a `Visualizer`, but instead of drawing directly it reads
  live band energy/beat/BPM to pick which of the modes above to delegate to,
  and periodically nudges the analyser's FFT size to match the material.
- `AnimationEngine` — canvas sizing, the `requestAnimationFrame` loop, FPS
  tracking, mode switching, hidden-tab pausing.
- `UIController` — binds all of the above to the DOM, handles start/stop/pause,
  screenshots, recording, and keyboard shortcuts.

---

## Browser support

Tab audio capture via `getDisplayMedia({ audio: true })` requires Chromium-based
browsers:

- ✅ Chrome, Edge, Opera — full support
- ⚠️ Firefox — `getDisplayMedia` video works, but tab/system **audio** capture
  support is inconsistent across versions
- ❌ Safari — no tab-audio capture support

If the API is unavailable, SIGNAL shows a clear inline error instead of
failing silently.

---

## Privacy

No backend, no analytics, no network calls. The only "network" activity is
loading the two Google Fonts referenced in `style.css` — everything else,
including all audio processing, is 100% local to the browser tab.
