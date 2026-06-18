# Smooth Vocal & Instrumental Isolation Ensemble for Google Colab
# ==============================================================
# How to use if you do not know Python setup:
# IMPORTANT: Do not upload this .py file with Colab's Upload notebook button.
# That button expects a .ipynb JSON notebook and will show an
# "Unexpected token '#'" error for normal Python files.
#
# Easiest beginner path:
# 1. Use vocal_instrumental_isolation_colab.ipynb in Google Colab.
# 2. In Colab, click File -> Upload notebook, then choose the .ipynb file.
# 3. Click Runtime -> Change runtime type -> GPU -> Save.
# 4. Run each cell from top to bottom with the play button.
# 5. When the upload button appears, choose your audio file.
# 6. Download smooth_ensemble_vocals.wav and
#    smooth_ensemble_instrumental.wav at the end.
#
# This .py file is only a readable source-code copy for people who prefer
# normal Python text.

# %% [markdown]
# # Smooth Vocal & Instrumental Isolation Ensemble
#
# This Colab script separates an audio file into **vocals** and
# **instrumental** stems by combining multiple strong open-source models.
#
# You do **not** need local Python setup. Google Colab runs this in your
# browser. Use a GPU runtime for better speed.

# %%
# Install dependencies. This can take a few minutes on the first run.
import sys
import subprocess

subprocess.run(['apt-get', '-qq', 'update'], check=True)
subprocess.run(['apt-get', '-qq', 'install', '-y', 'ffmpeg'], check=True)
subprocess.run(
    [
        sys.executable,
        '-m',
        'pip',
        '-q',
        'install',
        '-U',
        'demucs',
        'soundfile',
        'librosa',
        'pyloudnorm',
        'pedalboard',
        'ipywidgets',
    ],
    check=True,
)

# %%
# Imports and setup.
import shutil
import subprocess
from pathlib import Path
from typing import Iterable

import librosa
import numpy as np
import pyloudnorm as pyln
import soundfile as sf
from google.colab import files
from IPython.display import Audio, display
from pedalboard import HighpassFilter, LowpassFilter, Pedalboard

WORK_DIR = Path('/content/isolation_workspace')
INPUT_DIR = WORK_DIR / 'input'
OUTPUT_DIR = WORK_DIR / 'output'
SEPARATED_DIR = WORK_DIR / 'separated'

for folder in (INPUT_DIR, OUTPUT_DIR, SEPARATED_DIR):
    folder.mkdir(parents=True, exist_ok=True)

SAMPLE_RATE = 44100

# Remove a model from this list if you want faster processing.
MODEL_NAMES = [
    'htdemucs_ft',  # high-quality fine-tuned Demucs model
    'htdemucs_6s',  # alternate 6-source model, useful vocal estimate
    'mdx_extra',    # MDX-style Demucs model for ensemble diversity
]

print('Workspace:', WORK_DIR)

# %%
# Upload your song/audio file.
uploaded = files.upload()
if not uploaded:
    raise RuntimeError('Upload one audio file first.')

input_name = next(iter(uploaded))
raw_input_path = INPUT_DIR / input_name
shutil.move(input_name, raw_input_path)

# Convert everything to a clean 44.1 kHz stereo WAV so each model receives
# identical input. WAV, MP3, FLAC, M4A, and many other formats should work.
input_wav = INPUT_DIR / 'source_44100_stereo.wav'
subprocess.run(
    [
        'ffmpeg',
        '-y',
        '-i',
        str(raw_input_path),
        '-ar',
        str(SAMPLE_RATE),
        '-ac',
        '2',
        '-c:a',
        'pcm_s16le',
        str(input_wav),
    ],
    check=True,
)

print('Prepared input:', input_wav)
display(Audio(str(input_wav)))

# %%
# Run multiple separation models.
def run_demucs(model_name: str, audio_path: Path) -> Path:
    model_out = SEPARATED_DIR / model_name
    model_out.mkdir(parents=True, exist_ok=True)

    command = [
        'python',
        '-m',
        'demucs.separate',
        '--two-stems',
        'vocals',
        '-n',
        model_name,
        '-o',
        str(model_out),
        '--filename',
        '{track}/{stem}.{ext}',
        str(audio_path),
    ]

    print('Running:', ' '.join(command))
    subprocess.run(command, check=True)
    return model_out / audio_path.stem


model_result_dirs = {}
for model in MODEL_NAMES:
    try:
        model_result_dirs[model] = run_demucs(model, input_wav)
    except subprocess.CalledProcessError as error:
        print(f'WARNING: {model} failed and will be skipped: {error}')

if not model_result_dirs:
    raise RuntimeError('No separation model completed successfully.')

print('Completed models:', list(model_result_dirs))

# %%
# Ensemble helper functions.
def read_audio(path: Path, sr: int = SAMPLE_RATE) -> np.ndarray:
    audio, _ = librosa.load(path, sr=sr, mono=False)
    if audio.ndim == 1:
        audio = np.vstack([audio, audio])
    return audio.T.astype(np.float32)


def match_length(audio: np.ndarray, length: int) -> np.ndarray:
    if len(audio) > length:
        return audio[:length]
    if len(audio) < length:
        return np.pad(audio, ((0, length - len(audio)), (0, 0)))
    return audio


def rms(audio: np.ndarray) -> float:
    return float(np.sqrt(np.mean(np.square(audio)) + 1e-12))


def loudness_normalize_to(
    reference: np.ndarray,
    candidate: np.ndarray,
    sr: int = SAMPLE_RATE,
) -> np.ndarray:
    # Match RMS first; LUFS can be unstable for near-silent stems.
    ref_rms = rms(reference)
    cand_rms = rms(candidate)
    if cand_rms < 1e-7:
        return candidate

    scaled = candidate * (ref_rms / cand_rms)

    try:
        meter = pyln.Meter(sr)
        ref_lufs = meter.integrated_loudness(reference)
        cand_lufs = meter.integrated_loudness(scaled)
        if np.isfinite(ref_lufs) and np.isfinite(cand_lufs):
            gain = 10 ** ((ref_lufs - cand_lufs) / 20)
            scaled = scaled * np.clip(gain, 0.5, 2.0)
    except Exception as error:
        print('LUFS match skipped:', error)

    return scaled.astype(np.float32)


def soft_clip(audio: np.ndarray, drive: float = 1.05) -> np.ndarray:
    return np.tanh(audio * drive) / np.tanh(drive)


def smooth_stem(audio: np.ndarray, sr: int = SAMPLE_RATE) -> np.ndarray:
    # Gentle cleanup: remove sub-rumble and very high model fizz without
    # making the result sound dull.
    board = Pedalboard(
        [
            HighpassFilter(cutoff_frequency_hz=25),
            LowpassFilter(cutoff_frequency_hz=19500),
        ]
    )
    processed = board(audio.astype(np.float32), sr)
    return np.asarray(processed, dtype=np.float32)


def weighted_average(
    stems: Iterable[np.ndarray],
    weights: Iterable[float],
) -> np.ndarray:
    stems = list(stems)
    weights = np.asarray(list(weights), dtype=np.float32)
    weights = weights / weights.sum()
    stacked = np.stack(stems, axis=0)
    return np.tensordot(weights, stacked, axes=(0, 0)).astype(np.float32)

# %%
# Build the smooth ensemble result.
source_audio = read_audio(input_wav)
target_len = len(source_audio)

vocal_stems = []
instrumental_stems = []
used_models = []

for model, result_dir in model_result_dirs.items():
    vocal_path = result_dir / 'vocals.wav'
    no_vocal_path = result_dir / 'no_vocals.wav'

    if not vocal_path.exists():
        print(f'Skipping {model}: missing vocals.wav')
        continue

    vocals = match_length(read_audio(vocal_path), target_len)

    # Prefer each model's no_vocals stem when present; otherwise use a residual.
    if no_vocal_path.exists():
        instrumental = match_length(read_audio(no_vocal_path), target_len)
    else:
        instrumental = source_audio - vocals

    vocal_stems.append(vocals)
    instrumental_stems.append(instrumental)
    used_models.append(model)

if not vocal_stems:
    raise RuntimeError('No usable vocal stems were produced.')

# Weight the most natural general-purpose model highest, while keeping the
# other models for detail. You can tweak these values.
base_weights = {
    'htdemucs_ft': 0.50,
    'htdemucs_6s': 0.25,
    'mdx_extra': 0.25,
}
weights = [base_weights.get(model, 1.0) for model in used_models]

reference_vocal = vocal_stems[0]
matched_vocals = [reference_vocal]
matched_vocals += [
    loudness_normalize_to(reference_vocal, stem) for stem in vocal_stems[1:]
]

ensemble_vocals = weighted_average(matched_vocals, weights)
ensemble_vocals = smooth_stem(ensemble_vocals)

# Reconstruct instrumental as source minus final vocals for phase-safe summing,
# then blend it with the model instrumental stems for smoother tone.
residual_instrumental = source_audio - ensemble_vocals
matched_instrumentals = [
    loudness_normalize_to(residual_instrumental, stem)
    for stem in instrumental_stems
]
model_instrumental_blend = weighted_average(matched_instrumentals, weights)
ensemble_instrumental = 0.70 * residual_instrumental + 0.30 * model_instrumental_blend
ensemble_instrumental = smooth_stem(ensemble_instrumental)

# Prevent clipping while preserving the source level relationship.
peak = max(
    np.max(np.abs(ensemble_vocals)),
    np.max(np.abs(ensemble_instrumental)),
    1e-6,
)
if peak > 0.98:
    gain = 0.98 / peak
    ensemble_vocals *= gain
    ensemble_instrumental *= gain

ensemble_vocals = soft_clip(ensemble_vocals).astype(np.float32)
ensemble_instrumental = soft_clip(ensemble_instrumental).astype(np.float32)

vocals_out = OUTPUT_DIR / 'smooth_ensemble_vocals.wav'
instrumental_out = OUTPUT_DIR / 'smooth_ensemble_instrumental.wav'

sf.write(vocals_out, ensemble_vocals, SAMPLE_RATE, subtype='PCM_24')
sf.write(instrumental_out, ensemble_instrumental, SAMPLE_RATE, subtype='PCM_24')

print('Used models:', used_models)
print('Saved:', vocals_out)
print('Saved:', instrumental_out)

# %%
# Preview and download the results.
print('Vocals preview')
display(Audio(str(vocals_out)))

print('Instrumental preview')
display(Audio(str(instrumental_out)))

files.download(str(vocals_out))
files.download(str(instrumental_out))

# %% [markdown]
# ## Tuning notes
#
# - If vocals sound too wet or phasey, reduce `mdx_extra` weight and increase
#   `htdemucs_ft`.
# - If the instrumental has too much vocal bleed, increase the residual amount
#   in `ensemble_instrumental` from `0.70` to something like `0.85`.
# - If the output sounds dull, raise the low-pass cutoff in `smooth_stem` from
#   `19500` to `20500`.
# - For faster runs, remove one model from `MODEL_NAMES`; for smoother results,
#   keep all three.
