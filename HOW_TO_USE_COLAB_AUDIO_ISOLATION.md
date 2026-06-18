# How to use the vocal/instrumental isolation notebook

If you saw this error:

```text
Unexpected token '#', "# Smooth V"... is not valid JSON
```

it means you uploaded the **`.py` file** using Colab's **Upload notebook** button.
That button expects a real notebook file ending in **`.ipynb`**. A normal Python
file starts with `#` comments, so Colab tries to parse it as notebook JSON and
fails immediately.

## Use this file in Colab

Upload this file:

```text
vocal_instrumental_isolation_colab.ipynb
```

Do **not** upload this file with the notebook uploader:

```text
vocal_instrumental_isolation_colab.py
```

The `.py` file is included only as a readable source-code copy for people who
want to inspect normal Python text.

## Beginner steps

1. Go to <https://colab.research.google.com/>.
2. Click **File → Upload notebook**.
3. Choose `vocal_instrumental_isolation_colab.ipynb`.
4. Click **Runtime → Change runtime type**.
5. Set **Hardware accelerator** to **GPU**, then click **Save**.
6. Run the cells from top to bottom using the play button on the left of each cell.
7. When the upload widget appears, choose your song or audio file.
8. Wait for the models to finish. The first run can take a while because Colab
   has to install packages and download model weights.
9. Download the final files:
   - `smooth_ensemble_vocals.wav`
   - `smooth_ensemble_instrumental.wav`

## Why the `.ipynb` can look weird outside Colab

A `.ipynb` file is a JSON document. If you open it in a plain text viewer, you
may see quoted lines and `\n` symbols. That is normal. Open it in Google Colab
or Jupyter to see normal notebook cells.

## Which file is for what?

| File | Use |
| --- | --- |
| `vocal_instrumental_isolation_colab.ipynb` | Upload this to Google Colab and run it. |
| `vocal_instrumental_isolation_colab.py` | Readable code copy; do not upload with Colab's notebook uploader. |
