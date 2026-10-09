# Interactive geometry visualization

This is a self-contained static package of the saved geometry atlas, together with the six illustrated explanations from the **ver503 paper**. It includes 42 selectable numerical models: spatial seeds, the actual band and its local views, alternative identity-return bands, asymptotic trajectories, bending sign patches, and the successive completion pieces.

## Run it

Clone or download this repository. From its **root**, run:

```sh
python -m http.server 8000 --bind 127.0.0.1
```

Open **http://127.0.0.1:8000/visualization/index.html**. On systems where Python is named `python3`, substitute that name. Stop the server with Ctrl+C. Serve the repository root so links to the adjacent `paper` and `lean` directories work. Any ordinary static HTTP server also works.

No package installation, browser computation service, login or external asset host is required. Geometry, Plotly, equation styles and fonts are local. The models load on demand; the largest models may take a few seconds and require a browser with WebGL enabled.

## Suggested route

| What to explore | Page |
|---|---|
| Spatial seed, center curve and normal image | [seed.html](seed.html#models) |
| Actual band, local microscope and wider patches | [width.html](width.html#models) |
| Three-, four- and five-lobed alternatives | [alternative-bands.html](alternative-bands.html#models) |
| Closed asymptotic trajectories and return flow | [return.html](return.html#models), [alternative-return.html](alternative-return.html#models) |
| Positive exits and visible connectors | [exits.html](exits.html#models), [connector.html](connector.html#models) |
| Legendre duality, outer/inner filling and neck | [duality.html](duality.html#models), [filling.html](filling.html#models), [inner.html](inner.html#models), [neck.html](neck.html#models) |
| Reflection, closure, normals and marking | [annulus.html](annulus.html#models), [tightness.html](tightness.html#models), [marking.html](marking.html#models) |
| Opposite supported bending signs | [pair.html](pair.html#models) |
| The bending/asymptotic-leaf mechanism and Cantor-family sketch | [illustrations.html](illustrations.html) |

The original requested alternative-band view is available at **http://127.0.0.1:8000/visualization/alternative-bands.html#models**. A browser-friendly [guide](guide.html) also explains the controls and route.

Drag to rotate, scroll to zoom and shift-drag to pan. The buttons switch models; Reset view restores the camera; Full screen enlarges the viewer; Save picture exports a PNG. On applicable models, Show belt mesh reveals sampled rulings and the circuit slider reveals saved trajectories. Left/right arrow keys move between construction chapters.

## Interpret the figures correctly

The meshes are **numerical illustrations**, not formal proof certificates. The saved twelve-cell example lies below the manuscript's sufficient analytic range. Its piecewise completion still needs internal relative smoothing. The broad alternative bands illustrate the return mechanism and may self-intersect; they are separate from the completed torus construction.

Physical units are equal in all three directions within a model. Local microscopes use rigid rotation and uniform magnification; their captions specify the scale. Do not infer a global feature's size from the local microscope or from the enlarged neck view. The ver503 gallery contains its own separately captioned figure data and explanatory sketches; its local scale need not equal an older atlas model's scale.

The [current paper](../paper/README.md) is ver503. This saved numerical atlas retains ver500 chapter/source coordinates; [source.html](source.html) displays that exact pinned reference. [coverage.html](coverage.html) is a manuscript passage map, not the current Lean proof-coverage report. The actual latest formalization status is in [../lean/README.md](../lean/README.md), and the final Lean existence theorem is still pending. The Cantor-family illustration is a paper sketch; that extension is deferred in Lean.

## Package contents

- HTML chapters and the on-page explanations.
- `assets/catalog.js`, the viewer and only the current model geometry assets.
- Local Plotly, KaTeX styles/fonts and third-party notices.
- Linked numerical audit data and still images that the chapters use.
- Six ver503 figure previews, linked to their vector PDFs under `paper/figures`.

Raw experiment archives, numerical work arrays, duplicate manuscripts, obsolete hashed meshes, generator caches and old site-validation reports are excluded. [manifest.json](manifest.json) records the source reference and packaged resource hashes. Geometry vertices are unchanged from the saved atlas; publication edits fix navigation, add usage/proof-status explanations and link the current paper.

This is a static visualization package. Editing an HTML explanation or camera does not rerun the numerical construction; the raw computation pipeline is not included.

For bundled library attribution, see [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
