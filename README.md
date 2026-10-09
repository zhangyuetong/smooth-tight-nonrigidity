# Smooth tight nonrigidity

| Content | Location |
|---|---|
| Current illustrated manuscript, ver503 | [paper](paper/README.md) |
| Latest integrated Lean sources and exact proof status | [lean](lean/README.md) |
| Interactive numerical geometry and illustrated construction | [visualization](visualization/README.md) |

The Lean formalization remains **incomplete**. The latest integrated audit records 1,403 modules and 17,564 declarations; the final existence theorem is pending. The numerical meshes illustrate the construction and do not certify it.

To explore the visualization, serve this repository root:

```sh
python -m http.server 8000 --bind 127.0.0.1
```

Then open **http://127.0.0.1:8000/visualization/index.html**. Detailed build and usage instructions are in each directory's README.
