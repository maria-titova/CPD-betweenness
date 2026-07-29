# CPD Betweenness

This repository isolates the betweenness results from `Coalition-Proof Disclosure`.

- `tex/v5.tex` contains the betweenness subsection from the paper’s `v5.tex`, its proofs, and the definitions and results on which those proofs depend.
- `lean/` contains the Lean proofs corresponding to the results in that subsection and the transitive closure of their local imports.

Source snapshots:

- TeX: `overleaf-CPD` commit `a53543a`
- Lean: `lean-CPD-v3` commit `95b9605`

Build the paper from `tex/` with `latexmk -pdf -interaction=nonstopmode v5.tex`.

The Lean project uses the toolchain and Mathlib revision recorded in `lean/lean-toolchain`, `lean/lakefile.toml`, and `lean/lake-manifest.json`.
