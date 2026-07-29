# call1-thinB-def

- Targets:     `CPDLinear.IsBetweenness.bddOn_simplex`, `CPDLinear.thinB_eq_Icc`,
               `CPDLinear.thinB_A4`  (all in `lean/CPDLinear/ThinB.lean`)
- TeX:         `dfn:thinB`, `lem:thinB-A4`; appendix "Proof of \cref{lem:thinB-A4}"
- Base commit: `71fccec`  (19 `sorry`, `lake build` exit 0, 8056 jobs)
- Project ID:  —
- Task ID:     —
- Status:      **PREPARED — not submitted**
- Retries:     0
- Merged:      no
- Expected:    on merge, `sorry` count 19 → 16; `#print axioms CPDLinear.thinB_A4` =
               `propext, Classical.choice, Quot.sound` (no `CPDLinear.kakutani`).
