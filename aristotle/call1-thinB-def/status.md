# call1-thinB-def

- Lane:        A (`ThinB.lean`)
- Targets:     `CPDLinear.IsBetweenness.bddOn_simplex`, `CPDLinear.thinB_eq_Icc`,
               `CPDLinear.thinB_A4`  (all in `lean/CPDLinear/ThinB.lean`)
- TeX:         `dfn:thinB`, `lem:thinB-A4`; appendix "Proof of \cref{lem:thinB-A4}"
- Owns:        `ThinB.lean`
- Base commit: `71fccec`  (19 `sorry`, `lake build` exit 0, 8056 jobs)
- Project ID:  `4cc36581-d439-4805-979f-926b993b47ae`
- Task ID:     `6554274d-0165-4c2b-a0cc-e3dfdcf80898`
- Status:      **COMPLETE** (submitted and returned 2026-07-29, ~1h45m)
- Retries:     0
- Merged:      yes
- Result:      all three proved. `ThinB.lean` 147 → 1134 lines; +987 / −3, and the only
               removed lines were the three `sorry`s — no statement, definition or
               docstring altered. Fidelity gate: clean.
- Ownership:   the solution bundle predated call3, so its `ThinBExistence.lean` was the
               pre-call3 9-`sorry` version. Verified byte-identical to `71fccec` (i.e.
               Aristotle did not touch it) and **not** copied back; only `ThinB.lean`
               was merged. This is the lane discipline working as designed.
- Verified:    `lake build` exit 0, 8056 jobs. Sorry count 16 → 13 (`ThinB` 6 → 3),
               delta exactly 3. `two_B_existence` untouched, still sorry-free.
- Axioms:      `bddOn_simplex`, `thinB_eq_Icc`, `thinB_A4` all
               `{propext, Classical.choice, Quot.sound}` — no `sorryAx`, no
               `CPDLinear.kakutani`. `ThinB.lean` remains axiom-free as required.
- Badge:       `lem:thinB-A4` flipped `\leanpending` → `\leanproved`.
               `dfn:thinB` NOT flipped — it names only definitions (`clusterValues`,
               `thinB`, `IsThinB`), which carry no proof obligation, so whether it
               counts as "Lean proved" is a convention call for the user.
