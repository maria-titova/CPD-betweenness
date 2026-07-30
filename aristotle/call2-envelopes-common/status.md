# call2-envelopes-common

- Lane:        A (`ThinB.lean`)
- Targets:     `CPDLinear.thinBUpper_isBetweenness`, `CPDLinear.thinBLower_isBetweenness`,
               `CPDLinear.thinB_common_value`  (all in `lean/CPDLinear/ThinB.lean`)
- TeX:         `lem:thinB-envelope-B`, `prop:thinB-common-value`
- Owns:        `ThinB.lean`
- Dispatch:    lane A free, i.e. after call1 merges
- Project ID:  `08528a35-a59c-4d24-93b5-b41287f76413`
- Task ID:     `7bb9a6b8-e87d-42f6-9bb3-143e0f8bb158`
- Status:      **PARTIAL** — returned `COMPLETE_WITH_ERRORS` 2026-07-30, 1 of 3 proved
- Retries:     0
- Merged:      yes (the one proved target)
- Expected:    completes `ThinB.lean` (sorry −3, file reaches 0). Axioms of all `ThinB`
               declarations must stay `propext, Classical.choice, Quot.sound`.

## Return (2026-07-30)
- ✅ `thinBLower_isBetweenness` — proved by negation symmetry (`u := -v`), citing
  `thinBUpper_isBetweenness` (still `sorry`, so the decl is sorryAx-tainted until it lands).
- ⛔ `thinBUpper_isBetweenness`, ⛔ `thinB_common_value` — Ari's own report: the
  relative-interior/closure arguments "did not converge to checked proofs".
- Merge: proof-body-only diff (+154 lines, −1 sorry), no new top-level decls, statements
  byte-identical. `lake build` exit 0. Retry via `aristotle ask` planned (workspace has
  the thinBLower proof already).
