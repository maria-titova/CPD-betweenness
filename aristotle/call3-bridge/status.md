# call3-bridge

- Lane:        B (`ThinBExistence.lean`)
- Targets:     `IsThinB.betweenness`, `IsThinB.hasCommonValueIntersections`,
               `HasCommonValueIntersections.of_subgame`
               (all in `lean/CPDLinear/ThinBExistence.lean`)
- TeX:         `prop:thinB-common-value` (game-level transport); no separate appendix proof
- Owns:        `ThinBExistence.lean`
- Dispatch:    immediately — lane B is independent of lanes A and C
- Project ID:  `09839860-53f3-4609-843e-8c755fef37d4`
- Task ID:     `ad9e47b2-65d8-4f46-a8d1-6256d07844da`
- Status:      **COMPLETE** (submitted and returned 2026-07-29, ~19 min)
- Retries:     0
- Merged:      yes
- Result:      all three proved. Diff touched exactly one file (`ThinBExistence.lean`,
               owned by this lane) and removed exactly three lines, all `sorry` —
               no statement, definition or docstring altered. Fidelity gate: clean.
- Verified:    `lake build` exit 0, 8056 jobs. Sorry count 19 → 16 (`ThinBExistence`
               9 → 6), delta exactly 3. `two_B_existence` untouched, still sorry-free
               with axioms `{propext, kakutani, Classical.choice, Quot.sound}`.
- Axioms:      `of_subgame` = `{propext, Classical.choice, Quot.sound}` — fully clean.
               `IsThinB.betweenness` and `IsThinB.hasCommonValueIntersections` additionally
               show **`sorryAx`**, because they legitimately cite `thinB_eq_Icc` /
               `thinBUpper_isBetweenness` / `thinB_common_value`, which lane A is still
               proving (calls 1 and 2). This is the intended consequence of the
               cite-a-sorried-lemma design and clears automatically once lane A lands.
               Re-check axioms after call2 merges.
- Badge:       none flipped — no badge in `tex/v5.tex` names these three declarations
               (`dfn:thinB` names only `clusterValues`, `thinB`, `IsThinB`, all defs).
