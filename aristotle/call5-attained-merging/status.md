# call5-attained-merging

- Lane:        B (`ThinBExistence.lean`)
- Targets:     `thinB_attained`, `thinB_merging`
               (both in `lean/CPDLinear/ThinBExistence.lean`)
- TeX:         `lem:thinB-attained`, `lem:thinB-merging`
- Owns:        `ThinBExistence.lean`
- Dispatch:    lane B free, i.e. after call4 merges
- Project ID:  `c532126f-d02a-411f-bc97-8bcc577485aa`
- Task ID:     `79478d6a-86b3-4e81-a1e0-1dff7c68f653`
- Status:      **PARTIAL** — returned `COMPLETE_WITH_ERRORS` 2026-07-30, 1 of 2 proved
- Retries:     0
- Merged:      yes (the one proved target)
- Expected:    sorry −2. Shape-identical to the proved `btw_attained` / `btw_merging` in
               `BetweennessCore.lean`; the prompt directs Aristotle to mirror them.
               `thinB_merging` genuinely depends on `thinB_attained`.

## Return (2026-07-30)
- ✅ `thinB_merging` — proved via `thinB_coalition_payoff_set` + betweenness of the
  conditional-prior mixture + `thinB_attained` for the reverse bound (sorryAx-tainted
  until `thinB_attained` lands).
- ⛔ `thinB_attained` — **diagnosed blocker**: the auxiliary-game realization machinery
  (`btwcAux` and the ~30 `btwc_*` lemmas in `BetweennessCore.lean`) is `private`, so it
  cannot be cited from `ThinBExistence.lean` and would have to be reproduced wholesale.
  Fix: de-privatize the machinery locally, then a fresh submit (call5b) — `ask` cannot
  see repo changes.
- Merge: proof-body-only diff (+155 lines, −1 sorry), statements byte-identical.
  `lake build` exit 0.
