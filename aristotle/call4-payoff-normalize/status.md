# call4-payoff-normalize

- Lane:        B (`ThinBExistence.lean`)
- Targets:     `thinB_coalition_payoff_set`, `exists_upperNormalizedPBE`,
               `thinB_upperNormalizedPBE_subgame`
               (all in `lean/CPDLinear/ThinBExistence.lean`)
- TeX:         `lem:thinB-value-set`, `prop:thinB-upper-pbe`
- Owns:        `ThinBExistence.lean`
- Project ID:  `439ebba3-2fa0-4dfb-b70c-357ebc44a399`
- Task ID:     `0e970704-396d-46dd-abc9-5777fdad8572`
- Status:      **PARTIAL** — returned `COMPLETE_WITH_ERRORS` after ~3h10m, 2 of 3 proved
- Retries:     0
- Merged:      yes (the two proved targets)
- Result:      ✅ `thinB_coalition_payoff_set` — proved by reindexing the finite evidence
                  set with `Fin n`, applying `HasCommonValueIntersections`, and
                  identifying the intersection with `Coalition.repayablePayoffs`.
               ✅ `thinB_upperNormalizedPBE_subgame` — correct wrapper body via
                  `IsThinB.hasCommonValueIntersections` + `of_subgame` +
                  `exists_upperNormalizedPBE`.
               ⛔ `exists_upperNormalizedPBE` — still `sorry`. Aristotle's own account:
                  the paper's normalization requires a substantial formal construction
                  that repeatedly changes or merges adjacent partition cells while
                  preserving every dependent strategy and residual-game field, and it
                  could not complete that in this call.
               This is exactly the sacrifice the prompt pre-authorized ("if you must
               leave something `sorry`, leave `exists_upperNormalizedPBE`, not
               `thinB_coalition_payoff_set`"), so it counts as an anticipated partial,
               not a gate failure — the merge was kept rather than reverted.
- Ownership:   bundle predated calls 1 and 8; `ThinB.lean`, `BetweennessOrderUSC.lean`,
               `BetweennessRank.lean`, `BetweennessOrder.lean` all verified byte-identical
               to `71fccec` (untouched) and **not** copied back. Only
               `ThinBExistence.lean` merged.
- Fidelity:    +106 / −2, and the only removed lines were two `sorry`s. Clean.
- Verified:    `lake build` exit 0, 8056 jobs. Sorry 12 → 10, delta exactly 2 (matching
               2 of 3 targets). `two_B_existence` untouched, axioms unchanged.
- Axioms:      `thinB_coalition_payoff_set` = `{propext, Classical.choice, Quot.sound}` —
               fully clean (it takes `hcommon` as a hypothesis, so it does not inherit
               the still-`sorry` `IsThinB.hasCommonValueIntersections`).
               `thinB_upperNormalizedPBE_subgame` carries `sorryAx` via the unproved
               `exists_upperNormalizedPBE`.
- Badge:       `lem:thinB-value-set` flipped `\leanpending` → `\leanproved`.
               `prop:thinB-upper-pbe` stays `\leanpending`: it names
               `thinB_upperNormalizedPBE_subgame`, which is `sorryAx`-tainted.
- FOLLOW-UP:   **queued lane-B retry** — resume THIS project with
               `aristotle ask 439ebba3-2fa0-4dfb-b70c-357ebc44a399 "<finish
               exists_upperNormalizedPBE>"` (never cancel/resubmit). Scheduled after
               call5 and call6, since lane B is serial and the remaining fresh targets
               have clearer templates; the project stays IDLE and resumable meanwhile.
