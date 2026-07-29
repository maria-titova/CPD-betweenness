# call4-payoff-normalize

- Lane:        B (`ThinBExistence.lean`)
- Targets:     `thinB_coalition_payoff_set`, `exists_upperNormalizedPBE`,
               `thinB_upperNormalizedPBE_subgame`
               (all in `lean/CPDLinear/ThinBExistence.lean`)
- TeX:         `lem:thinB-value-set`, `prop:thinB-upper-pbe`
- Owns:        `ThinBExistence.lean`
- Dispatch:    lane B free, i.e. after call3 merges
- Project ID:  `439ebba3-2fa0-4dfb-b70c-357ebc44a399`
- Task ID:     `0e970704-396d-46dd-abc9-5777fdad8572`
- Status:      **IN_PROGRESS** (submitted 2026-07-29, bundle includes call3 proofs)
- Retries:     0
- Merged:      no
- Expected:    sorry −3. `thinB_coalition_payoff_set` is the critical one — calls 5 and 6
               both consume it. Partial credit acceptable on `exists_upperNormalizedPBE`.
               May pick up `CPDLinear.kakutani` through `exists_PBE`; that is expected and
               correct for this declaration.
