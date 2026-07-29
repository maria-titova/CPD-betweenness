# call2-envelopes-common

- Lane:        A (`ThinB.lean`)
- Targets:     `CPDLinear.thinBUpper_isBetweenness`, `CPDLinear.thinBLower_isBetweenness`,
               `CPDLinear.thinB_common_value`  (all in `lean/CPDLinear/ThinB.lean`)
- TeX:         `lem:thinB-envelope-B`, `prop:thinB-common-value`
- Owns:        `ThinB.lean`
- Dispatch:    lane A free, i.e. after call1 merges
- Project ID:  `08528a35-a59c-4d24-93b5-b41287f76413`
- Task ID:     `7bb9a6b8-e87d-42f6-9bb3-143e0f8bb158`
- Status:      **IN_PROGRESS** (submitted 2026-07-29; bundle carries call1 + call3 proofs)
- Retries:     0
- Merged:      no
- Expected:    completes `ThinB.lean` (sorry −3, file reaches 0). Axioms of all `ThinB`
               declarations must stay `propext, Classical.choice, Quot.sound`.
