# call8-btw-order-usc

- Targets:     `CPDLinear.DisclosureGame.btw_order_usc`
               (`lean/CPDLinear/BetweennessOrderUSC.lean`)
- TeX:         `lem:btw-order` (u.s.c. form) and the appendix proof following it,
               especially Case 4 and the slice-dimension paragraph
- Base commit: `71fccec`  (19 `sorry`, `lake build` exit 0, 8056 jobs)
- Project ID:  `17d68832-269e-49a4-9335-868987d26306`
- Task ID:     `f67361d6-a8c0-402c-81e9-66db436f4f5e`
- Status:      **IN_PROGRESS** (submitted 2026-07-29)
- Retries:     0
- Merged:      no
- Notes:       Run concurrently with call1 — disjoint files. This call is an explicit
               exception to the "do not touch other files" rule: it may edit
               `BetweennessRank.lean` (generalize `hcont` → `husc` in `pencil_hgood`,
               `btw_order_aux_rank`, `btw_order_aux`) and the proof body of
               `BetweennessOrder.lean`. It must NOT touch `ThinB.lean` /
               `ThinBExistence.lean`, which call1 owns.
- Gate:        `two_B_existence` must still build and stay proof-complete;
               `btw_order`'s public statement byte-for-byte unchanged;
               `sorry` count drops by exactly 1.
- Expected:    hardest call in the queue; budget several `ask` rounds.
