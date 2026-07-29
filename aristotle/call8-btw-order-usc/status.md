# call8-btw-order-usc

- Lane:        C (`BetweennessOrderUSC.lean`, `BetweennessRank.lean`, `BetweennessOrder.lean`)
- Targets:     `CPDLinear.DisclosureGame.btw_order_usc`
               (`lean/CPDLinear/BetweennessOrderUSC.lean`)
- TeX:         `lem:btw-order` (u.s.c. form) and the appendix proof following it,
               especially Case 4 and the slice-dimension paragraph
- Base commit: `71fccec`
- Project ID:  `17d68832-269e-49a4-9335-868987d26306`
- Task ID:     `f67361d6-a8c0-402c-81e9-66db436f4f5e`
- Status:      **COMPLETE** (submitted and returned 2026-07-29, ~2h20m — longest call)
- Retries:     0
- Merged:      yes
- Result:      `btw_order_usc` proved, no `sorry`. Aristotle took the preferred in-place
               route: generalized `hcont : ContinuousOn` → `husc : UpperSemicontinuousOn`
               in `pencil_hgood`, `btw_order_aux_rank` and `btw_order_aux`, reproved
               pencil non-constancy from openness of the strict lower level set with
               separate endpoint handling, and instantiated the generalized recursion in
               `BetweennessOrderUSC.lean`. `pencil_hgood` now needs strictly FEWER
               hypotheses than before (`hB` and `hgep` dropped) — the new argument is
               purely about openness, as the paper's proof predicts.
- Ownership:   bundle predated call1 and call3; its `ThinB.lean` and `ThinBExistence.lean`
               were verified byte-identical to `71fccec` (untouched by Aristotle) and
               **not** copied back. Only the three lane-C files were merged.
- Fidelity:    `btw_order_usc` statement byte-identical (only the `sorry` line replaced).
               `btw_order`'s public statement unchanged — its single edit is one line
               inside the proof body, `btwc_vbar_continuousOn hSV` →
               `(btwc_vbar_continuousOn hSV).upperSemicontinuousOn`. The
               `BetweennessRank` signature changes are the sanctioned auxiliary-lemma
               hypothesis generalization.
- Verified:    `lake build` exit 0, 8056 jobs. Sorry 13 → 12, delta exactly 1.
               **`two_B_existence` still proof-complete**, axioms unchanged
               `{propext, CPDLinear.kakutani, Classical.choice, Quot.sound}` — the
               headline theorem survived the refactor.
- Axioms:      `btw_order_usc` = `{propext, Classical.choice, Quot.sound}` — clean, no
               `sorryAx`, no `kakutani`. `btw_order` likewise unchanged and clean.
- Badge:       `lem:btw-order` flipped `\leanmixed{btw_order}{btw_order_usc}` →
               `\leanproved{btw_order; btw_order_usc}`.
