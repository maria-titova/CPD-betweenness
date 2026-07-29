You are working inside the Lean 4 project **CPDLinear**, whose complete source is in
this project and already builds against Mathlib (toolchain `leanprover/lean4:v4.28.0`).
The mathematical source of truth is `SPECIFICATION.tex` (the paper). `TASK.md` is a copy
of these instructions.

# Scope of this call

Prove **exactly one** declaration:

- `CPDLinear.DisclosureGame.btw_order_usc` in `CPDLinear/BetweennessOrderUSC.lean`

It is currently `sorry`. This is the level-set ranking lemma `lem:btw-order` with
**upper semicontinuity in place of continuity** — the hypothesis is
`husc : UpperSemicontinuousOn G.vbar (simplexOn G.Θ)`. It is the last missing piece of
the unconditional thin-B existence theorem `thm:thinB-cppbe`.

In `SPECIFICATION.tex` this is Lemma `lem:btw-order` and the proof immediately following
it in the appendix. **Read that proof in full before writing any Lean.** Pay particular
attention to Case 4 and to the paragraph beginning "We now check that every relevant
slice is lower-dimensional. This is the only place where upper semicontinuity is used."

# You are not starting from scratch

The entire recursion already exists and is proved in this project, under a continuity
hypothesis:

- `CPDLinear/BetweennessRank.lean` — `proper_separation`, the convexity lemmas for the
  level sets of `G.vbar`, `vectorSpan_hyperplane_finrank_lt`, the single-separator
  `rankRel*` family, the two-separator `pencil*` family, and the induction on affine
  dimension `btw_order_aux_rank` / `btw_order_aux`.
- `CPDLinear/BetweennessOrder.lean` — `btw_order`, which instantiates `btw_order_aux` at
  `F = simplexOn G.Θ` and obtains continuity from single-valuedness.

Structurally, `btw_order_usc` is `btw_order` with `hSV`/continuity replaced by `husc`.
Cases 1–3 and the whole induction are **unchanged**. Do not redesign them.

# The one real gap

Continuity is used in exactly **one** place: `pencil_hgood` in `BetweennessRank.lean`
(around line 711), in its final step. There, having produced a segment `w_α = α z +
(1-α) u` with `G.vbar w_α = y` for every `α ∈ (0,1)`, the proof lets `α → 0` and uses
continuity of `G.vbar` at `u` to conclude `G.vbar u = y`, contradicting `y < G.vbar u`.

**That argument cannot be repaired under upper semicontinuity, and you must not try.**
Upper semicontinuity gives `limsup_α G.vbar w_α ≤ G.vbar u`, i.e. `y ≤ G.vbar u`, which
is consistent with `y < G.vbar u`. The inequality runs the wrong way.

The paper replaces it with a different argument for the same conclusion — that for every
`λ` with `F_λ ∩ S_F ≠ ∅` the pencil member `h_λ` is non-constant on `aff F`, so the tie
slice `F_λ` is lower-dimensional. In the notation of the appendix proof:

1. Because `G.vbar` is upper semicontinuous, the strict lower set `L^{--} = {v < y}` is
   **relatively open** in `simplexOn G.Θ`. (This is the only use of `husc`.)
2. Hence in Case 4, where `B_F = L^{--} ∩ F` is non-empty, `B_F` is a non-empty
   relatively open subset of the convex set `F`, and therefore `aff B_F = aff F`.
3. Suppose `h_λ` is constant on `F` and `F_λ ∩ S_F ≠ ∅`. Evaluating at a point of
   `F_λ` makes that constant `0`.
   - For `λ ∈ (0,1)`: on `B_F` we have `a ≤ 0` and `b ≤ 0`, and `λ a + (1-λ) b = 0`
     there with both coefficients strictly positive, so `a = b = 0` on `B_F`. An affine
     functional vanishing on `B_F` vanishes on `aff B_F = aff F`, so `b ≡ 0` on `F`,
     contradicting proper separation for `b`.
   - For `λ = 1`: `h_1 = a`, and `a ≡ 0` on `F` contradicts proper separation for `a`.
   - For `λ = 0`: `h_0 = b`, and `b ≡ 0` on `F` contradicts proper separation for `b`.
4. Therefore `h_λ` is non-constant on `aff F` and `F_λ` has affine dimension `< d` —
   which is exactly the conclusion `pencil_hgood` currently delivers, and it feeds
   `vectorSpan_hyperplane_finrank_lt` in the same way.

So the task is: reproduce the conclusion of `pencil_hgood` from `husc` by the argument
above, and re-run the existing induction with it.

# How to structure the work

Preferred route — **generalize the hypothesis in place**. Change `hcont : ContinuousOn
G.vbar (simplexOn G.Θ)` to `husc : UpperSemicontinuousOn G.vbar (simplexOn G.Θ)` in
`pencil_hgood`, `btw_order_aux_rank`, and `btw_order_aux`, prove `pencil_hgood` by the
new argument, and have the existing `btw_order` supply upper semicontinuity from
continuity (`ContinuousOn.upperSemicontinuousOn`, or derive it directly) so that its own
statement and every downstream user are unaffected. This call is therefore an explicit,
narrow exception to the pipeline's usual "do not touch other files" rule: you may edit
`CPDLinear/BetweennessRank.lean` and the proof body of `CPDLinear/BetweennessOrder.lean`
for this purpose **and no other**.

Note that `pencil_hgood` will now need `B_F ≠ ∅` — the Case 4 hypothesis — where the
continuous proof needed only `hA2`. Thread the extra hypothesis through
`btw_order_aux_rank`; Case 4 is the only caller that needs it, and Cases 2 and 3 use the
single-separator `rankRel` family, not the pencil.

If in-place generalization turns out to be impractical, the fallback is to prove
`btw_order_usc` self-containedly inside `CPDLinear/BetweennessOrderUSC.lean`,
re-proving whatever it needs there. Do not leave the project in a half-refactored state.

# Rules

- **Do not change any statement.** The signature of `btw_order_usc` — name, binders,
  hypotheses, conclusion — must remain byte-for-byte as given, and the public statement
  of `CPDLinear.DisclosureGame.btw_order` in `BetweennessOrder.lean` must remain
  byte-for-byte as it is now. Only proof bodies, private/auxiliary lemma signatures in
  `BetweennessRank.lean`, and the imports of `BetweennessOrderUSC.lean` may change.
  If you believe the statement is unprovable as written, stop and say so in
  `ARISTOTLE_SUMMARY.md` rather than adjusting it.
- **`two_B_existence` in `BetweennessOrder.lean` must still build and stay proof-complete.**
  It is the paper's headline theorem and it consumes `btw_order`. Breaking it fails the
  call, however good the new lemma is.
- **Leave every other `sorry` in the project exactly as it is.** The project ships with
  18 further `sorry` declarations (in `ThinB.lean`, `ThinBExistence.lean`, and
  `BetweennessPending.lean`); they are other calls in this pipeline and are deliberately
  out of scope. Do not prove them, do not delete them, do not restate them. In
  particular another call is running concurrently against `ThinB.lean`: **do not modify
  `CPDLinear/ThinB.lean` or `CPDLinear/ThinBExistence.lean` at all.**
- Use no `sorry` in `btw_order_usc`. If you are genuinely blocked, leave it `sorry`,
  revert any half-finished refactor so the project still builds, and explain the
  obstruction in `ARISTOTLE_SUMMARY.md`.
- The whole project must still build (`lake build`, package `CPDLinear`).

Deliver the updated `CPDLinear/BetweennessOrderUSC.lean` together with whatever changes
to `CPDLinear/BetweennessRank.lean` and `CPDLinear/BetweennessOrder.lean` the
generalization required.
