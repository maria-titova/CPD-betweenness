You are working inside the Lean 4 project **CPDLinear**, whose complete source is in
this project and already builds against Mathlib (toolchain `leanprover/lean4:v4.28.0`).
The mathematical source of truth is `SPECIFICATION.tex` (the paper). `TASK.md` is a copy
of these instructions.

# Scope of this call

Prove **exactly these three declarations**, all in `CPDLinear/ThinB.lean`:

1. `CPDLinear.IsBetweenness.bddOn_simplex`
2. `CPDLinear.thinB_eq_Icc`
3. `CPDLinear.thinB_A4`

They are currently stated with `sorry`. Replace only those three `sorry` proof bodies.

This is the thin-B **definitional layer**: the definitions `clusterValues` and `thinB`
together with the lemma certifying that a thin-B correspondence is an admissible payoff
correspondence for the model. In `SPECIFICATION.tex` this is Definition `dfn:thinB`,
Lemma `lem:thinB-A4`, and the appendix subsection **"Proof of \cref{lem:thinB-A4}"** in
section "Proofs for \cref{sec:existence-thinB}". Read that appendix subsection in full
before writing any Lean; it is a complete proof and you should follow it.

# The mathematics (mirrors the appendix proof)

Let `Θ` be a finite non-empty type set, `v : (T → ℝ) → ℝ` satisfy `IsBetweenness Θ v`
(betweenness on `simplexOn Θ`; `v` is **not** assumed continuous), and let
`thinB Θ v μ = convexHull ℝ (clusterValues Θ v μ)`.

**Step 1 — `IsBetweenness.bddOn_simplex`.** First establish the finite-mixture form of
betweenness: for finitely many `μ i ∈ simplexOn Θ` and weights `λ i ≥ 0` summing to `1`,
`min_{i : λ i > 0} v (μ i) ≤ v (∑ i, λ i • μ i) ≤ max_{i : λ i > 0} v (μ i)`.
Prove it by induction on the number of strictly-positive weights: discard zero weights;
the one-term case is immediate; with at least two terms, split off one term of weight
`λ ∈ (0,1)`, renormalize the rest to a belief `μ'`, apply the induction hypothesis to
`μ'`, then apply `IsBetweenness` to `λ • μ i + (1-λ) • μ'`.
Then every `μ ∈ simplexOn Θ` is the mixture `∑ θ ∈ Θ, μ θ • δ θ` of the vertices, so
with `a := min_{θ ∈ Θ} v (δ θ)` and `b := max_{θ ∈ Θ} v (δ θ)` (finite non-empty `Θ`)
we get `v μ ∈ Set.Icc a b` for every `μ ∈ simplexOn Θ`. Consequently
`clusterValues Θ v μ ⊆ Set.Icc a b` for every such `μ` — this is what makes the thin-B
values compact, and it is the keystone the other two declarations rest on.

**Step 2 — `thinB_eq_Icc`.** Show the graph
`Γ = {(μ, w) | μ ∈ simplexOn Θ ∧ w ∈ clusterValues Θ v μ}` is closed, by a diagonal
argument: given `(μ k, w k) ∈ Γ` with `(μ k, w k) → (μ, w)`, pick for each `k` a
`ν k ∈ simplexOn Θ` with `‖ν k - μ k‖ < 1/(k+1)` and `|v (ν k) - w k| < 1/(k+1)`
(possible since `w k` is a cluster value at `μ k`); then `ν k → μ` and `v (ν k) → w`,
so `w ∈ clusterValues Θ v μ`. Each section `clusterValues Θ v μ` is non-empty (the
constant sequence `μ` gives `v μ`), closed, and bounded by Step 1, hence compact.
The convex hull of a non-empty compact subset of `ℝ` is the closed interval between its
infimum and supremum, which gives
`thinB Θ v μ = Set.Icc (thinBLower Θ v μ) (thinBUpper Θ v μ)`.

**Step 3 — envelope semicontinuity (a private helper, not a listed target).**
`thinBUpper Θ v` is upper semicontinuous and `thinBLower Θ v` lower semicontinuous on
`simplexOn Θ`: for `μ k → μ`, pass to a subsequence along which
`thinBUpper Θ v (μ k)` tends to `limsup_k thinBUpper Θ v (μ k)`; since each
`(μ k, thinBUpper Θ v (μ k)) ∈ Γ` and `Γ` is closed, that limsup lies in
`clusterValues Θ v μ` and is therefore `≤ thinBUpper Θ v μ`. Symmetrically for
`thinBLower`.

**Step 4 — `thinB_A4`.** The four conjuncts. Non-emptiness and compactness and
order-connectedness follow from Step 2 (`Set.Icc` with `thinBLower ≤ thinBUpper`).
For `UpperHemicontinuousOn` (its definition is in `CPDLinear/Game.lean`): given
`μ ∈ simplexOn Θ` and open `U ⊇ thinB Θ v μ`, compactness of the interval gives `ε > 0`
with `Set.Icc (thinBLower Θ v μ - ε) (thinBUpper Θ v μ + ε) ⊆ U`; Step 3 gives a
neighbourhood `W ∈ 𝓝[simplexOn Θ] μ` on which
`thinBLower Θ v μ - ε < thinBLower Θ v μ' ≤ thinBUpper Θ v μ' < thinBUpper Θ v μ + ε`,
so `thinB Θ v μ' ⊆ U` for every `μ' ∈ W`.

# Rules

- **Do not change any statement.** The signatures of the three target declarations —
  name, binders, hypotheses, conclusion — must remain byte-for-byte as given. Only the
  proof body after `:=` may change. The same applies to `IsBetweenness`, `clusterValues`,
  `thinB`, `thinBUpper`, `thinBLower`: do not restate, rename, weaken, or redefine them.
  If you believe a statement is wrong or unprovable as written, stop and say so in
  `ARISTOTLE_SUMMARY.md` rather than adjusting it.
- **Do not touch any other file.** In particular do not modify `CPDLinear/Game.lean`,
  `CPDLinear/Simplex.lean`, `CPDLinear/ThinBExistence.lean`,
  `CPDLinear/BetweennessPending.lean`, or any already-proved module.
- **Leave every other `sorry` in the project exactly as it is.** The project ships with
  16 further `sorry` declarations (in `ThinB.lean`, `ThinBExistence.lean`,
  `BetweennessOrderUSC.lean`, and `BetweennessPending.lean`); they are later calls in
  this pipeline and are deliberately out of scope. Do not prove them, do not delete
  them, do not restate them.
- New auxiliary lemmas are welcome, but put them in `CPDLinear/ThinB.lean` in namespace
  `CPDLinear`, above the declaration that uses them.
- `CPDLinear/ThinB.lean` imports only `CPDLinear.Game` and must stay that way: this file
  is deliberately **axiom-free** (the project has one axiom, `CPDLinear.kakutani`, reached
  only through `CPDLinear.PBEExistence`). Do not add an import that pulls it in.
  `#print axioms CPDLinear.thinB_A4` must list only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Use no `sorry` in the three target declarations. If you are genuinely blocked on one,
  leave that single one `sorry`, finish the others, and explain the obstruction.
- The whole project must still build (`lake build`, package `CPDLinear`).

Deliver the updated `CPDLinear/ThinB.lean`.
