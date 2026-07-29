You are working inside the Lean 4 project **CPDLinear**, whose complete source is in
this project and already builds against Mathlib (toolchain `leanprover/lean4:v4.28.0`).
The mathematical source of truth is `SPECIFICATION.tex` (the paper). `TASK.md` is a copy
of these instructions.

# Scope of this call

Prove **exactly these three declarations**, all in `CPDLinear/ThinB.lean`:

1. `CPDLinear.thinBUpper_isBetweenness`
2. `CPDLinear.thinBLower_isBetweenness`
3. `CPDLinear.thinB_common_value`

They are currently stated with `sorry`. Replace only those three proof bodies. These are
the last three `sorry`s in `ThinB.lean`; when this call succeeds that file is complete.

In `SPECIFICATION.tex` these are Lemma `lem:thinB-envelope-B` and Proposition
`prop:thinB-common-value`, with proofs in the appendix subsections
"Proof of \cref{lem:thinB-envelope-B}" and "Proof of \cref{prop:thinB-common-value}".
**Read both in full before writing any Lean.** They are complete proofs; follow them.

# Lemmas you may assume

`CPDLinear.IsBetweenness.bddOn_simplex`, `CPDLinear.thinB_eq_Icc` and
`CPDLinear.thinB_A4` are being proved by another call in this pipeline and may still
carry `sorry` in the copy you receive. **Their statements are frozen and correct. Use
them freely as if proved. Do not prove them, do not restate them, do not delete their
`sorry`.** You will need `bddOn_simplex` (boundedness of `v` on the simplex, hence of
every `clusterValues` set) and `thinB_eq_Icc` (`thinB Θ v μ = Icc (thinBLower Θ v μ)
(thinBUpper Θ v μ)`) constantly.

# The mathematics

## `thinBUpper_isBetweenness` (and `thinBLower_isBetweenness`)

Betweenness of `v` makes every strict sublevel set `{v < c}` and every strict superlevel
set `{v > c}` convex. The proof shows the *weak* level sets of the upper envelope are
convex, via the two identities (relative to `simplexOn Θ`):

- `{thinBUpper ≤ c} = ⋂_{ε > 0} interior {v < c + ε}`
- `{thinBUpper ≥ c} = ⋂_{ε > 0} closure {v > c - ε}`

For the first: if `thinBUpper μ ≤ c` but `μ ∉ interior {v < c+ε}` for some `ε > 0`, there
are `ν n → μ` with `v (ν n) ≥ c + ε`; boundedness (`bddOn_simplex`) gives a subsequence
whose values converge to some `w ≥ c + ε`, so `w ∈ clusterValues Θ v μ`, contradicting
`thinBUpper μ ≤ c`. Conversely, if `μ` is in the right-hand side and `w ∈ clusterValues
Θ v μ` is witnessed by `ν n → μ`, then for every `ε > 0` eventually `v (ν n) < c + ε`,
so `w ≤ c`.

For the second: if `thinBUpper μ ≥ c`, a sequence witnessing the cluster value
`thinBUpper μ` meets every neighbourhood of `μ` inside `{v > c - ε}`. Conversely, given
`μ` in the right-hand side pick `ν n → μ` with `v (ν n) > c - 1/(n+1)`; a convergent
subsequence of the bounded values has limit `w ≥ c` in `clusterValues Θ v μ`.

Relative interiors and closures of convex sets are convex, and arbitrary intersections of
convex sets are convex. So every weak sub- and superlevel set of `thinBUpper` is convex,
i.e. `thinBUpper` is both quasiconvex and quasiconcave — which is exactly
`IsBetweenness Θ (thinBUpper Θ v)`.

Note the shape of the target: `IsBetweenness` is stated as a pair of `min ≤ · ∧ · ≤ max`
inequalities at a mixture. Convexity of `{f ≤ c}` and `{f ≥ c}` for all `c` gives exactly
those two inequalities — instantiate at `c = max (f μ) (f μ')` and `c = min (f μ) (f μ')`.
Proving that bridge once as a private helper lemma (`quasiconvex ∧ quasiconcave ↔
IsBetweenness`) and using it for both envelopes is the efficient route.

For `thinBLower_isBetweenness`, apply the result just proved to `u := -v`. Then `u`
satisfies betweenness, `clusterValues Θ u μ = {-w | w ∈ clusterValues Θ v μ}`, so
`thinBUpper Θ u = -(thinBLower Θ v)`; negate the inequalities.

## `thinB_common_value`

Set `ℓ* := max_i thinBLower Θ v (μs i)` and `r* := min_i thinBUpper Θ v (μs i)`. Since
`w ∈ thinB Θ v (μs i)` for every `i`, `thinB_eq_Icc` gives
`⋂_i thinB Θ v (μs i) = Icc ℓ* r*` (in particular `ℓ* ≤ w ≤ r*`, so it is non-empty).

The inclusion `Icc ℓ* r* ⊆ thinB Θ v μ` follows from the envelope betweenness just proved
plus the finite-mixture form of betweenness (the induction established inside
`bddOn_simplex`): `thinBLower Θ v μ ≤ ℓ*` and `r* ≤ thinBUpper Θ v μ`.

For equality it suffices to prove the two endpoints match. Suppose `thinBUpper Θ v μ >
r*`. Pick `c` with `r* < c < thinBUpper Θ v μ` and `i₀` with `thinBUpper Θ v (μs i₀) =
r*`. Let `K := {v < c}`, convex. Every `μs i` lies in `closure K` (a sequence witnessing
`thinBLower Θ v (μs i) ≤ w ≤ r* < c` does it), and `μs i₀` lies in `interior K` —
otherwise there are `ν n → μs i₀` with `v (ν n) ≥ c`, and a convergent subsequence of
their bounded values gives a cluster value `≥ c > thinBUpper Θ v (μs i₀)`, absurd.

Now the elementary convex-set fact, worth proving as a private helper: *if `K` is convex,
every `μs i ∈ closure K`, at least one `μs i ∈ interior K`, and all weights are strictly
positive, then the convex combination lies in `interior K`.* One component is immediate;
otherwise isolate an interior component, note the normalized mixture of the rest lies in
the convex set `closure K`, and use that every non-trivial point of the segment from an
interior point to a point of the closure is interior.

It gives `μ ∈ interior K`, so every sequence converging to `μ` is eventually in `K`, so
every cluster value at `μ` is `≤ c` — contradicting `thinBUpper Θ v μ > c`. Hence
`thinBUpper Θ v μ = r*`. The lower endpoint is symmetric with `H := {v > c}`.

All interiors and closures are **relative to `simplexOn Θ`**. Getting that wrong is the
most likely way to fail this call: the simplex has empty interior in `T → ℝ`.

# Rules

- **Do not change any statement.** The signatures of the three targets — name, binders,
  hypotheses, conclusion — must remain byte-for-byte as given. Do not restate, rename,
  weaken or redefine `IsBetweenness`, `clusterValues`, `thinB`, `thinBUpper`,
  `thinBLower`. If you believe a statement is unprovable as written, stop and say so in
  `ARISTOTLE_SUMMARY.md` rather than adjusting it.
- **Do not touch any other file.** In particular do not modify `CPDLinear/Game.lean`,
  `CPDLinear/Simplex.lean`, `CPDLinear/ThinBExistence.lean`,
  `CPDLinear/BetweennessOrderUSC.lean`, `CPDLinear/BetweennessRank.lean`, or
  `CPDLinear/BetweennessPending.lean`. Other calls in this pipeline own those files and
  are running concurrently.
- **Leave every other `sorry` in the project exactly as it is.**
- New private helper lemmas are welcome; put them in `CPDLinear/ThinB.lean` in namespace
  `CPDLinear`, above the declaration that uses them.
- `CPDLinear/ThinB.lean` imports only `CPDLinear.Game` and must stay that way: this file
  is deliberately **axiom-free**. Do not add an import that reaches `CPDLinear.kakutani`.
- **Partial credit is valuable.** If you are genuinely blocked on one of the three, prove
  the other two, leave that one `sorry`, and explain the obstruction in
  `ARISTOTLE_SUMMARY.md`. Do not stall the whole call on one target.
- The whole project must still build (`lake build`, package `CPDLinear`).

Deliver the updated `CPDLinear/ThinB.lean`.
