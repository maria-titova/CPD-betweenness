You are working inside the Lean 4 project **CPDLinear**, whose complete source is in
this project and already builds against Mathlib (toolchain `leanprover/lean4:v4.28.0`).
The mathematical source of truth is `SPECIFICATION.tex` (the paper). `TASK.md` is a copy
of these instructions.

# Scope of this call

Prove **exactly these three declarations**, all in `CPDLinear/ThinBExistence.lean`:

1. `CPDLinear.DisclosureGame.IsThinB.betweenness`
2. `CPDLinear.DisclosureGame.IsThinB.hasCommonValueIntersections`
3. `CPDLinear.DisclosureGame.HasCommonValueIntersections.of_subgame`

They are currently stated with `sorry`. Replace only those three proof bodies.

These are the **bridge** from the analytic thin-B facts (`ThinB.lean`, about a bare
function `v` on `simplexOn Θ`) to the game-level API (`DisclosureGame`, about `G.V`,
`G.vbar`, `G.Betweenness`). They are short. Everything downstream in this pipeline
consumes them, so correctness matters more than cleverness here.

# Lemmas you may assume

`CPDLinear.thinB_eq_Icc`, `CPDLinear.thinB_common_value`,
`CPDLinear.thinBUpper_isBetweenness`, `CPDLinear.thinBLower_isBetweenness`,
`CPDLinear.IsBetweenness.bddOn_simplex` and `CPDLinear.thinB_A4` are being proved by
other calls in this pipeline and may still carry `sorry` in the copy you receive.
**Their statements are frozen and correct. Use them freely as if proved. Do not prove
them, do not restate them, do not delete their `sorry`.**

This call is essentially "transport those four facts across the `IsThinB` definition".

# The mathematics

`G.IsThinB` unfolds to: there is `v` with `IsBetweenness G.Θ v` and
`∀ μ ∈ simplexOn G.Θ, G.V μ = thinB G.Θ v μ`.

## `IsThinB.betweenness`

`G.Betweenness` is the betweenness property of the **upper envelope** `G.vbar`, where
`G.vbar μ = sSup (G.V μ)` (`Game.lean`). Under `IsThinB`, for `μ ∈ simplexOn G.Θ`,
`G.V μ = thinB G.Θ v μ = Icc (thinBLower G.Θ v μ) (thinBUpper G.Θ v μ)` by
`thinB_eq_Icc`, so `G.vbar μ = thinBUpper G.Θ v μ` (the `sSup` of a non-empty `Icc` is
its right endpoint). Then `thinBUpper_isBetweenness` gives the betweenness inequalities
for `thinBUpper G.Θ v`, and rewriting along `G.vbar = thinBUpper G.Θ v` on the simplex
yields `G.Betweenness`. Mind the difference in shape between `IsBetweenness` (bare
function, `ThinB.lean`) and `G.Betweenness` (`Betweenness.lean`) and bridge it explicitly;
this small mismatch is the only real work in this declaration.

## `IsThinB.hasCommonValueIntersections`

Unfold `HasCommonValueIntersections`, rewrite every `G.V` as `thinB G.Θ v` using the
`IsThinB` witness, and apply `thinB_common_value` directly. The only care needed is that
the mixture `fun θ => ∑ i, a i * μs i θ` lies in `simplexOn G.Θ` (a convex combination of
simplex points with positive weights summing to one) so the rewrite applies to it too.

## `HasCommonValueIntersections.of_subgame`

Pure transport, no analysis. `H` has `H.Θ ⊆ G.Θ` and `H.V = G.V` on `simplexOn H.Θ`.
Given data for `H`, note `simplexOn H.Θ ⊆ simplexOn G.Θ` (a belief supported on the
smaller set is supported on the larger — this follows from the `simplexOn` definition in
`Simplex.lean`), rewrite each `H.V (μs i)` as `G.V (μs i)`, apply `hcommon`, and rewrite
back. The mixture again needs to be seen in `simplexOn H.Θ` to rewrite its value.

**This lemma is the reason the pipeline never recomputes a thin hull on a smaller
simplex.** See the trap below.

# Traps — do not fall into these

- **Do not** try to prove that a face/message subgame of a thin-B game is itself
  `IsThinB` by recomputing `thinB` on the smaller simplex. It is false in general:
  cluster values visible only from ambient directions disappear. That is precisely why
  `HasCommonValueIntersections` exists as a separate, transportable property and why
  `of_subgame` is stated the way it is.
- **Do not** replace `G.V` by the singleton `{G.vbar μ}`. That correspondence need not
  satisfy the standing upper-hemicontinuity assumption `A4`, since `G.vbar` is only upper
  semicontinuous here.

# Rules

- **Do not change any statement.** The signatures of the three targets — name, binders,
  hypotheses, conclusion — must remain byte-for-byte as given, as must the definitions
  `IsThinB`, `HasCommonValueIntersections`, `Coalition.repayablePayoffs` and
  `Partition.IsUpperNormalized`. If you believe a statement is unprovable as written,
  stop and say so in `ARISTOTLE_SUMMARY.md` rather than adjusting it.
- **Do not touch any other file.** In particular do not modify `CPDLinear/ThinB.lean`,
  `CPDLinear/BetweennessOrderUSC.lean`, `CPDLinear/BetweennessRank.lean`,
  `CPDLinear/BetweennessOrder.lean`, or `CPDLinear/BetweennessPending.lean`. Other calls
  in this pipeline own those files and are running concurrently.
- **Leave every other `sorry` in the project exactly as it is** — including the other six
  `sorry`s in `ThinBExistence.lean`, which are later calls in this pipeline.
- New private helper lemmas are welcome; put them in `CPDLinear/ThinBExistence.lean`,
  above the declaration that uses them.
- **Partial credit is valuable.** If genuinely blocked on one, prove the others, leave
  that one `sorry`, and explain in `ARISTOTLE_SUMMARY.md`.
- The whole project must still build (`lake build`, package `CPDLinear`).

Deliver the updated `CPDLinear/ThinBExistence.lean`.
