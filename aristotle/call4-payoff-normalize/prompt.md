You are working inside the Lean 4 project **CPDLinear**, whose complete source is in
this project and already builds against Mathlib (toolchain `leanprover/lean4:v4.28.0`).
The mathematical source of truth is `SPECIFICATION.tex` (the paper). `TASK.md` is a copy
of these instructions.

# Scope of this call

Prove **exactly these three declarations**, all in `CPDLinear/ThinBExistence.lean`:

1. `CPDLinear.DisclosureGame.thinB_coalition_payoff_set`
2. `CPDLinear.DisclosureGame.exists_upperNormalizedPBE`
3. `CPDLinear.DisclosureGame.thinB_upperNormalizedPBE_subgame`

They are currently stated with `sorry`. Replace only those three proof bodies.

In `SPECIFICATION.tex` these are Lemma `lem:thinB-value-set` and Proposition
`prop:thinB-upper-pbe`, with proofs in the appendix subsections "Proof of
\cref{lem:thinB-value-set}" and "Proof of \cref{prop:thinB-upper-pbe}".
**Read both in full before writing any Lean.**

# Lemmas you may assume

Everything in `CPDLinear/ThinB.lean` and the three bridge lemmas
`IsThinB.betweenness`, `IsThinB.hasCommonValueIntersections`,
`HasCommonValueIntersections.of_subgame` are being proved by other calls in this
pipeline and may still carry `sorry` in the copy you receive. **Their statements are
frozen and correct. Use them freely as if proved. Do not prove them, do not restate
them, do not delete their `sorry`.**

# The proved single-valued analogue — read it first

`CPDLinear/BetweennessCore.lean` contains `value_id` (around line 712):

    lemma value_id (hSV : G.SingleValued) (hB : G.Betweenness) (K : G.Coalition) :
        K.w = G.vbar (G.condPrior K.C)

`thinB_coalition_payoff_set` is its correspondence-valued strengthening: instead of
pinning `K.w` to a single number it identifies the **whole set** of payoffs compatible
with a fixed coalition strategy as `G.V (G.condPrior K.C)`. The proof of `value_id`
already contains the Bayes-plausibility decomposition you need
(`btwc_condPrior_decomp`, `btwc_bayes`, `btwc_coalitionBelief_mem`); read it and reuse
its structure. You may not edit that file, but you may re-prove any `private` helper you
need inside `ThinBExistence.lean`.

# The mathematics

## `thinB_coalition_payoff_set`

`Coalition.repayablePayoffs K = {w | ∀ m ∈ K.σ.evidence, w ∈ G.V (K.σ.coalitionBelief m)}`
and the claim is that this equals `G.V (G.condPrior K.C)`.

Bayes plausibility in the coalition gives
`G.condPrior K.C = ∑_{m ∈ X(σ)} p_σ(m) • μ_σ(· | m)` with strictly positive weights
summing to one. Coalition condition `C4` gives a common payoff `K.w ∈ G.V (μ_σ(· | m))`
for every `m ∈ X(σ)`. So `hcommon` (the `HasCommonValueIntersections` hypothesis) applies
with `μs := m ↦ K.σ.coalitionBelief m`, `a := p_σ`, `w := K.w`, and yields exactly

    G.V (G.condPrior K.C) = {x | ∀ m, x ∈ G.V (K.σ.coalitionBelief m)}

which is the claim. Conditions `C1`–`C3` do not mention the payoff, so a triple
`(C, σ, w̃)` is a coalition exactly when `w̃` lies in that intersection.

The index bookkeeping — turning the `Finset` of on-path messages into the `Fin n` family
that `HasCommonValueIntersections` expects — is the bulk of the Lean work. Do it once as
a private helper; call 5 and the crown call need the same conversion.

## `exists_upperNormalizedPBE`

Start from an existing PBE partition with strictly decreasing payoffs: `exists_PBE`
(`PBEExistence.lean`) plus `pbe_characterization` (`PBEChar.lean`), exactly as
`BetweennessOrder.lean` does around `btwc_isPBE_zero` / `btwcAux_exists_partition`
(lines ~517–560). Then **normalize the cells from first to last**, raising each payoff
to the upper endpoint `G.vbar (G.condPrior (P.C t))`:

- First cell: raise its payoff to `G.vbar (G.condPrior C₁)`. Feasible for the same
  coalition strategy by `thinB_coalition_payoff_set`; preserves individual rationality
  and the payoff order.
- Inductive step: processed cells form a strictly decreasing normalized prefix; the next
  cell is `(C, σ, w)`; let `p` be the last processed payoff and `r := G.vbar (G.condPrior C)`.
  Since processed payoffs only ever increase and the original order was strict, `w < p`.
  - If `r < p`: replace `w` by `r`. Feasible, and `r ≥ w`, so IR and strict order survive.
  - If `r ≥ p`: then `G.vlow (G.condPrior C) ≤ w < p ≤ r`, so
    `thinB_coalition_payoff_set` allows this cell to be paid exactly `p`. Pay it `p` and
    **merge it with the preceding processed cell**. The two evidence sets are disjoint (no
    type in the later residual set can send evidence used by the preceding cell), every
    type keeps its old strategy, posteriors at used messages are unchanged, every used
    message pays `p`, and the preimage of the union of evidence sets is the union of the
    two adjacent cells — so the merged triple is a coalition of the residual game before
    the preceding cell. The merged prior is a **strict** convex combination of the two old
    priors and both old value intervals contain `p`, so `hcommon` gives
    `V(merged) = V(preceding) ∩ V(C)`, whose upper endpoint is `p`. Hence the merged cell
    is upper-normalized, its payoff is weakly above both old payoffs (IR preserved), and
    removing it leaves the same residual game as removing the two old cells.

The procedure is finite and terminates with an IR partition, strictly decreasing payoffs,
and `w t = G.vbar (G.condPrior (P.C t))` at every cell — a PBE partition by
`pbe_characterization`.

Note this declaration takes only `hcommon`, **not** `hthin`. That is deliberate: it is
what lets the same statement be applied to auxiliary games later.

## `thinB_upperNormalizedPBE_subgame`

A thin wrapper: from `hthin` get `hcommon` via `IsThinB.hasCommonValueIntersections`,
transport it to `H` with `HasCommonValueIntersections.of_subgame hΘ hV`, then apply
`exists_upperNormalizedPBE` in `H`. If your `exists_upperNormalizedPBE` is stated and
proved for a general game with `hcommon`, this is a few lines.

# Traps — do not fall into these

- **Do not** recompute `thinB` on the smaller simplex for a face or message-deleted
  subgame. Auxiliary games keep the **ambient** correspondence restricted to their face;
  cluster values visible only from ambient directions would be lost. Transport
  `HasCommonValueIntersections` instead — that is exactly what `of_subgame` is for.
- **Do not** replace `G.V` by the singleton `{G.vbar μ}`. It need not satisfy `A4`.
- **Do not** assume `G.vbar` is continuous. Under thin-B it is only upper semicontinuous.

# Rules

- **Do not change any statement.** Signatures of the three targets byte-for-byte as
  given, as must the definitions `IsThinB`, `HasCommonValueIntersections`,
  `Coalition.repayablePayoffs`, `Partition.IsUpperNormalized`. If you believe a statement
  is unprovable as written, stop and say so in `ARISTOTLE_SUMMARY.md`.
- **Do not touch any other file.** Other calls own `ThinB.lean`,
  `BetweennessOrderUSC.lean`, `BetweennessRank.lean`, `BetweennessOrder.lean` and are
  running concurrently. Re-prove any `private` helper you need inside
  `ThinBExistence.lean` rather than editing its home file.
- **Leave every other `sorry` in the project exactly as it is.**
- **Partial credit is valuable.** `thinB_coalition_payoff_set` is the important one and
  the other calls depend on it; if you must leave something `sorry`, leave
  `exists_upperNormalizedPBE`, not that. Explain any gap in `ARISTOTLE_SUMMARY.md`.
- The whole project must still build (`lake build`, package `CPDLinear`).

Deliver the updated `CPDLinear/ThinBExistence.lean`.
