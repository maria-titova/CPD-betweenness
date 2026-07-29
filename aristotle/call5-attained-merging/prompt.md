You are working inside the Lean 4 project **CPDLinear**, whose complete source is in
this project and already builds against Mathlib (toolchain `leanprover/lean4:v4.28.0`).
The mathematical source of truth is `SPECIFICATION.tex` (the paper). `TASK.md` is a copy
of these instructions.

# Scope of this call

Prove **exactly these two declarations**, both in `CPDLinear/ThinBExistence.lean`:

1. `CPDLinear.DisclosureGame.thinB_attained`
2. `CPDLinear.DisclosureGame.thinB_merging`

They are currently stated with `sorry`. Replace only those two proof bodies.

In `SPECIFICATION.tex` these are Lemma `lem:thinB-attained` and Lemma `lem:thinB-merging`,
with proofs in the appendix subsections of the same names. **Read both in full before
writing any Lean.**

# The proved single-valued analogues — these are your templates

`CPDLinear/BetweennessCore.lean` contains the single-valued versions, fully proved:

- `btw_attained (hSV) (hB) {R} (hne) (hsub) : IsGreatest (G.restrict R hne hsub).coalitionPayoffs (G.vstar R)` — around line 781
- `btw_merging (hSV) (hB) {R} (hne) (hsub) (K) (hmax) (hne') (K') (hgt) : G.preimageSet R (K.σ.evidence ∪ K'.σ.evidence) = K.C ∪ K'.C ∧ G.vbar (G.condPrior (K.C ∪ K'.C)) = K.w` — around line 812

**Your two targets have literally the same conclusions.** The only difference is the
hypotheses: `(hSV, hB)` becomes `(hthin)`. So the right way to run this call is:

1. Read `btw_attained` and `btw_merging` and their supporting private lemmas
   (`vstar`, `vstar_isGreatest`, `btw_attained_le`, `btwc_pooling_coalition`,
   `btwc_condPrior_union`, `btwc_preimage_nonempty`) closely.
2. Identify every step that uses single-valuedness. There are only two kinds:
   - uses of `value_id` (`K.w = G.vbar (G.condPrior K.C)`) — replace by
     `thinB_coalition_payoff_set`, which gives the *set* identity
     `K.repayablePayoffs = G.V (G.condPrior K.C)`; combined with maximality of `K.w` this
     recovers `G.vbar (G.condPrior K.C) = K.w` where the original used `value_id`;
   - uses of continuity or of `G.vbar = G.vlow` — these must go. Under thin-B `G.vbar` is
     only upper semicontinuous and the correspondence is genuinely interval-valued.
3. Reuse everything else verbatim. You may not edit `BetweennessCore.lean`, but you may
   re-prove any `private` helper you need inside `ThinBExistence.lean`.

# Lemmas you may assume

Everything in `CPDLinear/ThinB.lean`, the bridge lemmas (`IsThinB.betweenness`,
`IsThinB.hasCommonValueIntersections`, `HasCommonValueIntersections.of_subgame`) and
`thinB_coalition_payoff_set`, `exists_upperNormalizedPBE`,
`thinB_upperNormalizedPBE_subgame` are being proved by other calls in this pipeline and
may still carry `sorry` in the copy you receive. **Their statements are frozen and
correct. Use them freely as if proved. Do not prove them, do not restate them, do not
delete their `sorry`.**

# The mathematics

## `thinB_attained`: `max 𝒲_R = v̄*(R)`, i.e. `IsGreatest … (G.vstar R)`

*Upper bound.* Let `(C, σ, w)` be a coalition of `G|_R`. Exclusivity and its converse
give `C = M⁻¹_R(X(σ))`, and `thinB_coalition_payoff_set` gives `w ≤ G.vbar (G.condPrior C)
≤ G.vstar R`. Hence `max 𝒲_R ≤ G.vstar R`. This mirrors `btw_attained_le` exactly.

*Attainment.* Let `X*` attain the max defining `G.vstar R` and put `C* := M⁻¹_R(X*)`.
Form the auxiliary game with type set `C*`, message set `X*`, mapping
`M'(θ) := M θ ∩ X*`, prior `G.condPrior C*`, and **the restriction of the ambient `V`**.
Every type in `C*` has a message in `X*` and every message in `X*` is available to a type
in `C*`, so this is a disclosure game.

Apply `thinB_upperNormalizedPBE_subgame` to it: a PBE partition with
`w̃₁ > ⋯ > w̃ₖ` and `w̃τ = G.vbar (G.condPrior C̃τ)`. The cells partition `C*`, so
`G.condPrior C* = ∑τ βτ • G.condPrior C̃τ` with positive weights summing to one. The
finite-mixture form of betweenness for `G.vbar` (available from `IsThinB.betweenness`)
gives `G.vstar R = G.vbar (G.condPrior C*) ≤ maxτ G.vbar (G.condPrior C̃τ) = w̃₁`.

The first auxiliary cell is a coalition of `G|_R`: its strategy uses only messages in
`X*` and induces the same posteriors, and if a type in `R` can send one of its messages
it lies in `C*` by definition of `C*`, whence auxiliary-game exclusivity places it in
`C̃₁`. So `w̃₁ ≤ max 𝒲_R ≤ G.vstar R ≤ w̃₁` and all are equalities.

## `thinB_merging`

*First conjunct.* Preimages distribute over unions; exclusivity and its converse give
`M⁻¹_R(X(σ)) = C` and `M⁻¹_R(X(σ')) \ C = M⁻¹_{R'}(X(σ')) = C'`, hence
`M⁻¹_R(X(σ) ∪ X(σ')) = C ∪ C'`. This part is identical to `btw_merging`'s first conjunct
— reuse that proof.

*Second conjunct.* By `thinB_coalition_payoff_set` the strategy `σ` can be paid
`G.vbar (G.condPrior C)`; maximality of `K.w` together with `K.w ∈ G.V (G.condPrior C)`
gives `G.vbar (G.condPrior C) = K.w`. Similarly `G.vbar (G.condPrior C') ≥ K'.w > K.w`.
Since `C` and `C'` are disjoint and non-empty, `G.condPrior (C ∪ C')` is a **strict**
convex combination of the two priors (`btwc_condPrior_union` is the identity you want),
so quasiconcavity of `G.vbar` — the `min ≤ ·` half of `IsThinB.betweenness` — gives
`G.vbar (G.condPrior (C ∪ C')) ≥ min {K.w, G.vbar (G.condPrior C')} = K.w`.
For the reverse, the first conjunct shows `C ∪ C'` is a relative preimage in `G|_R`, so
`thinB_attained` gives `G.vbar (G.condPrior (C ∪ C')) ≤ G.vstar R = max 𝒲_R = K.w`.

So `thinB_merging` genuinely depends on `thinB_attained`: prove `thinB_attained` first
and use it.

# Traps — do not fall into these

- **Do not** recompute `thinB` on the smaller simplex for the auxiliary game in
  `thinB_attained`. It keeps the **ambient** correspondence restricted to its face; that
  is exactly why `thinB_upperNormalizedPBE_subgame` is stated with an
  `H.V = G.V on simplexOn H.Θ` hypothesis rather than an `H.IsThinB` hypothesis.
- **Do not** replace `G.V` by the singleton `{G.vbar μ}`. It need not satisfy `A4`.
- **Do not** assume `G.vbar` is continuous or that `G.vbar = G.vlow`. Both hold in the
  single-valued templates and neither holds here.

# Rules

- **Do not change any statement.** Signatures of the two targets byte-for-byte as given,
  as must every definition in the file. If you believe a statement is unprovable as
  written, stop and say so in `ARISTOTLE_SUMMARY.md`.
- **Do not touch any other file.** Other calls own `ThinB.lean`,
  `BetweennessOrderUSC.lean`, `BetweennessRank.lean`, `BetweennessOrder.lean` and may be
  running concurrently. Re-prove any `private` helper you need inside
  `ThinBExistence.lean`.
- **Leave every other `sorry` in the project exactly as it is.**
- **Partial credit is valuable.** `thinB_attained` is the prerequisite; if you must leave
  one `sorry`, leave `thinB_merging`. Explain any gap in `ARISTOTLE_SUMMARY.md`.
- The whole project must still build (`lake build`, package `CPDLinear`).

Deliver the updated `CPDLinear/ThinBExistence.lean`.
