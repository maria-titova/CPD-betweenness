import CPDLinear.BetweennessCore
import CPDLinear.BetweennessEqualizeAux

/-!
# Value-equalizing coalition at a minimal attaining evidence set (working-paper)

**Working-paper lemma (equalize).** Companion to Lemma 6 (btw-attained,
`BetweennessCore.lean`). Assume `V` is single-valued and `v̄` satisfies
betweenness (B). For a non-empty residual `R ⊆ Θ`, take an
**inclusion-minimal** non-empty evidence set `X* ⊆ 𝓜_R` whose relative
preimage attains the top pooling value `v*(R)`. Then `G|_R` admits an actual
coalition supported exactly on `X*`, with type set `M⁻¹_R(X*)` and payoff
`v*(R)` (`btw_equalize`).

The proof reruns the attainment argument of `btw_attained` on `X*`: the
auxiliary game's top cell is a coalition of `G|_R` whose evidence `X̃ ⊆ X*`
still attains `v*(R)` (`value_id`), so minimality forces `X̃ = X*` and the
auxiliary partition collapses to the single cell `M⁻¹_R(X*)`.
-/

open Set Topology

namespace CPDLinear

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-- **Working-paper lemma (equalize).** Assume `V` is single-valued and `v̄`
satisfies betweenness (B). Let `R ⊆ Θ` be non-empty and let `X* ⊆ 𝓜_R` be
non-empty, inclusion-minimal among the non-empty evidence sets whose relative
preimage attains `v*(R)`. Then `G|_R` admits a coalition
`(M⁻¹_R(X*), σ, v*(R))` with `X(σ) = X*`. -/
lemma btw_equalize (hSV : G.SingleValued) (hB : G.Betweenness)
    {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ G.Θ)
    {Xstar : Finset Msg} (hXsub : Xstar ⊆ G.restrictMsgSpace R) (hXne : Xstar.Nonempty)
    (hXattain : G.vbar (G.condPrior (preimage G.M R Xstar)) = G.vstar R)
    (hXmin : ∀ X : Finset Msg, X ⊆ G.restrictMsgSpace R → X.Nonempty →
        G.vbar (G.condPrior (preimage G.M R X)) = G.vstar R → X ⊆ Xstar → X = Xstar) :
    ∃ K : Coalition (G.restrict R hne hsub),
      K.C = preimage G.M R Xstar ∧ K.σ.evidence = (Xstar : Set Msg) ∧
      K.w = G.vstar R :=
  btweq_exists_coalition hSV hB hne hsub hXsub hXne hXattain hXmin

end DisclosureGame

end CPDLinear
