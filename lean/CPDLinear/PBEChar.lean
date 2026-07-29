import CPDLinear.PBE

/-!
# PBE characterization  (writeup §3: IR, strong-IR, prop pbe-characterization)

Individual rationality (Def IR), its strong form (Lemma strong-IR), and the
characterization (Prop pbe-characterization): a sender strategy is a PBE strategy
iff it is associated with an IR partition with non-increasing payoffs.

## A note on the statement of `pbe_characterization`

The proposition as originally phrased,

```
G.IsPBE s ↔ ∃ P : Partition G, P.IsPBEPartition ∧ P.AssociatedWith s
```

is **false** for the `Strategy` type as defined in this development.  The reason is
purely representational: a `Strategy G` carries a *total* function `σ : T → Msg → ℝ`,
but the predicate `IsPBE` (through `Supports`) only ever constrains `σ` on the type
space `Θ` and on the message space `𝓜`.  In particular the values `s.σ θ` for
`θ ∉ Θ` are completely unconstrained by `IsPBE s`.  On the other hand,
`P.toSenderStrategy.σ θ = 0` for every `θ ∉ Θ` (because `P.C t ⊆ Θ`).  Hence a PBE
strategy that is nonzero off `Θ` can never be equal to any `P.toSenderStrategy`,
so the forward implication fails.  A fully machine-checked counterexample is given
at the very bottom of this file (`namespace OriginalStatementCounterexample`).

The mathematically intended statement is recovered by adding the (entirely
natural) normalization hypothesis that `s` vanishes off `Θ` -- exactly the
property enjoyed by every `toSenderStrategy`.  This is the version proved below as
`pbe_characterization`.  The reverse implication needs no such hypothesis.
-/

open Set
open scoped Classical

namespace CPDLinear

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-
For every message there is a feasible belief minimizing the lower envelope
`v̲` over `𝓕(m)` (the *skeptical* belief).
-/
lemma pbeChar_min_vlow_feasible {m : Msg} (hm : m ∈ G.𝓜) :
    ∃ μ ∈ G.feasibleBeliefs m, IsMinOn G.vlow (G.feasibleBeliefs m) μ := by
  have h_compact : IsCompact (G.feasibleBeliefs m) := by
    exact isCompact_convex_feasibleBeliefs hm |>.1;
  have h_lower_semicontinuous : LowerSemicontinuousOn G.vlow (G.feasibleBeliefs m) := by
    exact G.vlow_lowerSemicontinuousOn.mono ( feasibleBeliefs_subset_simplex m );
  convert h_lower_semicontinuous.exists_isMinOn _ _;
  · grind +suggestions;
  · exact h_compact

/-
For `m ∈ M θ`, the inner skeptical value at `m` is at most the skeptical
payoff of `θ` (the outer maximum over `M θ`).
-/
lemma skepticalInner_le_skeptical {θ : T} {m : Msg} (hm : m ∈ G.M θ) :
    G.skepticalInner m ≤ G.skeptical θ := by
  exact le_csSup ( Set.Finite.bddAbove ( Set.Finite.image _ ( Finset.finite_toSet _ ) ) ) ( Set.mem_image_of_mem _ hm )

/-
If `ν` minimizes `v̲` over `𝓕(m)`, then `v̲(ν)` equals the inner skeptical
value `min_{μ ∈ 𝓕(m)} v̲(μ)`.
-/
lemma vlow_eq_skepticalInner_of_isMinOn {m : Msg} {ν : T → ℝ}
    (hν : ν ∈ G.feasibleBeliefs m) (hmin : IsMinOn G.vlow (G.feasibleBeliefs m) ν) :
    G.vlow ν = G.skepticalInner m := by
  have h_least : IsLeast (G.vlow '' G.feasibleBeliefs m) (G.vlow ν) := by
    exact ⟨ Set.mem_image_of_mem _ hν, Set.forall_mem_image.2 hmin ⟩;
  exact h_least.csInf_eq.symm

namespace Partition

variable (P : Partition G)

/-- **Individual rationality (Def IR).** `w_t ≥ u̲(θ)` for every `t`, `θ ∈ C_t`. -/
def IsIR : Prop := ∀ t, ∀ θ ∈ P.C t, G.skeptical θ ≤ P.w t

/-- A **PBE partition**: an IR partition with non-increasing payoffs. -/
def IsPBEPartition : Prop := P.IsIR ∧ Antitone P.w

/-- `σ` is **associated with** the partition `Π` if `σ = σ^Π`. -/
def AssociatedWith (s : Strategy G) : Prop := s = P.toSenderStrategy

/-- `σ^Π` is associated with `Π`. -/
lemma toSenderStrategy_associatedWith : P.AssociatedWith P.toSenderStrategy := rfl

/-- **Lemma strong-IR.** For non-increasing payoffs, `Π` is IR iff
`w_t ≥ max_{θ ∈ R_t} u̲(θ)` for every `t`. -/
lemma isIR_iff_sup_le (hmono : Antitone P.w) :
    P.IsIR ↔ ∀ t, ∀ θ ∈ thetaStep P.C t, G.skeptical θ ≤ P.w t := by
  classical
  constructor
  · intro hIR t θ hθ
    rw [thetaStep, Finset.mem_biUnion] at hθ
    obtain ⟨s, hs, hθs⟩ := hθ
    rw [Finset.mem_filter] at hs
    exact (hIR s θ hθs).trans (hmono hs.2)
  · intro h t θ hθ
    apply h t θ
    rw [thetaStep, Finset.mem_biUnion]
    exact ⟨t, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ t, le_refl t⟩, hθ⟩

/-
If `θ ∈ C_t` can send a message `m` that is on path at step `t'`
(`m ∈ X_{t'}`), then `w_{t'} ≤ w_t`.
-/
lemma evidence_payoff_le (hmono : Antitone P.w) {t t' : Fin P.card} {θ : T} {m : Msg}
    (hθ : θ ∈ P.C t) (hm : m ∈ G.M θ) (hmX : m ∈ P.evidence t') :
    P.w t' ≤ P.w t := by
  by_cases h_cases : t ≤ t';
  · exact hmono h_cases;
  · have h_eq : t = t' := by
      have h_eq : θ ∈ G.preimageSet ( thetaStep P.C t' ) ( P.evidence t' ) := by
        refine' Finset.mem_filter.mpr ⟨ _, _ ⟩;
        · exact Finset.mem_biUnion.mpr ⟨ t, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_of_not_ge h_cases ⟩, hθ ⟩;
        · exact ⟨ m, hm, hmX ⟩;
      have := P.exclusive t';
      exact Classical.not_not.1 fun h => Finset.disjoint_left.mp ( P.C_disjoint t t' h ) hθ ( this h_eq );
    aesop

end Partition

/-
The reverse implication of the characterization: the strategy associated with
a PBE partition is a PBE strategy.
-/
lemma isPBE_of_isPBEPartition (P : Partition G) (hP : P.IsPBEPartition) :
    G.IsPBE P.toSenderStrategy := by
  obtain ⟨hIR, hmono⟩ := hP;
  use fun m => if h : (∃ t, m ∈ P.evidence t) then P.toSenderStrategy.belief m else if hM : m ∈ G.𝓜 then (pbeChar_min_vlow_feasible hM).choose else (fun _ => 0);
  refine' ⟨ fun m => if h : ∃ t, m ∈ P.evidence t then P.w h.choose else G.skepticalInner m, _, _, _, _, _ ⟩;
  · intro m hm;
    split_ifs with h hM;
    · exact P.toSenderStrategy.belief_mem_simplex ( by simp +decide [ P.evidence_eq_iUnion, Set.mem_iUnion ] ; tauto );
    · exact ( pbeChar_min_vlow_feasible hm ).choose_spec.1 |> fun h => feasibleBeliefs_subset_simplex m h;
  · intro m hm;
    split_ifs with h;
    · exact P.toSenderStrategy.belief_mem_feasibleBeliefs ( by simpa [ P.evidence_eq_iUnion ] using h );
    · exact Classical.choose_spec ( pbeChar_min_vlow_feasible hm ) |>.1;
  · intro m hm; split_ifs <;> simp_all +decide [ Partition.evidence_eq_iUnion ] ;
  · intro m hm;
    split_ifs with h;
    · exact P.payoff_mem_V h.choose_spec;
    · have := Classical.choose_spec ( pbeChar_min_vlow_feasible hm );
      exact vlow_eq_skepticalInner_of_isMinOn this.1 this.2 ▸ vlow_mem ( feasibleBeliefs_subset_simplex m this.1 );
  · intro θ hθ m hm;
    refine' ⟨ _, fun m' hm' => _ ⟩;
    · exact P.toSenderStrategy.mem θ hθ |> fun h => simplexSupport_subset h hm;
    · by_cases h : ∃ t, m' ∈ P.evidence t <;> by_cases h' : ∃ t, m ∈ P.evidence t <;> simp +decide [ h, h' ];
      · exact P.evidence_payoff_le hmono ( P.mem_C_of_partitionStrategy_pos h'.choose_spec ( by
          exact hm ) ) hm' h.choose_spec;
      · have h_contra : m ∈ P.toSenderStrategy.evidence := by
          exact Set.mem_iUnion₂.mpr ⟨ θ, hθ, hm ⟩;
        exact False.elim ( h' ( by rw [ P.evidence_eq_iUnion ] at h_contra; exact Set.mem_iUnion.mp h_contra ) );
      · have h_skeptical_le : G.skepticalInner m' ≤ G.skeptical θ := by
          exact skepticalInner_le_skeptical hm';
        exact le_trans h_skeptical_le ( hIR _ _ ( P.mem_C_of_partitionStrategy_pos h'.choose_spec hm ) );
      · contrapose! h';
        have h_mem : m ∈ P.toSenderStrategy.evidence := by
          exact Set.mem_iUnion₂.mpr ⟨ θ, hθ, hm ⟩;
        rw [ P.evidence_eq_iUnion ] at h_mem; exact Set.mem_iUnion.mp h_mem;

/-! ## Forward implication: constructing a PBE partition from a PBE strategy

We group types by their equilibrium payoff `eqPayoff θ = max_{m ∈ M θ} r m`, sort
the (finitely many) distinct payoff values in decreasing order, and read off the
cells as the level sets.  This produces an IR partition with non-increasing
payoffs whose associated strategy is `s` (using that `s` vanishes off `Θ`).
-/

/-
The relationship between the coalition-induced belief of a restricted copy of
`s` and the full induced belief, when every type sending `m` lies inside `C`.
-/
lemma coalitionBelief_eq_belief {C : Finset T} (hne : C.Nonempty) (hsub : C ⊆ G.Θ)
    {s : Strategy G} (σC : Strategy (G.restrict C hne hsub)) (hσ : σC.σ = s.σ)
    {m : Msg} (hC : ∀ θ ∈ G.Θ, 0 < s.σ θ m → θ ∈ C) :
    σC.coalitionBelief m = s.belief m := by
  funext θ; simp [Strategy.coalitionBelief, DisclosureGame.zeroExt];
  by_cases hθ : θ ∈ G.Θ <;> simp_all +decide [ Strategy.belief ];
  · have h_onPathProb_eq : s.onPathProb m = ∑ θ' ∈ C, G.μ0 θ' * s.σ θ' m := by
      rw [ Strategy.onPathProb, ← Finset.sum_subset hsub ];
      exact fun x hx hx' => mul_eq_zero_of_right _ ( le_antisymm ( le_of_not_gt fun hx'' => hx' ( hC x hx hx'' ) ) ( s.mem x hx |>.1 m ) );
    have h_onPathProb_eq : σC.onPathProb m = (∑ θ' ∈ C, G.μ0 θ' * s.σ θ' m) / G.priorMeasure C := by
      simp +decide [ Strategy.onPathProb, hσ ];
      rw [ Finset.sum_div _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ DisclosureGame.condPrior_of_mem hx ] ; ring;
    by_cases hθC : θ ∈ C <;> simp_all +decide [ DisclosureGame.condPrior ];
    · rw [ div_mul_eq_mul_div, div_div_div_cancel_right₀ ( ne_of_gt ( G.priorMeasure_pos hne hsub ) ) ];
    · rw [ show s.σ θ m = 0 from le_antisymm ( le_of_not_gt fun h => hθC <| hC θ hθ h ) ( by exact ( s.mem θ hθ ) |>.1 _ ) ] ; ring;
  · simp +decide [ hθ, G.μ0_mem.2.2, Strategy.onPathProb ];
    exact fun h => False.elim ( hθ ( hsub h ) )

section ForwardConstruction

variable (G)

/-- The **equilibrium payoff** of type `θ`: `max_{m ∈ M θ} r m`. -/
noncomputable def eqPayoff (r : Msg → ℝ) (θ : T) : ℝ :=
  if h : (G.M θ).Nonempty then (G.M θ).sup' h r else 0

/-- The finite set of distinct equilibrium payoff values. -/
noncomputable def fwdVals (r : Msg → ℝ) : Finset ℝ := G.Θ.image (G.eqPayoff r)

/-- The payoff levels, enumerated in **decreasing** order. -/
noncomputable def fwdW (r : Msg → ℝ) (t : Fin (G.fwdVals r).card) : ℝ :=
  (G.fwdVals r).orderEmbOfFin rfl t.rev

/-- The `t`-th cell: types whose equilibrium payoff is the `t`-th level. -/
noncomputable def fwdC (r : Msg → ℝ) (t : Fin (G.fwdVals r).card) : Finset T :=
  G.Θ.filter (fun θ => G.eqPayoff r θ = G.fwdW r t)

variable {G}

/-
For `θ ∈ Θ` and `m ∈ M θ`, `r m ≤ eqPayoff θ`.
-/
lemma le_eqPayoff {r : Msg → ℝ} {θ : T} (hθ : θ ∈ G.Θ) {m : Msg} (hm : m ∈ G.M θ) :
    r m ≤ G.eqPayoff r θ := by
  unfold DisclosureGame.eqPayoff;
  split_ifs <;> [ exact Finset.le_sup' ( fun x => r x ) hm; exact absurd ( G.M_nonempty θ hθ ) ( by aesop ) ]

/-
For a message in the support of `σ(·|θ)` (with `θ ∈ Θ`), `r m = eqPayoff θ`.
-/
lemma eqPayoff_eq_of_support {s : Strategy G} {μ : Msg → T → ℝ} {r : Msg → ℝ}
    (hsup : Supports s μ r) {θ : T} (hθ : θ ∈ G.Θ) {m : Msg} (hm : 0 < s.σ θ m) :
    r m = G.eqPayoff r θ := by
  have h_sup : r m = (G.M θ).sup' (by
  exact G.M_nonempty θ hθ) r := by
    refine' le_antisymm _ _;
    · exact Finset.le_sup' ( fun x => r x ) ( by
        exact Classical.not_not.1 fun h => hm.ne' <| by simpa [ h ] using s.mem θ hθ |>.2.2 m h; );
    · exact Finset.sup'_le _ _ fun x hx => hsup.seq_optimal θ hθ ( by simpa [ Strategy.msgSupport ] using hm ) |>.2 x hx
  generalize_proofs at *;
  unfold DisclosureGame.eqPayoff; aesop;

/-
The skeptical payoff is dominated by the equilibrium payoff.
-/
lemma skeptical_le_eqPayoff {s : Strategy G} {μ : Msg → T → ℝ} {r : Msg → ℝ}
    (hsup : Supports s μ r) {θ : T} (hθ : θ ∈ G.Θ) :
    G.skeptical θ ≤ G.eqPayoff r θ := by
  apply csSup_le;
  · exact ⟨ _, Set.mem_image_of_mem _ ( G.M_nonempty θ hθ |> Classical.choose_spec ) ⟩;
  · rintro _ ⟨ m, hm, rfl ⟩;
    obtain ⟨ν, hν⟩ : ∃ ν ∈ G.feasibleBeliefs m, IsMinOn G.vlow (G.feasibleBeliefs m) ν := by
      apply pbeChar_min_vlow_feasible;
      exact G.M_subset θ hθ hm;
    have h_le_r : G.vlow ν ≤ r m := by
      apply le_trans (hν.right (hsup.feasible m (G.M_subset θ hθ hm)));
      apply G.vlow_le;
      · exact hsup.belief_system m ( G.M_subset θ hθ hm );
      · exact hsup.payoff_compat m ( G.M_subset θ hθ hm );
    exact le_trans ( vlow_eq_skepticalInner_of_isMinOn hν.1 hν.2 ▸ h_le_r ) ( le_eqPayoff hθ hm )

lemma fwdC_subset {r : Msg → ℝ} (t : Fin (G.fwdVals r).card) : G.fwdC r t ⊆ G.Θ :=
  Finset.filter_subset _ _

lemma fwdW_mem {r : Msg → ℝ} (t : Fin (G.fwdVals r).card) : G.fwdW r t ∈ G.fwdVals r := by
  convert Finset.orderEmbOfFin_mem _ _ _

lemma fwdW_strictAnti {r : Msg → ℝ} : StrictAnti (G.fwdW r) := by
  intro a b;
  convert Fin.rev_lt_rev.mpr;
  simp +decide [ DisclosureGame.fwdW ]

lemma fwdW_surjOn {r : Msg → ℝ} {x : ℝ} (hx : x ∈ G.fwdVals r) :
    ∃ t, G.fwdW r t = x := by
  obtain ⟨t, ht⟩ : ∃ t : Fin (G.fwdVals r).card, (G.fwdVals r).orderEmbOfFin rfl t = x := by
    convert Set.mem_range.mp ?_;
    simp +decide [ hx ];
  exact ⟨ t.rev, by simpa [ DisclosureGame.fwdW ] using ht ⟩

lemma fwdC_nonempty {r : Msg → ℝ} (t : Fin (G.fwdVals r).card) : (G.fwdC r t).Nonempty := by
  unfold DisclosureGame.fwdC;
  have h_exists_theta : ∃ x ∈ G.fwdVals r, x = G.fwdW r t := by
    exact ⟨ _, G.fwdW_mem t, rfl ⟩;
  obtain ⟨ x, hx, hx' ⟩ := h_exists_theta; rw [ DisclosureGame.fwdVals ] at hx; rw [ Finset.mem_image ] at hx; obtain ⟨ θ, hθ, rfl ⟩ := hx; exact ⟨ θ, by aesop ⟩ ;

lemma fwdC_disjoint {r : Msg → ℝ} (a b : Fin (G.fwdVals r).card) (hab : a ≠ b) :
    Disjoint (G.fwdC r a) (G.fwdC r b) := by
  exact Finset.disjoint_filter.mpr fun x _ hx₁ hx₂ => hab <| G.fwdW_strictAnti.injective <| hx₁.symm.trans hx₂

lemma fwdC_cover {r : Msg → ℝ} : G.Θ ⊆ Finset.univ.biUnion (G.fwdC r) := by
  intro θ hθ;
  obtain ⟨t, ht⟩ : ∃ t : Fin (G.fwdVals r).card, G.fwdW r t = G.eqPayoff r θ := by
    exact G.fwdW_surjOn ( Finset.mem_image_of_mem _ hθ );
  exact Finset.mem_biUnion.mpr ⟨ t, Finset.mem_univ _, Finset.mem_filter.mpr ⟨ hθ, ht.symm ⟩ ⟩

variable (G)

/-- The coalition strategy on the `t`-th cell: the restriction of `s`. -/
noncomputable def fwdSigma (s : Strategy G) (r : Msg → ℝ) (t : Fin (G.fwdVals r).card) :
    Strategy (G.restrict (G.fwdC r t) (fwdC_nonempty t) (fwdC_subset t)) where
  σ := s.σ
  mem := fun θ hθ => s.mem θ (fwdC_subset t hθ)

variable {G}

@[simp] lemma fwdSigma_σ (s : Strategy G) (r : Msg → ℝ) (t : Fin (G.fwdVals r).card) :
    (G.fwdSigma s r t).σ = s.σ := rfl

lemma fwd_exclusive {s : Strategy G} {μ : Msg → T → ℝ} {r : Msg → ℝ}
    (hsup : Supports s μ r) (t : Fin (G.fwdVals r).card) :
    G.preimageSet (thetaStep (G.fwdC r) t) (G.fwdSigma s r t).evidence ⊆ G.fwdC r t := by
  intro θ hθ
  simp [DisclosureGame.preimageSet, thetaStep] at hθ ⊢;
  obtain ⟨ ⟨ u, hu, hu' ⟩, m, hm ⟩ := hθ;
  obtain ⟨ θ', hθ', hθ'' ⟩ := Set.mem_iUnion₂.mp hm.2;
  have h_eqPayoff : r m = G.eqPayoff r θ' ∧ G.eqPayoff r θ' = G.fwdW r t := by
    have h_eqPayoff : r m = G.eqPayoff r θ' := by
      apply eqPayoff_eq_of_support hsup;
      · exact G.fwdC_subset t hθ';
      · exact hθ'';
    simp_all +decide [ DisclosureGame.fwdC ];
  have h_eqPayoff : G.eqPayoff r θ = G.fwdW r u ∧ G.fwdW r u ≤ G.fwdW r t := by
    exact ⟨ Finset.mem_filter.mp hu' |>.2, by exact ( G.fwdW_strictAnti.antitone hu ) ⟩;
  have h_eqPayoff : G.fwdW r u = G.fwdW r t := by
    have h_eqPayoff : r m ≤ G.eqPayoff r θ := by
      apply le_eqPayoff;
      · exact Finset.mem_filter.mp hu' |>.1;
      · exact hm.1;
    linarith;
  simp_all +decide [ DisclosureGame.fwdC ]

lemma fwd_payoff {s : Strategy G} {μ : Msg → T → ℝ} {r : Msg → ℝ}
    (hsup : Supports s μ r) (hsupp : ∀ θ ∉ G.Θ, s.σ θ = 0) (t : Fin (G.fwdVals r).card) :
    ∀ m ∈ (G.fwdSigma s r t).evidence, G.fwdW r t ∈ G.V ((G.fwdSigma s r t).coalitionBelief m) := by
  intro m hm;
  -- By `eqPayoff_eq_of_support hsup (θ'' ∈ G.Θ) (0 < s.σ θ'' m)`, `r m = G.eqPayoff r θ'' = G.fwdW r t`. (★)
  obtain ⟨θ'', hθ'', hm''⟩ : ∃ θ'' ∈ G.fwdC r t, m ∈ s.msgSupport θ'' := by
    simp_all +decide [ Strategy.evidence, Set.mem_iUnion₂ ];
    convert hm using 1;
  have h_eqPayoff : r m = G.fwdW r t := by
    convert eqPayoff_eq_of_support hsup ( G.fwdC_subset t hθ'' ) hm'' using 1;
    exact Eq.symm ( Finset.mem_filter.mp hθ'' |>.2 );
  have hCoalitionBelief : (G.fwdSigma s r t).coalitionBelief m = s.belief m := by
    apply coalitionBelief_eq_belief (fwdC_nonempty t) (fwdC_subset t) (G.fwdSigma s r t) (fwdSigma_σ s r t);
    intro θ hθ hpos
    have h_eqPayoff : r m = G.eqPayoff r θ := by
      exact eqPayoff_eq_of_support hsup hθ hpos;
    unfold DisclosureGame.fwdC; aesop;
  convert hsup.payoff_compat m _ using 1;
  · rw [ hCoalitionBelief, hsup.bayesian m ];
    exact Set.mem_iUnion₂.mpr ⟨ θ'', G.fwdC_subset t hθ'', hm'' ⟩;
  · exact h_eqPayoff.symm;
  · exact G.M_subset θ'' ( G.fwdC_subset t hθ'' ) ( by simpa using hm'' |> fun h => simplexSupport_subset ( s.mem θ'' ( G.fwdC_subset t hθ'' ) ) h )

/-- The PBE partition associated with a PBE strategy `s` (vanishing off `Θ`). -/
noncomputable def forwardPartition {s : Strategy G} {μ : Msg → T → ℝ} {r : Msg → ℝ}
    (hsup : Supports s μ r) (hsupp : ∀ θ ∉ G.Θ, s.σ θ = 0) : Partition G where
  card := (G.fwdVals r).card
  C := G.fwdC r
  C_nonempty := fwdC_nonempty
  C_disjoint := fwdC_disjoint
  C_subset := fwdC_subset
  C_cover := fwdC_cover
  σ := G.fwdSigma s r
  w := G.fwdW r
  exclusive := fwd_exclusive hsup
  payoff := fwd_payoff hsup hsupp

lemma forwardPartition_IsIR {s : Strategy G} {μ : Msg → T → ℝ} {r : Msg → ℝ}
    (hsup : Supports s μ r) (hsupp : ∀ θ ∉ G.Θ, s.σ θ = 0) :
    (forwardPartition hsup hsupp).IsIR := by
  intro t θ hθ;
  convert skeptical_le_eqPayoff hsup ( G.fwdC_subset t hθ ) using 1;
  exact Eq.symm ( Finset.mem_filter.mp hθ |>.2 )

lemma forwardPartition_associatedWith {s : Strategy G} {μ : Msg → T → ℝ} {r : Msg → ℝ}
    (hsup : Supports s μ r) (hsupp : ∀ θ ∉ G.Θ, s.σ θ = 0) :
    (forwardPartition hsup hsupp).AssociatedWith s := by
  convert Set.ext _;
  any_goals tauto;
  any_goals exact ∅;
  unfold Partition.AssociatedWith;
  simp +decide [ Partition.toSenderStrategy ];
  congr! 1;
  ext θ m;
  by_cases hθ : θ ∈ G.Θ;
  · rw [ Partition.partitionStrategy ];
    split_ifs with h;
    · exact congr_arg ( fun f => f θ m ) ( fwdSigma_σ s r h.choose ) ▸ rfl;
    · exact False.elim ( h ( by simpa using G.fwdC_cover hθ ) );
  · simp +decide [ hsupp θ hθ, Partition.partitionStrategy ];
    exact fun t ht => False.elim ( hθ ( fwdC_subset t ht ) )

end ForwardConstruction

/-- The forward implication of the characterization: a PBE strategy that vanishes
off `Θ` is associated with a PBE partition. -/
lemma exists_isPBEPartition_of_isPBE {s : Strategy G} (hsupp : ∀ θ ∉ G.Θ, s.σ θ = 0)
    (hs : G.IsPBE s) :
    ∃ P : Partition G, P.IsPBEPartition ∧ P.AssociatedWith s := by
  obtain ⟨μ, r, hsup⟩ := hs
  refine ⟨forwardPartition hsup hsupp, ⟨forwardPartition_IsIR hsup hsupp, ?_⟩,
    forwardPartition_associatedWith hsup hsupp⟩
  exact (fwdW_strictAnti).antitone

/-- **Proposition pbe-characterization.** A sender strategy that vanishes off `Θ`
is a PBE strategy iff it is associated with an IR partition with non-increasing
payoffs.

The normalization hypothesis `hsupp` is necessary: see the note at the top of this
file and `OriginalStatementCounterexample` below for why the version without it is
false. -/
theorem pbe_characterization {s : Strategy G} (hsupp : ∀ θ ∉ G.Θ, s.σ θ = 0) :
    G.IsPBE s ↔ ∃ P : Partition G, P.IsPBEPartition ∧ P.AssociatedWith s := by
  constructor
  · exact exists_isPBEPartition_of_isPBE hsupp
  · rintro ⟨P, hP, hassoc⟩
    have : s = P.toSenderStrategy := hassoc
    rw [this]
    exact isPBE_of_isPBEPartition P hP

end DisclosureGame

/-! ## Counterexample to the un-normalized statement

A fully machine-checked witness that the proposition
`G.IsPBE s ↔ ∃ P, P.IsPBEPartition ∧ P.AssociatedWith s`
fails without the normalization hypothesis `hsupp`.  We exhibit a one-type
disclosure game and a PBE strategy `sex` that is nonzero off `Θ`; it is a PBE,
yet no partition is associated with it.
-/
namespace OriginalStatementCounterexample

open DisclosureGame Set

/-- A minimal disclosure game: `T = Bool`, `Msg = Unit`, `Θ = {true}`, `V ≡ {0}`. -/
noncomputable def Gex : DisclosureGame Bool Unit where
  Θ := {true}
  𝓜 := {()}
  Θ_nonempty := ⟨true, by decide⟩
  𝓜_nonempty := ⟨(), by decide⟩
  M := fun _ => {()}
  M_subset := by intro θ hθ x hx; simp_all
  M_nonempty := by intro θ hθ; exact ⟨(), by decide⟩
  cover := by ext x; simp
  μ0 := fun b => if b then 1 else 0
  μ0_mem := by
    refine ⟨?_, ?_, ?_⟩
    · intro a; cases a <;> norm_num
    · simp
    · intro a ha; cases a <;> simp_all
  μ0_fullSupport := by intro θ hθ; simp at hθ; subst hθ; norm_num
  V := fun _ => {0}
  V_nonempty := by intro μ hμ; exact ⟨0, rfl⟩
  V_isCompact := by intro μ hμ; exact isCompact_singleton
  V_ordConnected := by intro μ hμ; exact ordConnected_singleton
  V_uhc := by intro μ hμ U hU hsub; exact ⟨univ, Filter.univ_mem, fun μ' _ => hsub⟩

/-- A PBE strategy that behaves like `δ` at the on-path type `true`, but is
nonzero off `Θ` (at `false`). -/
noncomputable def sex : Strategy Gex where
  σ := fun θ _ => if θ then 1 else 7
  mem := by
    intro θ hθ
    simp only [Gex, Finset.mem_singleton] at hθ
    subst hθ
    refine ⟨?_, ?_, ?_⟩
    · intro a; simp
    · simp
    · intro a ha; rw [Subsingleton.elim a ()] at ha; exact absurd (by simp [Gex]) ha

/-- `sex` is genuinely a PBE (proved without appealing to any sorried lemma). -/
theorem sex_isPBE : Gex.IsPBE sex := by
  have hev : () ∈ sex.evidence := by
    rw [Strategy.evidence, Set.mem_iUnion₂]
    exact ⟨true, by simp [Gex], by simp [Strategy.msgSupport, simplexSupport, sex]⟩
  have hop : sex.onPathProb () = 1 := by
    simp [Strategy.onPathProb, Gex, sex, Finset.sum_singleton]
  have hbel : sex.belief () = fun b => if b then (1:ℝ) else 0 := by
    funext b
    simp only [Strategy.belief, hop]
    cases b <;> simp [Gex, sex]
  refine ⟨sex.belief, fun _ => 0, ?_⟩
  refine { belief_system := ?_, feasible := ?_, bayesian := ?_,
           payoff_compat := ?_, seq_optimal := ?_ }
  · intro m hm
    rw [show m = () from rfl, hbel]
    refine ⟨?_, ?_, ?_⟩
    · intro a; cases a <;> norm_num
    · simp
    · intro a ha; cases a <;> simp_all [Gex]
  · intro m hm
    rw [show m = () from rfl]
    exact ⟨sex, hev, rfl⟩
  · intro m hm; rfl
  · intro m hm; show (0:ℝ) ∈ Gex.V _; exact rfl
  · intro θ hθ m hm
    refine ⟨by rw [show m = () from rfl]; simp [Gex], ?_⟩
    intro m' hm'; exact le_refl (0:ℝ)

/-- Yet no partition is associated with `sex`, because `toSenderStrategy` is `0`
off `Θ` while `sex.σ false () = 7`. -/
theorem no_partition_associated : ¬ ∃ P : Partition Gex, P.AssociatedWith sex := by
  rintro ⟨P, hP⟩
  have hneg : ¬ ∃ t, false ∈ P.C t := by
    rintro ⟨t, ht⟩; have := P.C_subset t ht; simp [Gex] at this
  have hps : P.toSenderStrategy.σ false () = 0 := by
    change P.partitionStrategy false () = 0
    simp only [Partition.partitionStrategy]
    exact dif_neg hneg
  have h1 : sex.σ false () = 0 := by rw [hP]; exact hps
  have h7 : sex.σ false () = 7 := rfl
  rw [h7] at h1; norm_num at h1

/-- Therefore the un-normalized biconditional is false. -/
theorem original_statement_false :
    ¬ (∀ s : Strategy Gex,
        Gex.IsPBE s ↔ ∃ P : Partition Gex, P.IsPBEPartition ∧ P.AssociatedWith s) := by
  intro h
  obtain ⟨P, _, hassoc⟩ := (h sex).mp sex_isPBE
  exact no_partition_associated ⟨P, hassoc⟩

end OriginalStatementCounterexample

end CPDLinear