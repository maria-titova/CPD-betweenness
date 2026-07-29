import CPDLinear.Theorem3
import CPDLinear.Theorem1

/-!
# Betweenness  (writeup §7, `sec:betweenness`)

The upper envelope `v̄` satisfies **betweenness** (B) if for all beliefs
`μ, μ'` and `λ ∈ (0,1)` the value `v̄(λμ + (1-λ)μ')` lies between `v̄(μ)` and
`v̄(μ')`; it satisfies **strict betweenness** (B*) if, in addition, the value is
*strictly* between whenever `v̄(μ) ≠ v̄(μ')`.

The main result (`thm:betweenness-coe`) is that strict betweenness guarantees a
COE partition (hence a coalition-proof PBE).  Because B* implies quasiconcavity,
this is the QC existence theory specialized to strict betweenness; it is proved
under message completeness (M-C), the standing assumption of this existence
chapter (the same assumption used by Theorems 1 and 3).  See `betweenness_coe`
and `betweenness_max_cell` for the precise role of M-C.

This file also develops message-completeness-free infrastructure
(`merge_equal_payoff`, the betweenness ceiling `vbar_condPrior_le_max_dirac`,
etc.) that may be reused elsewhere.
-/

open Set Topology
open scoped Classical

namespace CPDLinear

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-! ## Definitions: betweenness and strict betweenness -/

variable (G) in
/-- **(B)** `v̄` satisfies *betweenness*: for all `μ, μ' ∈ ΔΘ` and `λ ∈ (0,1)`,
`v̄(λμ + (1-λ)μ')` lies between `v̄(μ)` and `v̄(μ')`. -/
def Betweenness : Prop :=
  ∀ μ ∈ simplexOn G.Θ, ∀ μ' ∈ simplexOn G.Θ, ∀ l : ℝ, l ∈ Set.Ioo (0 : ℝ) 1 →
    min (G.vbar μ) (G.vbar μ') ≤ G.vbar (fun θ => l * μ θ + (1 - l) * μ' θ) ∧
      G.vbar (fun θ => l * μ θ + (1 - l) * μ' θ) ≤ max (G.vbar μ) (G.vbar μ')

variable (G) in
/-- **(B*)** `v̄` satisfies *strict betweenness*: it satisfies B and the value is
strictly between `v̄(μ)` and `v̄(μ')` whenever `v̄(μ) ≠ v̄(μ')`. -/
def StrictBetweenness : Prop :=
  G.Betweenness ∧
    ∀ μ ∈ simplexOn G.Θ, ∀ μ' ∈ simplexOn G.Θ, G.vbar μ ≠ G.vbar μ' →
      ∀ l : ℝ, l ∈ Set.Ioo (0 : ℝ) 1 →
        min (G.vbar μ) (G.vbar μ') < G.vbar (fun θ => l * μ θ + (1 - l) * μ' θ) ∧
          G.vbar (fun θ => l * μ θ + (1 - l) * μ' θ) < max (G.vbar μ) (G.vbar μ')

/-! ## Elementary consequences -/

/-- The lower inequality of betweenness is exactly quasiconcavity. -/
lemma Betweenness.qc (hB : G.Betweenness) : G.QC := by
  intro μ hμ μ' hμ' l hl
  exact (hB μ hμ μ' hμ' l hl).1

/-- Strict betweenness implies quasiconcavity. -/
lemma StrictBetweenness.qc (hB : G.StrictBetweenness) : G.QC :=
  hB.1.qc

/-- Betweenness is inherited by restricted games. -/
lemma restrict_Betweenness {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    (hB : G.Betweenness) : (G.restrict S hne hsub).Betweenness := by
  intro μ hμ μ' hμ' l hl
  exact hB μ (simplexOn_mono hsub hμ) μ' (simplexOn_mono hsub hμ') l hl

/-- Strict betweenness is inherited by restricted games. -/
lemma restrict_StrictBetweenness {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    (hB : G.StrictBetweenness) : (G.restrict S hne hsub).StrictBetweenness := by
  refine ⟨restrict_Betweenness hne hsub hB.1, ?_⟩
  intro μ hμ μ' hμ' hne' l hl
  exact hB.2 μ (simplexOn_mono hsub hμ) μ' (simplexOn_mono hsub hμ') hne' l hl

/-- Under quasiconcavity, the quasiconcave closure of `v̄` agrees with `v̄` on the
simplex (since `v̄` is then already upper semicontinuous and quasiconcave). -/
lemma qcClosure_eq_vbar_of_QC (hQC : G.QC) {μ : T → ℝ} (hμ : μ ∈ simplexOn G.Θ) :
    G.qcClosure μ = G.vbar μ := by
  refine le_antisymm ?_ (t3_vbar_le_qcClosure hμ)
  have hconv : Convex ℝ (G.vbarUpperLevel (G.qcClosure μ)) :=
    vbar_superlevel_convex hQC (G.qcClosure μ)
  have hmem : μ ∈ {ν | ν ∈ simplexOn G.Θ ∧ G.qcClosure μ ≤ G.qcClosure ν} := ⟨hμ, le_refl _⟩
  rw [qcClosure_superlevel_eq_convexHull] at hmem
  rw [hconv.convexHull_eq] at hmem
  exact hmem.2

/-- **MC-free pooling bound.** Under quasiconcavity, every coalition `(C, σ, w)`
of a restricted game satisfies `w ≤ v̄(μ⁰_C)`. -/
lemma coalition_w_le_vbar_condPrior (hQC : G.QC) {R : Finset T} (hne : R.Nonempty)
    (hsub : R ⊆ G.Θ) (K : Coalition (G.restrict R hne hsub)) :
    K.w ≤ G.vbar (G.condPrior K.C) := by
  have h := coalition_w_le_qcClosure hne hsub K
  have hmem : G.condPrior K.C ∈ simplexOn G.Θ :=
    simplexOn_mono (K.C_subset.trans hsub)
      (G.condPrior_mem_simplex K.C_nonempty (K.C_subset.trans hsub))
  rwa [qcClosure_eq_vbar_of_QC hQC hmem] at h

/-! ## MC-free merging of equal-payoff coalitions -/

/-
**Restricted coalition belief, in terms of the full prior.** For a strategy
`s` of a restricted game `G|_S`, the (zero-extended) coalition belief after a
message `m` is the Bayesian posterior computed directly with the *full* prior
`G.μ0`; the `priorMeasure S` normalizer cancels between numerator and
denominator.
-/
lemma restrict_coalitionBelief_eq {S : Finset T} (hne : S.Nonempty) (hsub : S ⊆ G.Θ)
    (s : Strategy (G.restrict S hne hsub)) (m : Msg) (θ : T) :
    s.coalitionBelief m θ
      = if θ ∈ S then G.μ0 θ * s.σ θ m / (∑ θ' ∈ S, G.μ0 θ' * s.σ θ' m) else 0 := by
  by_cases hθ : θ ∈ S <;> simp +decide [ hθ, Strategy.coalitionBelief ];
  · simp +decide [ zeroExt, Strategy.belief, Strategy.onPathProb, condPrior_of_mem hθ, priorMeasure_pos hne hsub, ne_of_gt ];
    rw [ if_pos hθ, div_mul_eq_mul_div, div_div ];
    rw [ Finset.mul_sum _ _ _ ];
    exact congr_arg _ ( Finset.sum_congr rfl fun x hx => by rw [ condPrior_of_mem hx ] ; rw [ div_mul_eq_mul_div, mul_div_assoc', mul_div_cancel_left₀ _ ( ne_of_gt ( priorMeasure_pos hne hsub ) ) ] );
  · exact if_neg hθ

/-
The evidence sets of two coalitions on disjoint cells are disjoint.
-/
lemma merge_evidence_disjoint (H : DisclosureGame T Msg)
    (K K' : H.Coalition) (hdisj : Disjoint K.C K'.C) :
    Disjoint K.σ.evidence K'.σ.evidence := by
  rw [ Set.disjoint_left ];
  intro m hm hm';
  -- Since $m$ is in both $K.σ.evidence$ and $K'.σ.evidence$, there exist $\theta \in K.C$ and $\theta' \in K'.C$ such that $m \in K.σ.msgSupport \theta$ and $m \in K'.σ.msgSupport \theta'$.
  obtain ⟨θ, hθK, hθm⟩ : ∃ θ ∈ K.C, m ∈ K.σ.msgSupport θ := by
    simp_all +decide [ Strategy.evidence, Strategy.msgSupport ]
  obtain ⟨θ', hθ'K', hθ'm⟩ : ∃ θ' ∈ K'.C, m ∈ K'.σ.msgSupport θ' := by
    simp_all +decide [ Strategy.evidence, Strategy.msgSupport ];
  -- Since θ can send m, we have θ ∈ H.preimageSetFull {m}.
  have hθ_preimage : θ ∈ H.preimageSetFull K'.σ.evidence := by
    have hθm' : θ ∈ H.preimageSetFull {m} := by
      simp_all +decide [ Strategy.msgSupport, mem_preimageSet, DisclosureGame.preimageSetFull, DisclosureGame.canSend, mem_simplexSupport ];
      have := K.σ.mem θ (by
      exact Finset.mem_coe.mpr hθK);
      simp_all +decide [ DisclosureGame.restrict, DisclosureGame.M ];
      exact ⟨ K.C_subset hθK, Classical.not_not.1 fun h => hθm.ne' <| this.2.2 m h ⟩;
    simp_all +decide [ DisclosureGame.preimageSetFull, DisclosureGame.preimageSet ];
    exact ⟨ m, hθm'.2, hm' ⟩;
  exact Finset.disjoint_left.mp hdisj hθK ( K'.exclusive hθ_preimage )

/-
Belief equality for the merged strategy, on `K`'s messages.
-/
lemma merge_belief_left (H : DisclosureGame T Msg)
    (K K' : H.Coalition) (hdisj : Disjoint K.C K'.C)
    {hCne : (K.C ∪ K'.C).Nonempty} {hCsub : (K.C ∪ K'.C) ⊆ H.Θ}
    (σt : Strategy (H.restrict (K.C ∪ K'.C) hCne hCsub))
    (hσt : ∀ θ m, σt.σ θ m = if θ ∈ K.C then K.σ.σ θ m else K'.σ.σ θ m)
    (m : Msg) (hm : m ∈ K.σ.evidence) :
    σt.coalitionBelief m = K.σ.coalitionBelief m := by
  -- By definition of $σt$, we know that for any message $m$, $σt.coalitionBelief m = K.σ.coalitionBelief m$ if $m$ is in $K.σ.evidence$.
  have h_eq : ∀ θ, σt.coalitionBelief m θ = K.σ.coalitionBelief m θ := by
    -- Since K and K' are disjoint, and m is in K's evidence, K' can't send m. Therefore, for any θ in K', K'.σ.σ θ m must be zero.
    have hK'_zero : ∀ θ ∈ K'.C, K'.σ.σ θ m = 0 := by
      intro θ hθ
      by_contra h_nonzero;
      have hK'_zero : m ∈ K'.σ.evidence := by
        exact Set.mem_iUnion₂.2 ⟨ θ, by
          exact hθ, by
          exact mem_simplexSupport.2 ( lt_of_le_of_ne ( K'.σ.mem θ |> fun h => by
            exact h ( by simpa using hθ ) |> fun h => h.1 m ) ( Ne.symm h_nonzero ) ) ⟩;
      exact absurd ( merge_evidence_disjoint H K K' hdisj ) ( Set.not_disjoint_iff.mpr ⟨ m, hm, hK'_zero ⟩ );
    intro θ
    rw [restrict_coalitionBelief_eq, restrict_coalitionBelief_eq];
    split_ifs <;> simp_all +decide [ Finset.sum_union hdisj ];
    rw [ Finset.inter_comm, Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.sum_empty, add_zero ];
  exact funext h_eq

/-
Belief equality for the merged strategy, on `K'`'s messages.
-/
lemma merge_belief_right (H : DisclosureGame T Msg)
    (K K' : H.Coalition) (hdisj : Disjoint K.C K'.C)
    {hCne : (K.C ∪ K'.C).Nonempty} {hCsub : (K.C ∪ K'.C) ⊆ H.Θ}
    (σt : Strategy (H.restrict (K.C ∪ K'.C) hCne hCsub))
    (hσt : ∀ θ m, σt.σ θ m = if θ ∈ K.C then K.σ.σ θ m else K'.σ.σ θ m)
    (m : Msg) (hm : m ∈ K'.σ.evidence) :
    σt.coalitionBelief m = K'.σ.coalitionBelief m := by
  apply funext; intro θ; exact (by
    have :=DisclosureGame.restrict_coalitionBelief_eq (hne := hCne) (hsub := hCsub) σt m θ;
    have :=DisclosureGame.restrict_coalitionBelief_eq (hne := by
      grind) (hsub := by
      exact fun x hx => hCsub ( Finset.mem_union_right _ hx )) K'.σ m θ;
    have hden : ∑ θ' ∈ K.C ∪ K'.C, H.μ0 θ' * σt.σ θ' m = ∑ θ' ∈ K'.C, H.μ0 θ' * K'.σ.σ θ' m := by
      have hden : ∀ θ' ∈ K.C, K.σ.σ θ' m = 0 := by
        intro θ' hθ'
        have h_not_in_K : m ∉ K.σ.evidence := by
          exact fun h => Set.disjoint_right.mp ( DisclosureGame.merge_evidence_disjoint H K K' hdisj ) hm h;
        contrapose! h_not_in_K;
        exact Set.mem_iUnion₂.mpr ⟨ θ', by
          exact hθ', by
          exact Set.mem_setOf.mpr ( lt_of_le_of_ne ( K.σ.mem θ' ( by
            exact hθ' ) |>.1 m ) ( Ne.symm h_not_in_K ) ) ⟩;
      rw [ Finset.sum_union hdisj ];
      rw [ Finset.sum_eq_zero ] <;> simp +contextual [ * ];
      exact Finset.sum_congr rfl fun x hx => if_neg ( Finset.disjoint_right.mp hdisj hx );
    by_cases hθ : θ ∈ K.C <;> simp_all +decide [ Finset.disjoint_left.mp hdisj ];
    have h_zero : m ∉ K.σ.evidence := by
      exact fun h => Set.disjoint_right.mp ( DisclosureGame.merge_evidence_disjoint H K K' hdisj ) hm h;
    contrapose! h_zero;
    rw [ Strategy.evidence ];
    simp +decide [ Strategy.msgSupport, hθ ];
    exact ⟨ θ, hθ, lt_of_le_of_ne ( K.σ.mem θ |> fun h => by
      exact h ( by simpa using hθ ) |> fun h => h.1 m ) ( Ne.symm h_zero.1.2 ) ⟩)

/-
**MC-free merging of equal-payoff coalitions.** If `K` and `K'` are two
coalitions of a disclosure game `H` on **disjoint** cells that share the **same**
common payoff `w`, then there is a coalition on the union `K.C ∪ K'.C` with that
same payoff.

This is the key construction that lets the betweenness existence argument run
*without message completeness*: rather than pooling the union into a single
message (which would require completeness), we keep each cell's own messages and
use the *common* payoff `w` shared by both coalitions.  The combined sender
strategy plays `K.σ` on `K.C` and `K'.σ` on `K'.C`; the two evidence sets are
automatically disjoint (a message in both evidences would be sendable by a type
in `K.C ∩ K'.C = ∅`), so after every on-path message the induced belief is the
belief of exactly one of the two coalitions, where `w` is a valid payoff.
-/
lemma merge_equal_payoff (H : DisclosureGame T Msg)
    (K K' : H.Coalition) (hdisj : Disjoint K.C K'.C) (hw : K.w = K'.w) :
    ∃ Kt : H.Coalition, Kt.C = K.C ∪ K'.C ∧ Kt.w = K.w := by
  have h_merge_evidence_disjoint : Disjoint K.σ.evidence K'.σ.evidence := by
    apply merge_evidence_disjoint H K K' hdisj;
  obtain ⟨σt, hσt⟩ : ∃ σt : Strategy (H.restrict (K.C ∪ K'.C) (by
  exact ⟨ _, Finset.mem_union_left _ ( K.C_nonempty.choose_spec ) ⟩) (by
  exact Finset.union_subset K.C_subset K'.C_subset)), (∀ θ m, σt.σ θ m = if θ ∈ K.C then K.σ.σ θ m else K'.σ.σ θ m) := by
    refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
    use fun θ m => if θ ∈ K.C then K.σ.σ θ m else K'.σ.σ θ m;
    all_goals simp +decide [ simplexOn ];
    intro θ hθ; split_ifs <;> simp_all +decide [ Strategy.mem ] ;
    · have := K.σ.mem θ ‹_›; simp_all +decide [ DisclosureGame.restrict_M ] ;
    · have := K'.σ.mem θ hθ; simp_all +decide [ Strategy.mem ] ;
  generalize_proofs at *;
  refine' ⟨ ⟨ K.C ∪ K'.C, _, _, σt, _, K.w, _ ⟩, rfl, rfl ⟩ <;> simp_all +decide [ Finset.disjoint_left ];
  · intro θ hθ
    have hθ_in_K_or_K' : θ ∈ H.preimageSetFull K.σ.evidence ∨ θ ∈ H.preimageSetFull K'.σ.evidence := by
      unfold DisclosureGame.preimageSetFull at *; simp_all +decide [ Finset.disjoint_left, Set.disjoint_left ] ;
      unfold Strategy.evidence at *; simp_all +decide [ Finset.ext_iff, Set.ext_iff, DisclosureGame.preimageSet ] ;
      simp_all +decide [ Set.Nonempty, Set.mem_inter_iff, Set.mem_iUnion ];
      rcases hθ.2 with ⟨ m, hm, i, hi, hi' ⟩ ; cases hi <;> simp_all +decide [ Strategy.msgSupport ] ;
      · exact Or.inl ⟨ m, hm, i, by assumption, hi' ⟩;
      · grind
    generalize_proofs at *;
    exact hθ_in_K_or_K'.elim ( fun h => Finset.mem_union_left _ ( K.exclusive h ) ) fun h => Finset.mem_union_right _ ( K'.exclusive h );
  · intro m hm
    have h_m_in_evidence : m ∈ K.σ.evidence ∨ m ∈ K'.σ.evidence := by
      simp_all +decide [ Strategy.evidence, mem_simplexSupport ];
      simp_all +decide [ Strategy.msgSupport, mem_simplexSupport ];
      grind +qlia
    generalize_proofs at *;
    grind +suggestions

/-! ## The betweenness ceiling -/

/-
**Betweenness ceiling (dirac form).** Iterating the *upper* betweenness
inequality over the convex decomposition `μ⁰_C = ∑_{θ∈C} (μ⁰θ/μ⁰C) δ_θ`, the
upper-envelope value at the conditional prior of any cell `C` is bounded by the
largest full-revelation value `v̄(δ_θ)` over `θ ∈ C`.  (Here `δ_θ = condPrior {θ}`.)
No message completeness is used — only betweenness of `v̄`.
-/
lemma vbar_condPrior_le_max_dirac (hB : G.Betweenness) :
    ∀ {C : Finset T}, C.Nonempty → C ⊆ G.Θ →
      ∃ θ ∈ C, G.vbar (G.condPrior C) ≤ G.vbar (G.condPrior {θ}) := by
  intro C hCne hCsub; induction' hn : C.card using Nat.strong_induction_on with n ih generalizing C; rcases n with ( _ | _ | n ) ; simp_all +decide [ Finset.card_eq_one ] ;
  · obtain ⟨ θ, hθ ⟩ := Finset.card_eq_one.mp hn; use θ; aesop;
  · obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ ∈ C, ∃ D : Finset T, D = C.erase θ₀ ∧ D.Nonempty ∧ D ⊆ G.Θ ∧ Disjoint {θ₀} D ∧ C = {θ₀} ∪ D := by
      obtain ⟨ θ₀, hθ₀ ⟩ := hCne; use θ₀, hθ₀; use C.erase θ₀; simp +decide [ Finset.subset_iff, hCsub, hθ₀ ] ;
      exact ⟨ ⟨ θ₀, hθ₀, by obtain ⟨ x, hx ⟩ := Finset.exists_mem_ne ( by linarith ) θ₀; exact ⟨ x, hx.1, hx.2.symm ⟩ ⟩, fun x hx₁ hx₂ => hCsub hx₂ ⟩;
    obtain ⟨D, hD₁, hD₂, hD₃, hD₄, hD₅⟩ := hθ₀.right
    obtain ⟨l, hl⟩ : ∃ l ∈ Set.Ioo (0 : ℝ) 1, G.condPrior C = fun θ => l * G.condPrior {θ₀} θ + (1 - l) * G.condPrior D θ := by
      have h_condPrior : G.condPrior C = fun θ => (G.condPrior {θ₀} θ * (G.μ0 θ₀) + G.condPrior D θ * (∑ θ' ∈ D, G.μ0 θ')) / (G.μ0 θ₀ + ∑ θ' ∈ D, G.μ0 θ') := by
        ext θ; simp +decide [ hD₅, DisclosureGame.condPrior ] ; ring;
        by_cases hθ : θ = θ₀ <;> by_cases hθ' : θ ∈ D <;> simp +decide [ hθ, hθ', DisclosureGame.priorMeasure ];
        · grind;
        · rw [ Finset.sum_insert ] <;> simp +decide [ hθ, hθ', Finset.disjoint_singleton_left.mp hD₄ ];
        · rw [ Finset.sum_insert ( Finset.disjoint_singleton_left.mp hD₄ ) ] ; ring;
          simp +decide [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( show 0 < ∑ x ∈ D, G.μ0 x from Finset.sum_pos ( fun x hx => G.μ0_fullSupport x ( hD₃ hx ) ) hD₂ ) ];
      refine' ⟨ G.μ0 θ₀ / ( G.μ0 θ₀ + ∑ θ' ∈ D, G.μ0 θ' ), _, _ ⟩;
      · refine' ⟨ div_pos _ _, div_lt_one _ |>.2 _ ⟩;
        · exact G.μ0_fullSupport θ₀ ( hCsub hθ₀.1 );
        · exact add_pos_of_pos_of_nonneg ( G.μ0_fullSupport θ₀ ( hCsub hθ₀.1 ) ) ( Finset.sum_nonneg fun _ _ => G.μ0_mem.1 _ );
        · exact add_pos_of_pos_of_nonneg ( G.μ0_fullSupport θ₀ ( hCsub hθ₀.1 ) ) ( Finset.sum_nonneg fun _ _ => le_of_lt ( G.μ0_fullSupport _ ( hD₃ ‹_› ) ) );
        · exact lt_add_of_pos_right _ ( Finset.sum_pos ( fun x hx => G.μ0_fullSupport x ( hD₃ hx ) ) hD₂ );
      · convert h_condPrior using 2 ; ring;
        field_simp;
        rw [ div_add', div_eq_div_iff ] <;> ring <;> norm_num [ G.μ0_fullSupport ]; all_goals exact ne_of_gt ( add_pos_of_pos_of_nonneg ( G.μ0_fullSupport θ₀ ( hCsub hθ₀.1 ) ) ( Finset.sum_nonneg fun _ _ => le_of_lt ( G.μ0_fullSupport _ ( hD₃ ‹_› ) ) ) );
    have h_betweenness : G.vbar (G.condPrior C) ≤ max (G.vbar (G.condPrior {θ₀})) (G.vbar (G.condPrior D)) := by
      have := hB ( G.condPrior { θ₀ } ) ( by
        exact simplexOn_mono ( Finset.singleton_subset_iff.mpr ( hCsub hθ₀.1 ) ) ( condPrior_mem_simplex ( Finset.singleton_nonempty _ ) ( Finset.singleton_subset_iff.mpr ( hCsub hθ₀.1 ) ) ) ) ( G.condPrior D ) ( by
        exact simplexOn_mono hD₃ ( condPrior_mem_simplex hD₂ hD₃ ) ) l hl.1
      generalize_proofs at *;
      simpa only [ ← hl.2 ] using this.2;
    grind

/-- **Betweenness ceiling for coalition payoffs.** Every coalition payoff is
bounded by the largest full-revelation value `v̄(δ_θ)` over the types `θ` in its
cell.  Combines `coalition_w_le_vbar_condPrior` (QC) with the ceiling. -/
lemma coalition_w_le_max_dirac (hB : G.Betweenness) {R : Finset T} (hne : R.Nonempty)
    (hsub : R ⊆ G.Θ) (K : Coalition (G.restrict R hne hsub)) :
    ∃ θ ∈ K.C, K.w ≤ G.vbar (G.condPrior {θ}) := by
  obtain ⟨θ, hθC, hθ⟩ := vbar_condPrior_le_max_dirac hB K.C_nonempty (K.C_subset.trans hsub)
  exact ⟨θ, hθC, (coalition_w_le_vbar_condPrior hB.qc hne hsub K).trans hθ⟩

/-! ## The maximal-cell lemma -/

/-- **Maximal cell under strict betweenness.** There is a coalition attaining the
greatest coalition payoff whose removal does not raise the greatest coalition
payoff on the residual types.

This is the betweenness specialization of `exists_max_cell`.  Strict betweenness
implies quasiconcavity (`StrictBetweenness.qc`), and under quasiconcavity and
message completeness `exists_max_cell` provides exactly this maximal cell.

*On the role of message completeness.*  This lemma is proved here under message
completeness (M-C), the standing assumption of this existence chapter (it is what
Theorems 1 and 3 use), and the betweenness theorem is obtained through the same
merging machinery.  The by-contradiction argument behind `exists_max_cell`
chooses, among the coalitions attaining the greatest payoff `w*`, one whose cell
`K.C` has maximal cardinality; if removing `K.C` left a residual coalition paying
strictly more than `w*`, the `merging` lemma combines the two cells into a
strictly larger coalition still attaining `w*`, contradicting maximality.  With
M-C the merged cell is realized as a *single* pooled message.

*Can M-C be dropped here?*  The literal `thm:betweenness-coe` carries no M-C
hypothesis, and it appears to remain **true** without M-C: even with an
incomplete message structure, the value `v̄(μ⁰_{K.C ∪ D_R})` of a merged cell can
still be realized as a coalition payoff by a *value-equalizing* mixed strategy,
in which a "bridge" type that lies in `K.C` and can also send the residual
message splits its message probabilities so that every induced belief carries the
same value (this is what lets the would-be counterexamples collapse: the merged
cell is achievable even though no single message pools it).  Carrying this out
formally amounts to re-deriving the merging / pooling-realization machinery
(`merging`, `pooling_coalition`) without M-C, which is **not** done here; the
M-C-free proof is left open.  The MC-free merging of *equal-payoff* coalitions on
disjoint cells (`merge_equal_payoff`) is available as partial infrastructure. -/
lemma betweenness_max_cell (H : DisclosureGame T Msg)
    (hB : H.StrictBetweenness) (hMC : H.MC) :
    ∃ K : H.Coalition, IsGreatest H.coalitionPayoffs K.w ∧
      ∀ (hne : (H.Θ \ K.C).Nonempty) (hsub : (H.Θ \ K.C) ⊆ H.Θ) (w' : ℝ),
        IsGreatest (H.restrict (H.Θ \ K.C) hne hsub).coalitionPayoffs w' → w' ≤ K.w :=
  exists_max_cell H hB.qc hMC

/-! ## Existence of a COE partition -/

/-- **Existence of a COE partition under strict betweenness**, by induction on
`|Θ|` using the maximal-cell lemma.  Message completeness is threaded through the
induction via `restrict_MC`. -/
private lemma betweenness_exists_coe (H : DisclosureGame T Msg)
    (hB : H.StrictBetweenness) (hMC : H.MC) :
    ∃ P : Partition H, P.IsCOE := by
  induction' n : H.Θ.card using Nat.strong_induction_on with k ih generalizing H
  obtain ⟨K, hKmax, hbound⟩ := betweenness_max_cell H hB hMC
  by_cases hempty : H.Θ \ K.C = ∅
  · exact t3_single_cell_coe H K hempty hKmax
  · obtain ⟨hne, hsub⟩ : (H.Θ \ K.C).Nonempty ∧ (H.Θ \ K.C) ⊆ H.Θ :=
      ⟨Finset.nonempty_of_ne_empty hempty, Finset.sdiff_subset⟩
    have hcard : (H.restrict (H.Θ \ K.C) hne hsub).Θ.card < k := by
      convert Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩) using 1
      · exact n.symm
      · simp_all +decide [Finset.ext_iff]
        exact Finset.not_disjoint_iff.mpr
          ⟨_, Finset.mem_of_subset K.C_subset K.C_nonempty.choose_spec, K.C_nonempty.choose_spec⟩
    exact ih _ hcard _ (restrict_StrictBetweenness hne hsub hB) (restrict_MC hne hsub hMC) rfl
      |> fun ⟨P, hP⟩ => t3_prepend_coe H K hKmax hne hsub (hbound hne hsub) P hP

/-- **Theorem (`thm:betweenness-coe`).** If `v̄` satisfies strict betweenness
(B*), then `G` admits a COE partition.

The theorem is stated and proved under message completeness (`hMC`), the standing
assumption of this existence chapter (it is what Theorems 1 and 3 use).  Since
B* implies quasiconcavity, this is the QC + M-C existence result specialized to
strict betweenness.  See `betweenness_max_cell` for why message completeness
cannot be dropped by the present merging argument. -/
theorem betweenness_coe (hB : G.StrictBetweenness) (hMC : G.MC) :
    ∃ P : Partition G, P.IsCOE :=
  betweenness_exists_coe G hB hMC

/-- A coalition-proof PBE partition exists under strict betweenness (and message
completeness, the chapter's standing assumption). -/
theorem betweenness_existence (hB : G.StrictBetweenness) (hMC : G.MC) :
    ∃ P : Partition G, P.IsCPPBEPartition := by
  obtain ⟨P, hP⟩ := betweenness_coe hB hMC
  exact ⟨P, hP.isCPPBEPartition⟩

end DisclosureGame

end CPDLinear