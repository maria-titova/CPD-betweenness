import CPDLinear.CheapTalk
import CPDLinear.BetweennessGeneric
import CPDLinear.BetweennessCTAux

/-!
# Cheap-talk invariance of betweenness (working-paper appendix)

**Working-paper remark (cheap-talk invariance).** Under single-valued `V` and
betweenness (B), the coalition-proof predictions are insensitive to cheap
talk. We model "adjoining to every message as many copies as there are
states" by the **cheap-talk augmentation** `ctAugment`: the message space
becomes `𝓜 ×ˢ Θ` (each `m` replaced by the `|Θ|` copies `(m, s)`, `s ∈ Θ`, all
sharing `m`'s preimage). All belief-side data (`Θ`, `μ⁰`, `V`, hence `v̄` and
`condPrior`) is untouched, so the augmented game is a disclosure game
satisfying **cheap-talk copies (M-CT, Definition 15)**, and every relative
preimage — hence `v*(R)` and `max 𝒲_R` — is preserved. (Feasible-belief sets
and skeptical payoffs are *not* preserved: the `|Θ|`-copies augmentation
makes every message-set non-singleton, dropping the forcing constraints; only
the preimage-based quantities are cheap-talk invariant — see the remark
before `ctAugment_vstar_eq`.)

* `ctAugment` — the augmented game over `Msg × T`.
* `ctAugment_mct` — the augmented game satisfies M-CT (Definition 15).
* `ctAugment_vstar_eq` — the top pooling value `v*(R)` (hence `max 𝒲_R`) is
  unchanged.
* `btw_ct_correspondence` — under single-valued `V`, B, and genericity, the
  coalition-proof PBE partitions of `G` and of its cheap-talk augmentation
  coincide cell by cell, with equal payoffs.

The augmented game inherits `SingleValued`/`Betweenness`/`Generic` from `G`
definitionally (`v̄`, `Θ`, `μ⁰` are shared), so existence follows from
Theorem 3 (`two_B_existence`) applied to `ctAugment`, and the cell-by-cell
coincidence follows from the working-paper betweenness + genericity theorem,
part (ii) (`btw_generic_cppbe_iff_coe`), since `w_t = max 𝒲_t` is unchanged
and genericity pins the cell.
-/

open Set Topology

namespace CPDLinear

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable (G : DisclosureGame T Msg)

/-- **Cheap-talk augmentation.** Replace each message `m` by the `|Θ|` copies
`(m, s)`, `s ∈ Θ`, sharing `m`'s preimage; all belief-side data is
unchanged. -/
noncomputable def ctAugment : DisclosureGame T (Msg × T) where
  Θ := G.Θ
  𝓜 := G.𝓜 ×ˢ G.Θ
  Θ_nonempty := G.Θ_nonempty
  𝓜_nonempty := G.𝓜_nonempty.product G.Θ_nonempty
  M := fun θ => G.M θ ×ˢ G.Θ
  M_subset := fun θ hθ => Finset.product_subset_product (G.M_subset θ hθ) subset_rfl
  M_nonempty := fun θ hθ => (G.M_nonempty θ hθ).product G.Θ_nonempty
  cover := by
    simp only [Finset.coe_product, G.cover, Set.iUnion_prod_const]
  μ0 := G.μ0
  μ0_mem := G.μ0_mem
  μ0_fullSupport := G.μ0_fullSupport
  V := G.V
  V_nonempty := G.V_nonempty
  V_isCompact := G.V_isCompact
  V_ordConnected := G.V_ordConnected
  V_uhc := G.V_uhc

/-! ## Preimage / `canSend` invariance -/

private lemma inter_nonempty' {α : Type*} [DecidableEq α] (A B : Finset α) :
    (A ∩ B).Nonempty ↔ ∃ x, x ∈ A ∧ x ∈ B := by
  simp only [Finset.Nonempty, Finset.mem_inter]

private lemma inter_singleton_nonempty' {α : Type*} [DecidableEq α]
    (A : Finset α) (x : α) : (A ∩ {x}).Nonempty ↔ x ∈ A := by
  rw [Finset.Nonempty]
  constructor
  · rintro ⟨a, ha⟩
    rw [Finset.mem_inter, Finset.mem_singleton] at ha
    exact ha.2 ▸ ha.1
  · exact fun h => ⟨x, by rw [Finset.mem_inter, Finset.mem_singleton]; exact ⟨h, rfl⟩⟩

/-- The preimage `canSend` of a copy `(m, s)` (with `s ∈ Θ`) equals that of `m`:
the second coordinate is ignored. -/
private lemma ctAugment_canSend_eq (m : Msg) {s : T} (hs : s ∈ G.Θ) :
    G.ctAugment.canSend (m, s) = G.canSend m := by
  classical
  ext θ
  simp only [DisclosureGame.canSend, DisclosureGame.preimageFull, mem_preimage, ctAugment,
    inter_singleton_nonempty', Finset.mem_product]
  tauto

open Classical in
/-- Adjoining copies changes no relative preimage: for a copy-set `X'` all of
whose second coordinates lie in `Θ`, the relative preimage `M⁻¹_R(X')` in the
augmented game equals `M⁻¹_R(π(X'))` with `π = Prod.fst`. -/
private lemma ctAugment_preimage_eq {R : Finset T} {X' : Finset (Msg × T)}
    (hX' : ∀ p ∈ X', p.2 ∈ G.Θ) :
    preimage G.ctAugment.M R X' = preimage G.M R (X'.image Prod.fst) := by
  classical
  ext θ
  simp only [mem_preimage, ctAugment, inter_nonempty', Finset.mem_product, Finset.mem_image]
  constructor
  · rintro ⟨hθ, p, ⟨hp1, _⟩, hpX⟩
    exact ⟨hθ, p.1, hp1, p, hpX, rfl⟩
  · rintro ⟨hθ, m, hmM, p, hpX, rfl⟩
    exact ⟨hθ, p, ⟨hmM, hX' p hpX⟩, hpX⟩

/-- **Definition 15 (M-CT) holds after augmentation.** Every augmented message
has at least `|Θ|` copies with the same preimage. -/
theorem ctAugment_mct : G.ctAugment.MCT := by
  classical
  rintro ⟨m, s⟩ hms
  simp only [ctAugment, Finset.mem_product] at hms
  obtain ⟨hm, hs⟩ := hms
  -- The copies `{m} ×ˢ Θ` all share the preimage of `(m, s)` and lie in `𝓜'`.
  refine le_trans (le_of_eq ?_)
    (Finset.card_le_card (s := ({m} ×ˢ G.Θ)) ?_)
  · simp only [ctAugment, Finset.card_product, Finset.card_singleton, one_mul]
  · intro p hp
    obtain ⟨p1, p2⟩ := p
    simp only [Finset.mem_product, Finset.mem_singleton] at hp
    obtain ⟨hpm, hps⟩ := hp
    simp only [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · simp only [ctAugment, Finset.mem_product]; exact ⟨by rw [hpm]; exact hm, hps⟩
    · rw [G.ctAugment_canSend_eq p1 hps, G.ctAugment_canSend_eq m hs, hpm]

/-
Skeptical-payoff invariance is deliberately not claimed. Under the
`|Θ|`-copies augmentation `ctAugment.M θ = G.M θ ×ˢ G.Θ`
is never a singleton (for `2 ≤ |Θ|`), so every type loses its forcing
constraint: the feasible-belief polytope at a copy `(m, s)` enlarges to the full
simplex on `canSend m`, and the skeptical payoff can strictly drop. Concretely
`T = Msg = Fin 2`, `M θ1 = {a}` (forced), `M θ2 = {a, b}`, `V μ = {μ θ1}` give
`G.skeptical θ1 = 1/2` but `G.ctAugment.skeptical θ1 = 0`. Only the
preimage-based quantities `v*(R)`, `max 𝒲_R` are cheap-talk invariant
(`ctAugment_vstar_eq` below), which is exactly what the coalition-proof
correspondence (`btw_ct_correspondence`) needs.
-/

/-- **`v*(R)` is cheap-talk invariant** (hence so is `max 𝒲_R`): adjoining
copies changes no relative preimage. -/
theorem ctAugment_vstar_eq {R : Finset T} (hne : R.Nonempty) (hsub : R ⊆ G.Θ) :
    G.ctAugment.vstar R = G.vstar R := by
  classical
  -- membership in `𝓜'_R` forces the second coordinate into `Θ`.
  have hsnd : ∀ {X' : Finset (Msg × T)}, X' ⊆ G.ctAugment.restrictMsgSpace R →
      ∀ p ∈ X', p.2 ∈ G.Θ := by
    intro X' hX' p hp
    have := hX' hp
    simp only [DisclosureGame.restrictMsgSpace, ctAugment, Finset.mem_biUnion,
      Finset.mem_product] at this
    obtain ⟨θ, _, _, h2⟩ := this
    exact h2
  unfold DisclosureGame.vstar
  congr 1
  ext w
  constructor
  · rintro ⟨X', hX'sub, hX'ne, rfl⟩
    refine ⟨X'.image Prod.fst, ?_, hX'ne.image _, ?_⟩
    · intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨p, hpX, rfl⟩ := hm
      have := hX'sub hpX
      simp only [DisclosureGame.restrictMsgSpace, ctAugment, Finset.mem_biUnion,
        Finset.mem_product] at this ⊢
      obtain ⟨θ, hθR, h1, _⟩ := this
      exact ⟨θ, hθR, h1⟩
    · rw [G.ctAugment_preimage_eq (hsnd hX'sub)]; rfl
  · rintro ⟨X, hXsub, hXne, rfl⟩
    refine ⟨X ×ˢ G.Θ, ?_, hXne.product G.Θ_nonempty, ?_⟩
    · intro p hp
      rw [Finset.mem_product] at hp
      have := hXsub hp.1
      simp only [DisclosureGame.restrictMsgSpace, ctAugment, Finset.mem_biUnion,
        Finset.mem_product] at this ⊢
      obtain ⟨θ, hθR, h1⟩ := this
      exact ⟨θ, hθR, h1, hp.2⟩
    · have hpf : ∀ p ∈ X ×ˢ G.Θ, p.2 ∈ G.Θ := by
        intro p hp; rw [Finset.mem_product] at hp; exact hp.2
      rw [G.ctAugment_preimage_eq hpf, Finset.product_image_fst G.Θ_nonempty]
      rfl

/-- **Cross-game cell match.** If the level-`n` residuals of a COE partition `P`
of `G` and a COE partition `P'` of `G.ctAugment` coincide, then their `n`-th
cells and payoffs coincide. The payoffs agree because both equal `v*(R_n)`, which
is cheap-talk invariant (`ctAugment_vstar_eq`); the cells then agree by
genericity (shared `v̄ ∘ condPrior`). -/
private lemma ct_cell_match (hSV : G.SingleValued) (hB : G.Betweenness)
    (hGen : G.Generic) {P : Partition G} {P' : Partition G.ctAugment}
    (hP : P.IsCOE) (hP' : P'.IsCOE) {n : ℕ}
    (hres : ctaux_Rn P n = ctaux_Rn P' n) (hn : n < P.card) (hn' : n < P'.card) :
    P.C ⟨n, hn⟩ = P'.C ⟨n, hn'⟩ ∧ P.w ⟨n, hn⟩ = P'.w ⟨n, hn'⟩ := by
  have hthetaP : thetaStep P.C ⟨n, hn⟩ = ctaux_Rn P n := ctaux_thetaStep_eq_Rn P ⟨n, hn⟩
  have hthetaP' : thetaStep P'.C ⟨n, hn'⟩ = ctaux_Rn P' n := ctaux_thetaStep_eq_Rn P' ⟨n, hn'⟩
  have hRne : (ctaux_Rn P n).Nonempty := (ctaux_Rn_nonempty_iff P n).mpr hn
  have hRsub : ctaux_Rn P n ⊆ G.Θ := hthetaP ▸ P.thetaStep_subset ⟨n, hn⟩
  -- Payoffs: both equal `v*(R_n)`, and `v*` is cheap-talk invariant.
  have hwP : P.w ⟨n, hn⟩ = G.vstar (ctaux_Rn P n) := by
    rw [ctaux_coe_w_eq_vstar hSV hB P hP ⟨n, hn⟩, hthetaP]
  have hwP' : P'.w ⟨n, hn'⟩ = G.ctAugment.vstar (ctaux_Rn P' n) := by
    rw [ctaux_coe_w_eq_vstar (G := G.ctAugment) hSV hB P' hP' ⟨n, hn'⟩, hthetaP']
  have hvstar : G.ctAugment.vstar (ctaux_Rn P' n) = G.vstar (ctaux_Rn P n) := by
    rw [← hres]; exact G.ctAugment_vstar_eq hRne hRsub
  have hw : P.w ⟨n, hn⟩ = P'.w ⟨n, hn'⟩ := by rw [hwP, hwP', hvstar]
  refine ⟨?_, hw⟩
  -- Cells: shared `v̄ ∘ condPrior` values agree, so genericity forces equal cells.
  have hcP : G.vbar (G.condPrior (P.C ⟨n, hn⟩)) = P.w ⟨n, hn⟩ :=
    ctaux_cell_vbar hSV hB P ⟨n, hn⟩
  have hcP' : G.vbar (G.condPrior (P'.C ⟨n, hn'⟩)) = P'.w ⟨n, hn'⟩ :=
    ctaux_cell_vbar (G := G.ctAugment) hSV hB P' ⟨n, hn'⟩
  have hvbar : G.vbar (G.condPrior (P.C ⟨n, hn⟩)) = G.vbar (G.condPrior (P'.C ⟨n, hn'⟩)) := by
    rw [hcP, hcP', hw]
  exact hGen ⟨P.C_nonempty _, P.C_subset _⟩ ⟨P'.C_nonempty _, P'.C_subset _⟩ hvbar

/-- **Cross-game residual equality.** The level-`n` residuals of a COE partition
of `G` and of a COE partition of `G.ctAugment` coincide, for every `n`. -/
private lemma ct_residual_eq (hSV : G.SingleValued) (hB : G.Betweenness)
    (hGen : G.Generic) {P : Partition G} {P' : Partition G.ctAugment}
    (hP : P.IsCOE) (hP' : P'.IsCOE) (n : ℕ) :
    ctaux_Rn P n = ctaux_Rn P' n := by
  induction n with
  | zero => rw [ctaux_Rn_zero P, ctaux_Rn_zero P']; rfl
  | succ n ih =>
    by_cases hn : n < P.card <;> by_cases hn' : n < P'.card
    · rw [ctaux_Rn_succ P hn, ctaux_Rn_succ P' hn', ih,
        (ct_cell_match G hSV hB hGen hP hP' ih hn hn').1]
    · exact absurd ((ctaux_Rn_nonempty_iff P' n).mp (ih ▸ (ctaux_Rn_nonempty_iff P n).mpr hn)) hn'
    · refine absurd ((ctaux_Rn_nonempty_iff P n).mp ?_) hn
      exact ih.symm ▸ (ctaux_Rn_nonempty_iff P' n).mpr hn'
    · have e1 : ctaux_Rn P (n + 1) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp (by rw [ctaux_Rn_nonempty_iff]; omega)
      have e2 : ctaux_Rn P' (n + 1) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp (by rw [ctaux_Rn_nonempty_iff]; omega)
      rw [e1, e2]

/-- **Working-paper remark (cheap-talk invariance).** Under single-valued `V`,
B, and genericity, the coalition-proof PBE partitions of `G` and of its
cheap-talk augmentation `ctAugment` coincide cell by cell, with equal
payoffs.

The proof factors through `btw_generic_cppbe_iff_coe` (the working-paper
betweenness + genericity theorem, part (ii)) applied to both `G` and
`G.ctAugment`, turning both coalition-proof PBE partitions into COE
partitions. The two COE partitions are then matched level by level via the
cross-game helpers in `CPD/BetweennessCTAux.lean`: at each step `w_t` equals
`v*(R_t)` (`ctaux_coe_w_eq_vstar`), `v*` is cheap-talk invariant
(`ctAugment_vstar_eq`), and genericity on the shared `v̄ ∘ condPrior` pins the
same cell `C_t` (`ct_cell_match`), whence the residuals agree at every level
(`ct_residual_eq`) and the partitions coincide in length, cells, and
payoffs. -/
theorem btw_ct_correspondence (hSV : G.SingleValued) (hB : G.Betweenness)
    (hGen : G.Generic) (P : Partition G) (P' : Partition G.ctAugment)
    (hP : P.IsCPPBEPartition) (hP' : P'.IsCPPBEPartition) :
    P.card = P'.card ∧
      ∀ (t : Fin P.card) (t' : Fin P'.card), (t : ℕ) = (t' : ℕ) →
        P.C t = P'.C t' ∧ P.w t = P'.w t' := by
  have hPcoe : P.IsCOE := (btw_generic_cppbe_iff_coe hSV hB hGen P).mp hP
  have hP'coe : P'.IsCOE := (btw_generic_cppbe_iff_coe (G := G.ctAugment) hSV hB hGen P').mp hP'
  have hcard : P.card = P'.card := by
    have hiff : ∀ n : ℕ, n < P.card ↔ n < P'.card := by
      intro n
      rw [← ctaux_Rn_nonempty_iff P n, ← ctaux_Rn_nonempty_iff P' n,
        ct_residual_eq G hSV hB hGen hPcoe hP'coe n]
    rcases lt_trichotomy P.card P'.card with h | h | h
    · exact absurd ((hiff P.card).mpr h) (lt_irrefl _)
    · exact h
    · exact absurd ((hiff P'.card).mp h) (lt_irrefl _)
  refine ⟨hcard, ?_⟩
  intro t t' htt'
  have hPlt : (t : ℕ) < P.card := t.isLt
  have hP'lt : (t : ℕ) < P'.card := by have := t'.isLt; omega
  have hmatch := ct_cell_match G hSV hB hGen hPcoe hP'coe
    (ct_residual_eq G hSV hB hGen hPcoe hP'coe (t : ℕ)) hPlt hP'lt
  have ht : t = (⟨(t : ℕ), hPlt⟩ : Fin P.card) := by ext; rfl
  have ht' : t' = (⟨(t : ℕ), hP'lt⟩ : Fin P'.card) := by ext; exact htt'.symm
  rw [ht, ht']
  exact hmatch

end DisclosureGame

end CPDLinear
