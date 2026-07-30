import CPDLinear.BetweennessGeneric

/-!
# Private cross-game infrastructure for the cheap-talk-invariance remark

Helpers used by `btw_ct_correspondence` (in `CPD/BetweennessCT.lean`), the
working-paper remark that adjoining cheap-talk copies preserves the
betweenness development. These re-derive, in game-generic form, the
residual/cell machinery of `CPD/BetweennessGeneric.lean` (whose analogues are
`private`), plus the identification `w_t = v*(R_t)` for a COE partition, which
is the bridge that lets cheap-talk invariance of `v*` (`ctAugment_vstar_eq`)
transport the whole COE partition across the augmentation.
-/

open Set Topology
open scoped Classical

namespace CPDLinear

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-- Transport a strategy along an equality of games. -/
private lemma ctaux_strategy_of_eq {g₁ g₂ : DisclosureGame T Msg} (h : g₁ = g₂)
    (s : Strategy g₁) :
    ∃ s' : Strategy g₂, s'.evidence = s.evidence ∧
      ∀ m, s'.coalitionBelief m = s.coalitionBelief m := by
  subst h; exact ⟨s, rfl, fun _ => rfl⟩

/-- The cell `C_t` viewed as a coalition of the residual game `G|_{R_t}`. -/
private lemma ctaux_cell_coalition (P : Partition G) (t : Fin P.card) :
    ∃ K : (G.restrict (thetaStep P.C t) (thetaStep_nonempty t (P.C_nonempty t))
        (P.thetaStep_subset t)).Coalition,
      K.C = P.C t ∧ K.w = P.w t := by
  obtain ⟨K, hK⟩ : ∃ K : Coalition (G.restrict (thetaStep P.C t) (thetaStep_nonempty t (P.C_nonempty t)) (P.thetaStep_subset t)), K.C = P.C t ∧ K.w = P.w t := by
    have h_eq : (G.restrict (thetaStep P.C t) (thetaStep_nonempty t (P.C_nonempty t)) (P.thetaStep_subset t)).restrict (P.C t) (P.C_nonempty t) (by
    exact Finset.subset_biUnion_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, by rfl ⟩ ) |> Finset.Subset.trans <| Finset.Subset.refl _) = G.restrict (P.C t) (P.C_nonempty t) (P.C_subset t) := by
      exact restrict_restrict _ _ _ _
    obtain ⟨σ', hσ'⟩ := ctaux_strategy_of_eq h_eq.symm (P.σ t)
    refine' ⟨ ⟨ P.C t, _, _, σ', _, P.w t, _ ⟩, rfl, rfl ⟩ <;> simp_all +decide [ DisclosureGame.Coalition ]
    · convert P.exclusive t using 1
    · exact P.payoff t
  generalize_proofs at *
  use K

/-- The cell's pooling value equals its payoff (`value_id`). -/
lemma ctaux_cell_vbar (hSV : G.SingleValued) (hB : G.Betweenness)
    (P : Partition G) (t : Fin P.card) :
    G.vbar (G.condPrior (P.C t)) = P.w t := by
  obtain ⟨K, hKC, hKw⟩ := ctaux_cell_coalition P t
  have h := btw_attained_le hSV hB (thetaStep_nonempty t (P.C_nonempty t))
    (P.thetaStep_subset t) K
  rw [← hKC, ← hKw]; exact h.1.symm

/-- For a COE partition, the step payoff equals the largest pooling value
`v*(R_t)`. This is the cheap-talk-invariant bridge. -/
lemma ctaux_coe_w_eq_vstar (hSV : G.SingleValued) (hB : G.Betweenness)
    (P : Partition G) (hP : P.IsCOE) (t : Fin P.card) :
    P.w t = G.vstar (thetaStep P.C t) := by
  rw [hP.w_eq_stepMax t, Partition.stepMax]
  have hattn := btw_attained hSV hB (thetaStep_nonempty t (P.C_nonempty t)) (P.thetaStep_subset t)
  exact hattn.csSup_eq

/-! ### `ℕ`-indexed residuals (copies of the `BetweennessGeneric` helpers) -/

/-- The `ℕ`-indexed residual `R_n := ⋃_{(s:ℕ) ≥ n} C_s`. -/
noncomputable def ctaux_Rn (P : Partition G) (n : ℕ) : Finset T :=
  (Finset.univ.filter (fun s : Fin P.card => n ≤ (s : ℕ))).biUnion P.C

lemma ctaux_thetaStep_eq_Rn (P : Partition G) (t : Fin P.card) :
    thetaStep P.C t = ctaux_Rn P (t : ℕ) := by
  ext; simp [thetaStep, ctaux_Rn]

lemma ctaux_Rn_zero (P : Partition G) : ctaux_Rn P 0 = G.Θ := by
  unfold ctaux_Rn; simp +decide [ P.cover_eq ]

lemma ctaux_Rn_nonempty_iff (P : Partition G) (n : ℕ) :
    (ctaux_Rn P n).Nonempty ↔ n < P.card := by
  constructor <;> intro hn
  · obtain ⟨ θ, hθ ⟩ := hn
    obtain ⟨ s, hs, hθ ⟩ := Finset.mem_biUnion.mp hθ
    exact lt_of_le_of_lt ( Finset.mem_filter.mp hs |>.2 ) ( Fin.is_lt s )
  · exact ⟨ _, Finset.mem_biUnion.mpr ⟨ ⟨ n, hn ⟩, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, le_rfl ⟩, Finset.mem_coe.mpr ( P.C_nonempty ⟨ n, hn ⟩ |> Classical.choose_spec ) ⟩ ⟩

lemma ctaux_Rn_succ (P : Partition G) {n : ℕ} (h : n < P.card) :
    ctaux_Rn P (n + 1) = ctaux_Rn P n \ P.C ⟨n, h⟩ := by
  refine' Finset.Subset.antisymm _ _
  · intro x hx; simp_all +decide [ ctaux_Rn ]
    obtain ⟨ a, ha₁, ha₂ ⟩ := hx; refine' ⟨ ⟨ a, le_of_lt ha₁, ha₂ ⟩, _ ⟩ ; intro ha₃; have := P.C_disjoint a ⟨ n, h ⟩ ; simp_all +decide [ Fin.ext_iff ]
    exact Finset.disjoint_left.mp ( this ( ne_of_gt ha₁ ) ) ha₂ ha₃
  · intro x hx; simp_all +decide [ ctaux_Rn ]
    obtain ⟨ ⟨ a, ha₁, ha₂ ⟩, ha₃ ⟩ := hx; exact ⟨ a, lt_of_le_of_ne ha₁ ( Ne.symm <| by rintro rfl; exact ha₃ ha₂ ), ha₂ ⟩

end DisclosureGame

end CPDLinear
