import CPDLinear.Betweenness
import Mathlib

/-!
# Betweenness is a one-dimensional condition (working-paper appendix)

**Working-paper remark (segment characterization of betweenness).** `v̄`
satisfies betweenness (B) iff it is **weakly monotone along every line
segment** in `ΔΘ`: for every pair of endpoints `μ, μ'`, the one-variable map
`l ↦ v̄(l·μ + (1-l)·μ')` is monotone (non-decreasing) or antitone
(non-increasing) on `[0,1]` (`betweenness_iff_segment_monotone`).

Forward (`→`): B forces each segment map to be monotone-or-antitone (the
two-case argument of the remark, using B on sub-segments). Converse (`←`): an
interior point of a monotone segment lies between the endpoint values, which
is B.
-/

open Set Topology

namespace CPDLinear

/-
A convex combination of two points of a simplex `Δ S` stays in `Δ S`.
-/
private lemma simplex_seg_mem {α : Type*} [Fintype α] {S : Finset α} {μ μ' : α → ℝ}
    (hμ : μ ∈ simplexOn S) (hμ' : μ' ∈ simplexOn S) {l : ℝ}
    (hl : l ∈ Set.Icc (0 : ℝ) 1) :
    (fun θ => l * μ θ + (1 - l) * μ' θ) ∈ simplexOn S := by
  refine ⟨fun θ => ?_, ?_, fun θ => ?_⟩
  · exact add_nonneg (mul_nonneg hl.1 (hμ.1 θ))
      (mul_nonneg (sub_nonneg.2 hl.2) (hμ'.1 θ))
  · simp_all +decide [Finset.sum_add_distrib, ← Finset.mul_sum _ _ _]
  · intro hθ; have := hμ.2.2 θ hθ; have := hμ'.2.2 θ hθ; aesop

/-
**General real-analysis fact.** A function `f` on `[0,1]` that satisfies the
three-point betweenness property (the value at an interior point of any
subinterval lies between the endpoint values) is monotone or antitone.
-/
private lemma mono_or_anti_of_between (f : ℝ → ℝ)
    (hbtw : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1, ∀ y, x < y → y < z →
        min (f x) (f z) ≤ f y ∧ f y ≤ max (f x) (f z)) :
    MonotoneOn f (Set.Icc 0 1) ∨ AntitoneOn f (Set.Icc 0 1) := by
  by_cases h : f 0 ≤ f 1;
  · refine Or.inl fun x hx y hy hxy => ?_
    cases eq_or_lt_of_le hxy <;> simp_all +decide
    grind +extAll
  · right; intro x hx y hy hxy
    cases eq_or_lt_of_le hxy <;> simp_all +decide
    grind

namespace DisclosureGame

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

variable {G : DisclosureGame T Msg}

/-
**Three-point betweenness of the segment map.** If `v̄` satisfies B, then
the segment map `t ↦ v̄(t·μ + (1-t)·μ')` satisfies three-point betweenness on
`[0,1]`: at any interior point `y` of a subinterval `[x,z]`, its value lies
between the values at `x` and `z`. (Every subsegment is itself a segment between
two simplex points, so B applies.)
-/
private lemma segMap_between (hB : G.Betweenness) {μ μ' : T → ℝ}
    (hμ : μ ∈ simplexOn G.Θ) (hμ' : μ' ∈ simplexOn G.Θ)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1)
    (y : ℝ) (hxy : x < y) (hyz : y < z) :
    min (G.vbar (fun θ => x * μ θ + (1 - x) * μ' θ))
        (G.vbar (fun θ => z * μ θ + (1 - z) * μ' θ))
      ≤ G.vbar (fun θ => y * μ θ + (1 - y) * μ' θ) ∧
    G.vbar (fun θ => y * μ θ + (1 - y) * μ' θ)
      ≤ max (G.vbar (fun θ => x * μ θ + (1 - x) * μ' θ))
            (G.vbar (fun θ => z * μ θ + (1 - z) * μ' θ)) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c ∈ Set.Ioo (0 : ℝ) 1 ∧ y = c * x + (1 - c) * z := by
    refine ⟨(y - z) / (x - z), ⟨?_, ?_⟩, ?_⟩
    · rw [lt_div_iff_of_neg] <;> linarith
    · rw [div_lt_iff_of_neg] <;> linarith
    · linarith [mul_div_cancel₀ (y - z) (by linarith : (x - z) ≠ 0)]
  convert hB (fun θ => x * μ θ + (1 - x) * μ' θ) (simplex_seg_mem hμ hμ' hx)
    (fun θ => z * μ θ + (1 - z) * μ' θ) (simplex_seg_mem hμ hμ' hz) c hc.1 using 1
  · exact iff_of_eq (by congr; ext; rw [hc.2]; ring)
  · grind

/-- **Working-paper remark (segment characterization of betweenness).** `v̄`
satisfies B iff it is weakly monotone along every line segment: for all
endpoints `μ, μ' ∈ ΔΘ`, the map `l ↦ v̄(l·μ + (1-l)·μ')` is `MonotoneOn` or
`AntitoneOn` on `[0,1]`. -/
theorem betweenness_iff_segment_monotone :
    G.Betweenness ↔
      ∀ μ ∈ simplexOn G.Θ, ∀ μ' ∈ simplexOn G.Θ,
        MonotoneOn (fun l : ℝ => G.vbar (fun θ => l * μ θ + (1 - l) * μ' θ))
            (Set.Icc 0 1) ∨
        AntitoneOn (fun l : ℝ => G.vbar (fun θ => l * μ θ + (1 - l) * μ' θ))
            (Set.Icc 0 1) := by
  constructor
  · -- Forward: B ⇒ monotone-or-antitone, via three-point betweenness of the
    -- segment map and the general real-analysis fact.
    intro hB μ hμ μ' hμ'
    exact mono_or_anti_of_between _
      (fun x hx z hz y hxy hyz => segMap_between hB hμ hμ' x hx z hz y hxy hyz)
  · -- Converse: monotone-or-antitone ⇒ B.
    intro hmono μ hμ μ' hμ' l hl
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
    have hlI : l ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hl.1, le_of_lt hl.2⟩
    have hf0 : (fun l : ℝ => G.vbar (fun θ => l * μ θ + (1 - l) * μ' θ)) 0
        = G.vbar μ' := by
      simp
    have hf1 : (fun l : ℝ => G.vbar (fun θ => l * μ θ + (1 - l) * μ' θ)) 1
        = G.vbar μ := by
      simp
    rcases hmono μ hμ μ' hμ' with hm | ha
    · constructor
      · have hlo := hm h0 hlI (le_of_lt hl.1)
        rw [hf0] at hlo
        exact le_trans (min_le_right _ _) hlo
      · have hhi := hm hlI h1 (le_of_lt hl.2)
        rw [hf1] at hhi
        exact le_trans hhi (le_max_left _ _)
    · constructor
      · have hlo := ha hlI h1 (le_of_lt hl.2)
        rw [hf1] at hlo
        exact le_trans (min_le_left _ _) hlo
      · have hhi := ha h0 hlI (le_of_lt hl.1)
        rw [hf0] at hhi
        exact le_trans hhi (le_max_right _ _)

end DisclosureGame

end CPDLinear
