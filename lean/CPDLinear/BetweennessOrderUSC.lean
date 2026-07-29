import CPDLinear.BetweennessOrder

/-!
# Ranking level sets under upper semicontinuity

This file is the Lean handoff for the upper-semicontinuous version of
`lem:btw-order` used by the thin-B existence theorem in `tex/v5.tex`.

The existing construction in `BetweennessRank.btw_order_aux` assumes
continuity.  The paper proves that upper semicontinuity is enough.  In the
two-sided recursive case, on every compact convex face `F` the nonempty strict
sublevel set

`B_F = F ∩ {μ | G.vbar μ < y}`

is relatively open in `F`, and therefore has the same affine span as `F`.
If a pencil member `h_λ = λ a + (1 - λ) b` containing a tied level point were
constant on `F`, it would be zero there.  For `0 < λ < 1`, both separators are
nonpositive on `B_F`, so their convex combination can vanish there only if
both vanish there.  Affineness and `affineSpan B_F = affineSpan F` then
contradict properness of the separators.  The endpoint cases contradict
properness directly.  Thus every relevant tie slice has smaller affine
dimension, and the rest of the recursive proof of `btw_order_aux` is
unchanged.

The declaration below intentionally duplicates the public conclusion of
`DisclosureGame.btw_order`, replacing single-valuedness (which supplied
continuity) with the exact upper-semicontinuity hypothesis used in the proof.
-/

open Set Topology
open scoped BigOperators Classical

namespace CPDLinear

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-- **`lem:btw-order`, upper-semicontinuous form.** Every level set of an
upper-semicontinuous betweenness payoff carries the order required by the
greedy coalition-selection argument. -/
lemma btw_order_usc
    (husc : UpperSemicontinuousOn G.vbar (simplexOn G.Θ))
    (hB : G.Betweenness) (y : ℝ) :
    ∃ ord : (T → ℝ) → (T → ℝ) → Prop,
      (∀ x ∈ G.levelSet y, ∀ x' ∈ G.levelSet y, ord x x' ∨ ord x' x) ∧
      (∀ x ∈ G.levelSet y, ∀ x' ∈ G.levelSet y, ∀ x'' ∈ G.levelSet y,
        ord x x' → ord x' x'' → ord x x'') ∧
      (∀ x ∈ G.levelSet y, ∀ u ∈ simplexOn G.Θ, y < G.vbar u →
        ∀ α ∈ Set.Ioo (0 : ℝ) 1,
          (fun θ => α * x θ + (1 - α) * u θ) ∈ G.levelSet y →
            ord (fun θ => α * x θ + (1 - α) * u θ) x ∧
            ¬ ord x (fun θ => α * x θ + (1 - α) * u θ)) ∧
      (∀ μbar ∈ G.levelSet y, ∀ (n : ℕ) (a : Fin n → ℝ) (μs : Fin n → (T → ℝ)),
        (∀ z, 0 < a z) → (∑ z, a z = 1) →
        (∀ z, μs z ∈ simplexOn G.Θ ∧ G.vbar (μs z) ≤ y) →
        (μbar = fun θ => ∑ z, a z * μs z θ) →
          ∃ z, μs z ∈ G.levelSet y ∧ ord (μs z) μbar) := by
  obtain ⟨ord, hcomp, htrans, hi, hii⟩ :=
    btw_order_aux husc hB y (simplexOn G.Θ) (simplexOn_convex' G.Θ) (subset_refl _)
  have hlevel : ∀ x, x ∈ G.levelSet y ↔ (x ∈ simplexOn G.Θ ∧ G.vbar x = y) :=
    fun x => Iff.rfl
  refine ⟨ord, ?_, ?_, ?_, ?_⟩
  · intro x hx x' hx'
    exact hcomp x ((hlevel x).1 hx).1 ((hlevel x).1 hx).2 x' ((hlevel x').1 hx').1
      ((hlevel x').1 hx').2
  · intro x hx x' hx' x'' hx''
    exact htrans x ((hlevel x).1 hx).1 ((hlevel x).1 hx).2 x' ((hlevel x').1 hx').1
      ((hlevel x').1 hx').2 x'' ((hlevel x'').1 hx'').1 ((hlevel x'').1 hx'').2
  · intro x hx u hu hlt α hα hz
    exact hi x ((hlevel x).1 hx).1 ((hlevel x).1 hx).2 u hu hlt α hα
      ((hlevel _).1 hz).1 ((hlevel _).1 hz).2
  · intro μbar hμbar n a μs hpos hsum hmem hcomb
    obtain ⟨z, ⟨hzmem, hzval⟩, hord⟩ :=
      hii μbar ((hlevel μbar).1 hμbar).1 ((hlevel μbar).1 hμbar).2 n a μs hpos hsum
        (fun z => ⟨(hmem z).1, (hmem z).2⟩) hcomb
    exact ⟨z, (hlevel _).2 ⟨hzmem, hzval⟩, hord⟩

end DisclosureGame

end CPDLinear
