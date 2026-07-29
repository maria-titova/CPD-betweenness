import Mathlib

/-!
# Kakutani's fixed-point theorem  (the one permitted external input)

Kakutani's fixed-point theorem is **not** in mathlib.  Per the project rules it
is the single allowed dependency: we record the classical statement as
`KakutaniProperty E` and assert it as an `axiom kakutani` for finite-dimensional
real normed spaces.  Every other result in this development is proved from
mathlib first principles; `kakutani` is used exactly once, in the proof of PBE
existence.
-/

open Set

namespace CPDLinear

/-- **Kakutani's fixed-point theorem**, as a property of a real topological
vector space `E`: for every non-empty compact convex `K ⊆ E` and every
correspondence `Φ : E → Set E` with non-empty convex values, `Φ x ⊆ K` for
`x ∈ K`, and closed graph, there is a fixed point `x ∈ K` with `x ∈ Φ x`. -/
def KakutaniProperty (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] : Prop :=
  ∀ (K : Set E) (Φ : E → Set E),
    K.Nonempty → IsCompact K → Convex ℝ K →
    (∀ x ∈ K, (Φ x).Nonempty) →
    (∀ x ∈ K, Convex ℝ (Φ x)) →
    (∀ x ∈ K, Φ x ⊆ K) →
    IsClosed {p : E × E | p.1 ∈ K ∧ p.2 ∈ Φ p.1} →
    ∃ x ∈ K, x ∈ Φ x

/-- **Kakutani's fixed-point theorem** (the one permitted external input),
asserted for finite-dimensional real normed spaces. -/
axiom kakutani (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : KakutaniProperty E

/-- The ambient finite-dimensional real coordinate space of the fixed-point
argument: `ℝ^{Θ×𝓜} × ℝ^{𝓜×Θ} × ℝ^{𝓜}`, encoding `(σ, μ, r)`. -/
abbrev FixedPointSpace (T Msg : Type*) : Type _ :=
  (T → Msg → ℝ) × (Msg → T → ℝ) × (Msg → ℝ)

end CPDLinear
