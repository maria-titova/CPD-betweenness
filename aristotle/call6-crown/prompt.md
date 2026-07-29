You are working inside the Lean 4 project **CPDLinear**, whose complete source is in
this project and already builds against Mathlib (toolchain `leanprover/lean4:v4.28.0`).
The mathematical source of truth is `SPECIFICATION.tex` (the paper). `TASK.md` is a copy
of these instructions.

# Scope of this call

Prove **exactly one** declaration, in `CPDLinear/ThinBExistence.lean`:

- `CPDLinear.DisclosureGame.thinB_existence`

    theorem thinB_existence (hthin : G.IsThinB) :
        ∃ P : Partition G, P.IsCPPBEPartition

This is the crown theorem of the paper: **every thin-B disclosure game admits a
coalition-proof PBE**. In `SPECIFICATION.tex` it is Theorem `thm:thinB-cppbe`, with its
proof in the appendix subsection "Proof of \cref{thm:thinB-cppbe}". **Read that proof in
full before writing any Lean.**

# The proved single-valued analogue — this is your template

`CPDLinear/BetweennessOrder.lean` contains `two_B_existence` (around line 877), the same
theorem for a single-valued betweenness payoff, fully proved, together with the private
machinery that does the work: `two_B_top_cell`, `two_B_max_cell`, `two_B_exists_coe`,
`two_B_merged_preimage`, `two_B_merged_value`, `two_B_finite_max`.

**The recursion is identical.** Read `two_B_existence` and its helpers closely and mirror
them. You may not edit that file, but you may re-prove any `private` helper you need
inside `ThinBExistence.lean`. The substitutions are:

| single-valued | thin-B |
|---|---|
| `btw_order` (needs continuity via `hSV`) | `btw_order_usc` (needs only `UpperSemicontinuousOn G.vbar`) |
| `value_id` | `thinB_coalition_payoff_set` |
| `btw_attained` | `thinB_attained` |
| `btw_merging` | `thinB_merging` |
| PBE partition of the auxiliary game | `thinB_upperNormalizedPBE_subgame` |
| `hB : G.Betweenness` from `hSV` | `IsThinB.betweenness hthin` |

# Lemmas you may assume

Every other `sorry` declaration in this project — in particular `btw_order_usc`
(`BetweennessOrderUSC.lean`), `thinB_attained`, `thinB_merging`,
`thinB_coalition_payoff_set`, `thinB_upperNormalizedPBE_subgame`,
`IsThinB.betweenness`, `IsThinB.hasCommonValueIntersections`,
`HasCommonValueIntersections.of_subgame`, and everything in `ThinB.lean` — is being
proved by other calls in this pipeline and may still carry `sorry` in the copy you
receive. **Their statements are frozen and correct. Use them freely as if proved. Do not
prove them, do not restate them, do not delete their `sorry`.** Your job is only to
assemble them into `thinB_existence`.

You will need upper semicontinuity of `G.vbar` to invoke `btw_order_usc`. It follows
from the standing assumption `A4` (`G.V_uhc` in `Game.lean`) — the upper envelope of an
upper-hemicontinuous compact-interval-valued correspondence is upper semicontinuous.
`Game.lean` records the envelope properties derived from `A4`; if the exact statement you
need is not already there, prove it as a private helper in `ThinBExistence.lean`. Do
**not** try to get it from continuity: `G.vbar` is not continuous under thin-B.

# The mathematics

`IsThinB.betweenness` gives the betweenness inequalities for `G.vbar`, and `A4` gives its
upper semicontinuity, so `btw_order_usc` applies to every level set of `G.vbar`.

**The recursion.** `R₁ := G.Θ`. Given non-empty `Rₜ`, put `wₜ := max 𝒲_{Rₜ}` (the maximum
exists by `isCompact_coalitionPayoffs`, `CoalitionPayoffs.lean`). If `(C, σ, wₜ)` attains
it then `thinB_coalition_payoff_set` lets the same strategy be paid
`G.vbar (G.condPrior C)`, so maximality forces `G.vbar (G.condPrior C) = wₜ`; hence every
payoff-maximal coalition prior lies in the level set `{G.vbar = wₜ}`. Among them choose
`(Cₜ, σₜ, wₜ)` whose prior is **maximal under the relation supplied by `btw_order_usc`**
(possible: only finitely many type sets, hence finitely many priors — `two_B_finite_max`
is the finite-maximal-element helper). Set `Rₜ₊₁ := Rₜ \ Cₜ`. Each step removes a
non-empty cell, so the recursion terminates and returns a partition with
`wₜ = max 𝒲_{Rₜ}` at every step.

**The no-rise argument.** Suppose `w_{s+1} > w_s` for some `s`. Write `y := w_s`, and let
`L`, `L⁺⁺`, `L⁻⁻` be the level, strict-upper and strict-lower sets of `G.vbar` at `y`.
Then `G.condPrior C_s ∈ L` and `G.condPrior C_{s+1} ∈ L⁺⁺`.

Apply `thinB_merging` inside `G|_{R_s}` with `D := C_s ∪ C_{s+1}`: it gives
`D = M⁻¹_{R_s}(X(σ_s) ∪ X(σ_{s+1}))` and `G.vbar (G.condPrior D) = y`. Also
`G.condPrior D = α • G.condPrior C_s + (1-α) • G.condPrior C_{s+1}` with
`α = μ⁰(C_s)/μ⁰(D) ∈ (0,1)`. Property (i) of `btw_order_usc` then gives

    G.condPrior D ≻ G.condPrior C_s.                                    (*)

Form the auxiliary game `G'` with type set `D`, message set `X(σ_s) ∪ X(σ_{s+1})`,
mapping `θ ↦ M θ ∩ (X(σ_s) ∪ X(σ_{s+1}))`, prior `G.condPrior D`, and **the ambient `V`
restricted to `Δ D`**. The relative-preimage identity makes it a disclosure game. Apply
`thinB_upperNormalizedPBE_subgame` to it: a PBE partition with `w̃₁ > ⋯ > w̃ₖ` and
`w̃τ = G.vbar (G.condPrior C̃τ)`, whose cells partition `D`, so
`G.condPrior D = ∑τ βτ • G.condPrior C̃τ` with `βτ > 0` summing to one.

The first auxiliary cell is a coalition of `G|_{R_s}` (if a type in `R_s` can send one of
its messages, the relative-preimage identity puts it in `D` and auxiliary exclusivity
puts it in `C̃₁`), so `w̃₁ ≤ max 𝒲_{R_s} = y`. Quasiconvexity of `G.vbar` gives the
reverse: `y = G.vbar (G.condPrior D) ≤ maxτ G.vbar (G.condPrior C̃τ) = w̃₁`. So `w̃₁ = y`
and, by strict decrease, `w̃τ < y` for `τ ≥ 2`. Thus the first auxiliary prior lies in `L`
and every later one in `L⁻⁻`.

Property (ii) of `btw_order_usc`, applied to the decomposition of `G.condPrior D`, yields
a component on `L` weakly above `G.condPrior D`. The first cell is the only component on
`L`, so `G.condPrior C̃₁ ⪰ G.condPrior D ≻ G.condPrior C_s` by (*). But
`(C̃₁, σ̃₁, y)` is a coalition of `G|_{R_s}` attaining `max 𝒲_{R_s}`, contradicting the
rank-maximal choice of `(C_s, σ_s, w_s)`.

Hence `wₜ ≤ w_{t-1}` at every step, so the partition is COE, and
`IsCOE.isGreedy` (`COE.lean`) with `cppbe_characterization` (`CoalitionProof.lean`) make
it a coalition-proof PBE partition — exactly the last step of `two_B_existence`.

# Traps — do not fall into these

- **Do not** use `btw_order`. It requires single-valuedness, which supplies continuity of
  `G.vbar`. Under thin-B the envelope is only upper semicontinuous. Use `btw_order_usc`.
- **Do not** recompute `thinB` on `Δ D` for the auxiliary game. It keeps the **ambient**
  correspondence; cluster values visible only from ambient directions would be lost.
- **Do not** replace `G.V` by the singleton `{G.vbar μ}` and apply `two_B_existence`.
  That singleton correspondence need not satisfy `A4`, so it is not a disclosure game.
  This is the single most tempting wrong route and the paper explicitly rules it out.

# Rules

- **Do not change any statement.** The signature of `thinB_existence` byte-for-byte as
  given, as must every definition in the file. If you believe it is unprovable as
  written, stop and say so in `ARISTOTLE_SUMMARY.md`.
- **Do not touch any other file.** Re-prove any `private` helper you need inside
  `ThinBExistence.lean`.
- **Leave every other `sorry` in the project exactly as it is.**
- Use no `sorry` in `thinB_existence`. If genuinely blocked, leave it `sorry`, keep the
  project building, and explain precisely which step failed in `ARISTOTLE_SUMMARY.md` —
  a precise obstruction report is worth a lot here.
- The whole project must still build (`lake build`, package `CPDLinear`).

Deliver the updated `CPDLinear/ThinBExistence.lean`.
