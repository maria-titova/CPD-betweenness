Follow-up on your previous run. You proved `thinB_coalition_payoff_set` and the
`thinB_upperNormalizedPBE_subgame` wrapper, and left `exists_upperNormalizedPBE` as
`sorry`, reporting that the normalization requires repeatedly merging adjacent partition
cells while preserving every dependent strategy and residual-game field.

That diagnosis is right, and the in-place merge is the wrong route. **Do not attempt it
again.** Two things have changed that make a much cheaper route available.

# New machinery in the project

`CPDLinear/LexMax.lean` and `CPDLinear/LexMaxAux.lean` have been added (ported from the
full CPD development; they were missing from your previous snapshot). They give:

    theorem lexmax_exists : ∃ P : Partition G, P.IsLexMax

where `P.IsLexMax` means `P.IsPBEPartition` together with: no PBE partition agrees with
`P` on every step before some `t` (same cells, same payoffs) and pays strictly more at
`t`. It is `sorry`-free.

Also already present and central to the route below:

- `isPBE_of_isPBEPartition (P : Partition G) : P.IsPBEPartition → G.IsPBE P.toSenderStrategy`
  (`PBEChar.lean`)
- `pbe_characterization`, `forwardPartition`, and `fwdW_strictAnti` (`PBEChar.lean`) —
  the forward partition of a PBE strategy has as its cells the **level sets of the
  equilibrium payoff function** `u θ = max_{m ∈ M θ} r m`, with distinct payoffs listed
  in strictly decreasing order.
- `thinB_coalition_payoff_set` — your own result from the previous run.
- `thinB_common_value` (`ThinB.lean`) — may still be `sorry`; its statement is frozen and
  correct, so cite it freely and do not try to prove it.

# The route — no record surgery anywhere

**Step 1. Take a lex-max PBE partition.** `obtain ⟨P, hP⟩ := lexmax_exists`.

**Step 2. Lex-maximality pins each payoff.** Claim: for every `t`,
`P.w t = min (G.vbar (G.condPrior (P.C t))) (P.w (t-1))`, with the convention that the
cap is absent at `t = 0`, so `P.w 0 = G.vbar (G.condPrior (P.C 0))`.

Proof of the claim: suppose `P.w t < min (vbar (condPrior (P.C t))) (P.w (t-1))`. Let
`w' := min (vbar (condPrior (P.C t))) (P.w (t-1))` and let `P'` be `P` with the payoff at
`t` replaced by `w'` — **only the `w` field changes, `card`, `C` and `σ` are untouched**,
so this is a trivial record update, not a merge. Check `P'` is still a PBE partition:
  * the `payoff` field: `w' ∈ G.V (condPrior (P.C t))` because
    `G.vlow (condPrior (P.C t)) ≤ P.w t < w' ≤ G.vbar (condPrior (P.C t))` and the value
    set is the interval — this is exactly `thinB_coalition_payoff_set`;
  * `Antitone P'.w`: `w' ≤ P.w (t-1)` by construction, and `w' > P.w t ≥ P.w (t+1)`;
  * `IsIR`: raising a cell's payoff preserves individual rationality (`isIR_iff_sup_le`
    in `PBEChar.lean` is the characterization to use).
Then `P'` agrees with `P` on every step before `t` and pays strictly more at `t`,
contradicting `hP`. ∎

So a lex-max partition is upper-normalized wherever the cap is slack, and where the cap
binds it produces `P.w t = P.w (t-1)` — an **adjacent tie**, never a violation.

**Step 3. Round-trip through the strategy to merge the ties for free.** Apply
`isPBE_of_isPBEPartition P hP.1` to get a PBE strategy `s := P.toSenderStrategy`, then
take the forward partition of `s` via `pbe_characterization` / `forwardPartition`. Its
cells are the level sets of `u`, and `u θ = P.w t` for `θ ∈ P.C t`, so **each forward
cell is exactly the union of a maximal run of consecutive `P`-cells sharing a payoff** —
the merge the paper performs by hand, obtained here by construction. `fwdW_strictAnti`
gives `StrictAnti` on the nose. No `Fin` re-indexing, no rebuilding of `exclusive`, no
`thetaStep` bookkeeping: the forward partition is built by existing, proved code.

**Step 4. The merged cells are upper-normalized.** Let `D = C_i ∪ … ∪ C_j` be one forward
cell, the run of consecutive `P`-cells all paid `p`. `condPrior D` is a strict convex
combination of the `condPrior (C_l)` with positive weights (`btwc_condPrior_partition` in
`BetweennessOrder.lean` is the decomposition; re-prove it locally if it is `private`), and
`p ∈ G.V (condPrior (C_l))` for every `l` in the run. So `hcommon` applies and gives
`G.V (condPrior D) = ⋂_l G.V (condPrior (C_l))`. By Step 2 the first cell of the run has
`vbar (condPrior (C_i)) = p`, so the intersection has upper endpoint `p`, i.e.
`G.vbar (condPrior D) = p`. That is `IsUpperNormalized` for the forward partition.

# Scope and rules

- Prove **only** `CPDLinear.DisclosureGame.exists_upperNormalizedPBE`. Its signature must
  stay byte-for-byte as given; only the proof body may change.
- Note it takes only `hcommon : G.HasCommonValueIntersections`, **not** `hthin`. Keep it
  that way — that is what lets it apply to auxiliary games.
- Do not modify any file other than `CPDLinear/ThinBExistence.lean`. In particular do not
  touch `ThinB.lean`, `LexMax.lean`, `LexMaxAux.lean`, `PBEChar.lean`, or
  `BetweennessOrder.lean`. Re-prove any `private` helper you need locally.
- Leave every other `sorry` in the project exactly as it is. Another call is running
  concurrently on `thinB_attained` and `thinB_merging` in this same file — do not touch
  those two declarations.
- If Step 2's `IsIR` preservation turns out to be the sticking point, say so explicitly in
  `ARISTOTLE_SUMMARY.md` rather than abandoning the route; that sub-step is the one I am
  least certain about and a precise obstruction report there is worth a lot.
- The whole project must still build (`lake build`).

Deliver the updated `CPDLinear/ThinBExistence.lean`.
