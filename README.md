# CPD Betweenness

This repository isolates the single-valued and thin-B betweenness results from
`Coalition-Proof Disclosure`.

## Authoritative files

- `tex/v5.tex` is the final mathematical handoff. It contains the local model
  definitions, the single-valued B results, the thin-B extension, and the
  proofs needed to formalize them.
- `lean/CPDLinear/` contains the corresponding Lean declarations and proofs.
  `ThinB.lean` contains the analytic thin-B foundation;
  `BetweennessOrderUSC.lean` contains the pending upper-semicontinuous
  level-set ranking theorem;
  `ThinBExistence.lean` contains the game-level thin-B targets; and
  `BetweennessPending.lean` holds the genericity branch of the stronger
  single-valued theorem, now proved.

The Lean package is no longer restricted to the betweenness import closure.
The remaining modules of the full `CPD` development were ported in (namespace
`CPD` rewritten to `CPDLinear`), because the eventual deliverable is the whole
paper and the dropped modules turned out to carry machinery the thin-B work
needs — `LexMax`/`LexMaxAux` for lexicographically maximal PBE partitions, and
`BetweennessGeneric`, which discharges the genericity branch outright.

The former `tex/extension/` staging directory has been retired. Do not recreate
a second thin-B source: edit `tex/v5.tex`.

## TeX-to-Lean coverage invariant

Every formal assumption, definition, remark, lemma, proposition, and theorem
in `tex/v5.tex` carries a visible badge naming its Lean declaration:

- **Lean proved**: the declaration contains a proof (possibly using the
  project's separately documented axioms through its imports).
- **Lean proved modulo Kakutani**: the mapped declaration is the direct
  fixed-point-based PBE-existence result.
- **Lean pending**: the declaration exists with `sorry` and is an explicit
  proof obligation.

Do not add or change a formal TeX result without adding or updating its mapped
Lean declaration in the same change. A pending result must still have a
precise Lean statement; a comment or strategy note is not a substitute.

## Thin-B handoff

The recommended proof order is:

1. `IsBetweenness.bddOn_simplex`, compact cluster values, and `thinB_A4`;
2. `thinB_eq_Icc` and betweenness of the upper and lower envelopes;
3. `thinB_common_value`;
4. `IsThinB.hasCommonValueIntersections` and
   `HasCommonValueIntersections.of_subgame`;
5. `thinB_coalition_payoff_set`;
6. `exists_upperNormalizedPBE` and
   `thinB_upperNormalizedPBE_subgame`;
7. `thinB_attained`;
8. `thinB_merging`;
9. `btw_order_usc`;
10. `thinB_existence`.

The paper's proof of `btw_order_usc` generalizes the existing continuous
ranking construction. In its two-sided case, the strict lower set is a
nonempty relatively open subset of the current convex face and hence has the
same affine span. If a relevant member of the separator pencil were constant
on the face, the sign restrictions would force both separators to vanish on
that strict lower set and therefore on the whole face, contradicting proper
separation. Thus the recursive tie slices remain lower-dimensional without
continuity.

The crucial restriction convention is that auxiliary games keep the ambient
correspondence restricted to their faces. Do not recompute `thinB` on the
smaller simplex: doing so can discard cluster values visible only from ambient
directions. Transport `HasCommonValueIntersections` instead; this is what
justifies `exists_upperNormalizedPBE` in every auxiliary game used by
`thinB_attained` and `thinB_existence`.

Do not formalize the game by replacing `V` with the singleton
`{G.vbar μ}`. That singleton correspondence need not satisfy the standing
upper-hemicontinuity assumption.

## Builds

Build the paper from `tex/` with:

```sh
latexmk -pdf -interaction=nonstopmode v5.tex
```

The Lean project uses the toolchain and Mathlib revision recorded in
`lean/lean-toolchain`, `lean/lakefile.toml`, and `lean/lake-manifest.json`.

Source snapshots:

- TeX: `overleaf-CPD` commit `a53543a`
- Lean: `lean-CPD-v3` commit `95b9605`
