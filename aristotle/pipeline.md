# CPD-betweenness — Aristotle proof pipeline for the thin-B section

Formalize the thin-B subsection of `tex/v5.tex` (§"Thin-B correspondences" and its
appendix §"Proofs for sec:existence-thinB") into the `sorry` targets already stated in
`lean/CPDLinear/ThinB.lean` and `lean/CPDLinear/ThinBExistence.lean`.

The targets are **already stated** in the repo. Aristotle never invents a statement; it
fills in proof bodies. This keeps the README's TeX↔Lean coverage invariant intact and
makes the statement-fidelity check mechanical (`git diff` must touch proof bodies only).

## How a call works

One call = one `aristotle submit`, run **one at a time** (concurrency cap 1). Aristotle
is cheap but slow, and it does markedly better when told exactly which declarations to
close and which proof to follow, so each call carries the corresponding appendix proof
transcribed into Lean-facing steps.

Every submission bundles **the full Lean project plus the paper**:

- the whole `lean/` tree minus `.lake/` (the thin-B targets sit on top of the proved
  single-valued machinery — `BetweennessOrder`, `Restriction`, `Coalition`, … — and the
  prover needs to read it);
- `SPECIFICATION.tex` = a copy of `tex/v5.tex`;
- `TASK.md` = a copy of the call's `prompt.md`.

Aristotle rebuilds against its own matched mathlib v4.28.0, so `.lake/` is excluded.
Note the SDK force-includes `.lake` even when `.gitignore` lists it, so the exclusion
must happen in the bundling step — that is what `bin/make-submission.sh` is for.

```sh
aristotle/bin/make-submission.sh aristotle/call1-thinB-def
aristotle submit "$(cat aristotle/call1-thinB-def/prompt.md)" \
  --project-dir aristotle/call1-thinB-def/submission
```

Record the `Project created: <UUID>` in the call's `status.md`, commit, push.

## Per-call prompt contract

Every `prompt.md` must contain, in this order:

1. **Scope** — the exact list of declarations to close, by full name and file.
2. **Pointer into `SPECIFICATION.tex`** — the definition/lemma labels and the appendix
   subsection holding the proof, with an instruction to read it before writing Lean.
3. **The mathematics** — the appendix proof restated step by step in Lean-facing terms
   (names of the actual defs, the shape of each induction/limit argument).
4. **Rules** — the four that matter:
   - do not change any statement (signatures byte-for-byte; only bodies after `:=`);
   - do not touch any other file;
   - leave every other `sorry` in the project alone (they are later calls);
   - keep `ThinB.lean` importing only `CPDLinear.Game` so it stays **axiom-free**
     (`#print axioms` must not show `CPDLinear.kakutani`).

## Return protocol (per call)

1. Poll — never `aristotle show`, never `--wait`:
   `aristotle tasks <project-id>`  (or `/projects/lean/practice/bin/ari-wait <id>`).
2. On a terminal status, fetch into `call<N>-<slug>/solution`:
   `rm -rf call<N>-<slug>/solution*` first (a stale dir makes it refuse), then
   `/projects/lean/practice/bin/ari-fetch <project-id> aristotle/call<N>-<slug>/solution`.
3. The extracted top directory name **varies** (`submission_aristotle` for a first
   submit, `output-final_aristotle` after an `ask`). Locate the file by search:
   `find …/solution -path '*CPDLinear/ThinB.lean'`. Copy **only** the target file(s)
   back into `lean/CPDLinear/`.
4. **Statement-fidelity gate** — `git diff lean/CPDLinear/` must show changes to proof
   bodies and new auxiliary lemmas only. Any edit to a target's signature, or to a
   definition, fails the gate: do not merge, report to the user, let them decide.
5. **Verify locally** — this is not optional; Aristotle's server-side check is not a
   substitute for our mathlib pin:
   - `cd lean && lake build` (must succeed),
   - the call's targets no longer appear in the `declaration uses 'sorry'` warnings,
     and the remaining count is exactly what it should be,
   - `#print axioms` on the call's headline declaration — expect `propext`,
     `Classical.choice`, `Quot.sound`, and `CPDLinear.kakutani` only where the target
     genuinely goes through PBE existence (nothing in `ThinB.lean` may show it).
6. **Badge the writeup** — flip that result's badge in `tex/v5.tex` from
   `\leanpending{…}` to `\leanproved{…}` (or `\leanmixed{…}{…}` if only part closed).
   The badge macros are defined at the top of `v5.tex`.
7. Update `status.md`, `git commit` + `git push origin main`.
8. Only then start the next call.

If the task comes back `COMPLETE_WITH_ERRORS` or with the targets still `sorry`, resume
the **same** project with `aristotle ask <project-id> "<follow-up>"` — do **not** cancel
and resubmit, and do not bundle extra targets into a running call.

## Call queue

Order follows the proof order fixed in `README.md`. Later calls consume the lemmas
closed by earlier ones, so they are not reorderable.

| N | Call | Targets (file) | TeX |
|---|------|----------------|-----|
| 1 | `call1-thinB-def` | `IsBetweenness.bddOn_simplex`, `thinB_eq_Icc`, `thinB_A4` (ThinB) | `dfn:thinB`, `lem:thinB-A4` |
| 2 | `call2-envelopes` | `thinBUpper_isBetweenness`, `thinBLower_isBetweenness` (ThinB); `IsThinB.betweenness` (ThinBExistence) | `lem:thinB-envelope-B` |
| 3 | `call3-common-value` | `thinB_common_value` (ThinB); `IsThinB.hasCommonValueIntersections`, `HasCommonValueIntersections.of_subgame` (ThinBExistence) | `prop:thinB-common-value` |
| 4 | `call4-value-set` | `thinB_coalition_payoff_set` | `lem:thinB-value-set` |
| 5 | `call5-upper-pbe` | `exists_upperNormalizedPBE`, `thinB_upperNormalizedPBE_subgame` | `prop:thinB-upper-pbe` |
| 6 | `call6-attained` | `thinB_attained` | `lem:thinB-attained` |
| 7 | `call7-merging` | `thinB_merging` | `lem:thinB-merging` |
| 8 | `call8-btw-order-usc` | `btw_order_usc` (BetweennessOrderUSC) | `lem:btw-order`, u.s.c. form |
| 9 | `call9-existence` | `thinB_existence` | `thm:thinB-cppbe` |

Deviation from the README order, deliberate: `thinB_eq_Icc` is listed there under step 2,
but the appendix proof of `lem:thinB-A4` establishes it as its own Step 2
(equation `eq:thinB-interval`) and `thinB_A4` cannot be proved without it. Keeping the
two together makes call 1 exactly one appendix subsection.

Call 8 is the hard one. As of commit `36c3e4f` the continuity hypothesis was removed
from the existence theorem and the former conjecture `conj:thinB-cppbe` became
`thm:thinB-cppbe`; what carries that is the new upper-semicontinuous ranking lemma
`btw_order_usc`, whose geometric step (strict lower set relatively open in the face ⇒
same affine span ⇒ a constant pencil member forces both separators to vanish,
contradicting proper separation) is stated in `BetweennessOrderUSC.lean` and in the
appendix. Expect it to need more than one `ask`.

Watch the restriction convention throughout calls 5–9: auxiliary games keep the
**ambient** correspondence restricted to their face. Recomputing `thinB` on the smaller
simplex is wrong — it discards cluster values visible only from ambient directions —
which is exactly why `HasCommonValueIntersections.of_subgame` exists. Every prompt from
call 5 on must say so.

The three `sorry`s in `lean/CPDLinear/BetweennessPending.lean` (the plain-B-plus-
genericity branch of `thm:two`) are a **separate track**, not part of the thin-B queue.

## Sorry budget

Baseline at commit `71fccec`: **19** `declaration uses 'sorry'` warnings, `lake build`
exit 0 (8056 jobs). After each merged call the count must drop by exactly the number of
targets in that call, and by nothing else. The end state of the queue is 3 (the
`BetweennessPending` track).

## Layout

```
aristotle/
  pipeline.md                  # this file
  bin/make-submission.sh       # bundle lean/ + v5.tex + prompt for one call
  call<N>-<slug>/
    prompt.md                  # the verbatim Aristotle prompt
    status.md                  # project id, task id, status, merged, result
    submission/                # built by make-submission.sh (gitignored)
    solution/                  # fetched by ari-fetch (gitignored)
```

Shared lifecycle helpers live in `/projects/lean/practice/bin/`
(`ari-fetch`, `ari-wait`).
