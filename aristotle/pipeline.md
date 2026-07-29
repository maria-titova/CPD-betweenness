# CPD-betweenness — Aristotle proof pipeline for the thin-B section

Formalize the thin-B subsection of `tex/v5.tex` (§"Thin-B correspondences" and its
appendix §"Proofs for sec:existence-thinB") into the `sorry` targets already stated in
`lean/CPDLinear/ThinB.lean`, `lean/CPDLinear/ThinBExistence.lean` and
`lean/CPDLinear/BetweennessOrderUSC.lean`.

The targets are **already stated** in the repo. Aristotle never invents a statement; it
fills in proof bodies. This keeps the README's TeX↔Lean coverage invariant intact and
makes the statement-fidelity check mechanical (`git diff` must touch proof bodies only).

## The two facts that shape the whole schedule

1. **Aristotle returns whole files.** Two concurrent calls editing the same file would
   leave us splicing two independent rewrites of it. So *file ownership is the unit of
   concurrency*: at most one in-flight call per file.
2. **A Lean proof may cite a lemma that is still `sorry`.** Because every statement in
   this pipeline already exists and is frozen, a downstream call can be proved against
   upstream lemmas before those lemmas are proved. So *dependencies do not serialize the
   queue* — only file ownership does.

Together these give three independent **lanes**, which is exactly the concurrency cap:

| Lane | File(s) owned | Calls, in order |
|---|---|---|
| **A** | `ThinB.lean` | call1 → call2 |
| **B** | `ThinBExistence.lean` | call3 → call4 → call5 → call6 |
| **C** | `BetweennessOrderUSC.lean`, `BetweennessRank.lean`, `BetweennessOrder.lean` | call8 |

Lane B is the critical path (four serial calls), so **lane B must never idle**.

## Dispatch rule — follow this exactly

At every tick, after processing returns:

1. Compute in-flight = calls with a Project ID and `Merged: no`. Cap is **3**.
2. A call is **dispatchable** iff its lane has no in-flight call *and* its `prompt.md`
   exists. Nothing else blocks it — not unproved dependencies.
3. While in-flight < 3 and some call is dispatchable, dispatch by this priority:
   **lane B first, then lane A, then lane C.** Lane B is the long pole; a tick that
   leaves lane B idle while dispatching elsewhere is a scheduling error.
4. Never dispatch two calls that own a common file, and never dispatch a call whose
   `prompt.md` is missing — report that instead of inventing one.

Concretely, the intended sequence from the current state:

```
now:              call1 (A)   call3 (B)   call8 (C)        <- 3 in flight
call3 returns  -> call4 (B) dispatched immediately
call1 returns  -> call2 (A) dispatched
call4 returns  -> call5 (B)
call5 returns  -> call6 (B)   [prefer call8 merged first, but do not block]
call8 returns  -> lane C done
```

Total 8 calls; wall-clock ≈ the length of lane B, not the sum of all eight.

## Anti-stall design — why each prompt is shaped as it is

Aristotle gets stuck when a call is large, open-ended, or requires it to rediscover
something the repo already contains. Every prompt therefore carries:

- **One appendix subsection of scope**, 1–3 target declarations. No call is open-ended.
- **A pointer to the proved single-valued analogue to mirror.** This is the single
  biggest lever: `thinB_attained` / `thinB_merging` / `thinB_existence` have conclusions
  *identical* to `btw_attained` / `btw_merging` / `two_B_existence` in
  `BetweennessCore.lean` and `BetweennessOrder.lean`, differing only in hypotheses. The
  prompts say so and give the substitution table.
- **The appendix proof restated in Lean-facing terms**, naming the actual definitions.
- **An explicit "lemmas you may assume" section** — the frozen statements it may cite
  while they are still `sorry`, with an instruction not to prove or delete them.
- **A "traps" section** listing the known wrong routes: replacing `V` by `{vbar}`
  (fails `A4`), recomputing `thinB` on a smaller simplex (loses ambient cluster values),
  assuming `vbar` is continuous, and using `btw_order` instead of `btw_order_usc`.
- **A partial-credit clause** naming which target to sacrifice if blocked, so one hard
  declaration cannot stall a whole call.
- **Four standing rules**: don't change statements; don't touch other files; leave other
  `sorry`s alone; keep `ThinB.lean` axiom-free.

## Call table

| N | Call | Lane | Targets | TeX |
|---|------|------|---------|-----|
| 1 | `call1-thinB-def` | A | `IsBetweenness.bddOn_simplex`, `thinB_eq_Icc`, `thinB_A4` | `dfn:thinB`, `lem:thinB-A4` |
| 2 | `call2-envelopes-common` | A | `thinBUpper_isBetweenness`, `thinBLower_isBetweenness`, `thinB_common_value` | `lem:thinB-envelope-B`, `prop:thinB-common-value` |
| 3 | `call3-bridge` | B | `IsThinB.betweenness`, `IsThinB.hasCommonValueIntersections`, `HasCommonValueIntersections.of_subgame` | game-level transport |
| 4 | `call4-payoff-normalize` | B | `thinB_coalition_payoff_set`, `exists_upperNormalizedPBE`, `thinB_upperNormalizedPBE_subgame` | `lem:thinB-value-set`, `prop:thinB-upper-pbe` |
| 5 | `call5-attained-merging` | B | `thinB_attained`, `thinB_merging` | `lem:thinB-attained`, `lem:thinB-merging` |
| 6 | `call6-crown` | B | `thinB_existence` | `thm:thinB-cppbe` |
| 8 | `call8-btw-order-usc` | C | `btw_order_usc` | `lem:btw-order`, u.s.c. form |

(There is no call 7; the numbering predates the lane redesign and calls 1 and 8 were
already submitted under these names.)

Call 8 is the hardest. Continuity enters the existing ranking construction in exactly one
place — the final step of `pencil_hgood` (`BetweennessRank.lean` ~line 711), which lets
`α → 0` along a segment. Upper semicontinuity **cannot** patch that step: it yields
`limsup ≤ vbar u`, the wrong direction. The paper replaces it with an affine-span
argument (u.s.c. ⇒ `L⁻⁻` relatively open ⇒ `aff B_F = aff F` ⇒ a constant pencil member
forces both separators to vanish, contradicting proper separation). Call 8 is the one
sanctioned exception to "do not touch other files": it may generalize `hcont → husc` in
`BetweennessRank.lean` rather than duplicate ~400 lines, under the gates that
`two_B_existence` stays proof-complete and `btw_order`'s public statement is unchanged.

The three `sorry`s in `lean/CPDLinear/BetweennessPending.lean` (the plain-B-plus-
genericity branch of `thm:two`) are a **separate track**, not part of this queue.

## Sorry budget

Baseline at commit `71fccec`: **19** `declaration uses 'sorry'` warnings, `lake build`
exit 0 (8056 jobs). Each merged call must drop the count by exactly its number of
targets and by nothing else:

| after | call | delta | total |
|---|---|---|---|
| — | baseline | — | 19 |
| | call1 | −3 | 16 |
| | call3 | −3 | 13 |
| | call2 | −3 | 10 |
| | call4 | −3 | 7 |
| | call5 | −2 | 5 |
| | call8 | −1 | 4 |
| | call6 | −1 | 3 |

End state: **3** — the `BetweennessPending` track. (The order of the middle rows depends
on return order; only the arithmetic is fixed.)

Axiom expectations: everything in `ThinB.lean` must stay
`propext, Classical.choice, Quot.sound` — that file imports only `CPDLinear.Game` and
must never reach `CPDLinear.kakutani`. `exists_upperNormalizedPBE`, `thinB_existence` and
anything else routed through `exists_PBE` will legitimately show `CPDLinear.kakutani`.

## How a call works

```sh
aristotle/bin/make-submission.sh aristotle/call<N>-<slug>
aristotle submit "$(cat aristotle/call<N>-<slug>/prompt.md)" \
  --project-dir aristotle/call<N>-<slug>/submission
```

Every submission bundles the whole `lean/` tree minus `.lake/`, plus `SPECIFICATION.tex`
(a copy of `tex/v5.tex`) and `TASK.md` (a copy of the prompt). Aristotle rebuilds against
its own matched mathlib v4.28.0, so `.lake/` is excluded — and it must be excluded *in
the bundler*, because the SDK force-includes `.lake` even when `.gitignore` lists it.
The "no .lake folder" warning on submit is expected and harmless.

Record the `Project created: <UUID>` in the call's `status.md`, commit, push.

## Return protocol (per call)

1. Poll — never `aristotle show`, never `--wait`, never `aristotle cancel`:
   `aristotle tasks <project-id>`.
2. On a terminal status, fetch into `call<N>-<slug>/solution`:
   `rm -rf call<N>-<slug>/solution*` first (a stale dir makes it refuse), then
   `/projects/lean/practice/bin/ari-fetch <project-id> aristotle/call<N>-<slug>/solution`.
3. The extracted top directory name **varies** (`submission_aristotle` for a first
   submit, `output-final_aristotle` after an `ask`). Locate files by search. Copy back
   **only the files that call's lane owns**.
4. **Statement-fidelity gate** — `git diff lean/CPDLinear/` must show proof bodies and
   new auxiliary lemmas only. Any edit to a target's signature, to a definition, or to
   `btw_order`'s public statement fails the gate.
5. **Verify locally** — `lake build` exit 0; the call's targets gone from the `sorry`
   warnings; the total delta exactly as tabulated; `two_B_existence` still proof-complete;
   `#print axioms` as expected above.
6. **Badge** `tex/v5.tex`: `\leanpending{…}` → `\leanproved{…}`, only when every Lean
   declaration named in that badge is proof-complete.
7. Update `status.md`, commit, push. Then dispatch per the rule above.

On failure: `git checkout -- lean/CPDLinear/` to keep the repo green, bump `Retries`,
and resume the **same** project with `aristotle ask <project-id> "<what failed>"` — never
cancel and resubmit, never bundle extra targets into a running call. Three strikes →
`Status: STUCK`, leave for the user.

## Layout

```
aristotle/
  pipeline.md                  # this file
  bin/make-submission.sh       # bundle lean/ + v5.tex + prompt for one call
  bin/cron-prompt.txt          # the 30-minute poller's instructions
  call<N>-<slug>/
    prompt.md                  # the verbatim Aristotle prompt
    status.md                  # lane, targets, owned files, ids, status, merged
    submission/                # built by make-submission.sh (gitignored)
    solution/                  # fetched by ari-fetch (gitignored)
```

Shared lifecycle helpers live in `/projects/lean/practice/bin/` (`ari-fetch`, `ari-wait`).
