# call4b-normalize-lexmax

- Lane:        B (`ThinBExistence.lean`) — **running CONCURRENTLY with call5 on the same
               file**, by explicit user decision. See "Merge plan" below.
- Targets:     `CPDLinear.DisclosureGame.exists_upperNormalizedPBE`
- TeX:         `prop:thinB-upper-pbe`
- Owns:        `ThinBExistence.lean` (shared this once with call5)
- Project ID:  `24649bf5-0c82-49c8-8d7c-0dd0e85c4fe5`
- Task ID:     `158695a5-6451-470d-81ca-c54a92545082`
- Status:      **IN_PROGRESS** (submitted 2026-07-29)
- Retries:     0 (this is the retry of call4's one unproved target)
- Merged:      no
- Why a fresh submit, not `aristotle ask`: the route requires `LexMax.lean`, ported
               after call4 ran. `ask` cannot upload files — it continues in the old
               workspace, which has no `LexMax`. The prior project (`439ebba3`) is
               terminal, so this is not a cancel-and-resubmit.
- Route:       lexmax_exists → payoffs pinned by a `w`-field-only record update (no merge)
               → round-trip `isPBE_of_isPBEPartition`/`forwardPartition`, whose cells are
               level sets of the equilibrium payoff function, so ties merge for free and
               `fwdW_strictAnti` gives StrictAnti → merged cells normalized via
               `thinB_common_value`. Least-certain step: IR preservation when raising a
               payoff; the prompt asks for a precise obstruction report there.
- Merge plan:  call5 and this call share the SAME common ancestor,
               `aristotle/call4-payoff-normalize/BASE-ThinBExistence.lean`
               (commit `2a25909`, md5 a68bacdb36ced72028672e7989c1eb28). On the second
               return, 3-way merge:
                 git merge-file -p <first-merged> BASE-ThinBExistence.lean <second>
               Targets are disjoint declarations, so expect a clean merge; the real risk
               is duplicate private helper NAMES, which surface as a build error rather
               than a conflict. Rename and rebuild if so.
