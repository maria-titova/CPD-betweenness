# call6-crown

- Lane:        B (`ThinBExistence.lean`)
- Targets:     `thinB_existence`  (`lean/CPDLinear/ThinBExistence.lean`)
- TeX:         `thm:thinB-cppbe` — the crown theorem
- Owns:        `ThinBExistence.lean`
- Dispatch:    lane B free, i.e. after call5 merges. Prefer to dispatch once call8
               (`btw_order_usc`) has also merged, so the assembly is against a proved
               ranking lemma — but do not block on it, the statement is frozen.
- Project ID:  —
- Task ID:     —
- Status:      **QUEUED**
- Retries:     0
- Merged:      no
- Expected:    sorry −1, and the thin-B track is then complete (only the 3
               `BetweennessPending` sorrys remain). Pure assembly: mirrors
               `two_B_existence` in `BetweennessOrder.lean` with `btw_order_usc` in place
               of `btw_order`. Will pick up `CPDLinear.kakutani` — expected and correct.
- Badge:       on merge flip `thm:thinB-cppbe` to `\leanproved`, and re-check
               `dfn:thinB` / `prop:thinB-upper-pbe` badges.
