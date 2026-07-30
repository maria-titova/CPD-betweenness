import CPDLinear.BetweennessOrder
import CPDLinear.BetweennessGeneric
import CPDLinear.Theorem2

/-!
# Remaining plain-B plus genericity declarations

`Theorem2.lean` proves the strict-betweenness branch of `thm:two`.
`BetweennessOrder.lean` proves existence under plain B.  The declarations in
this file record the still-unformalized genericity branch of the stronger
no-halt, characterization, and uniqueness claims in `tex/v5.tex`.
-/

open Set Topology
open scoped Classical

namespace CPDLinear

variable {T Msg : Type*} [Fintype T] [Fintype Msg]

namespace DisclosureGame

variable {G : DisclosureGame T Msg}

/-- Under single-valued B and genericity, every greedy prefix extends. -/
theorem two_generic_noHalt_full (hSV : G.SingleValued)
    (hB : G.Betweenness) (hGen : G.Generic)
    (Q : G.GreedyPrefix) (hQ : Q.IsGreedy) :
    ∃ P : Partition G, P.IsGreedy ∧ Q.card ≤ P.card ∧
      ∀ (s : Fin Q.card) (t : Fin P.card), (s : ℕ) = (t : ℕ) →
        P.C t = Q.C s ∧ P.w t = Q.w s :=
  btw_generic_noHalt hSV hB hGen Q hQ

/-- Under single-valued B and genericity, coalition-proof PBE partitions are
exactly coalition-optimal partitions. -/
theorem generic_cppbe_iff_coe (hSV : G.SingleValued)
    (hB : G.Betweenness) (hGen : G.Generic) (P : Partition G) :
    P.IsCPPBEPartition ↔ P.IsCOE :=
  btw_generic_cppbe_iff_coe hSV hB hGen P

/-- Essential uniqueness under single-valued B and genericity. -/
theorem two_B_generic_unique (hSV : G.SingleValued)
    (hB : G.Betweenness) (hGen : G.Generic)
    (P P' : Partition G) (hP : P.IsCPPBEPartition)
    (hP' : P'.IsCPPBEPartition) :
    P.card = P'.card ∧
      ∀ (t : Fin P.card) (t' : Fin P'.card), (t : ℕ) = (t' : ℕ) →
        P.C t = P'.C t' ∧ P.w t = P'.w t' :=
  btw_generic_unique hSV hB hGen P P' hP hP'

end DisclosureGame

end CPDLinear
