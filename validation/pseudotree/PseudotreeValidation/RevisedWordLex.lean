import PseudotreeValidation.ReservoirChart
import PseudotreeValidation.SparseChainGeometry

/-! Direct manuscript clauses for the revised literal word order. -/
namespace AllThoseBigRamsey.Pseudotree.RevisedConvention

theorem revisedWordBelow_prefix_incomparable_lex {s t : Sparse.Word}
    (hinc : ¬s.IsPrefix t ∧ ¬t.IsPrefix s)
    (h : revisedWordBelow s t) : Sparse.lexLess s t = true := by
  induction s generalizing t with
  | nil => exact (hinc.1 List.nil_prefix).elim
  | cons a s ih =>
    cases t with
    | nil => exact (hinc.2 List.nil_prefix).elim
    | cons b t =>
      by_cases hab : a = b
      · subst b
        have hst : revisedWordBelow s t :=
          (below_common_prefix [a] s t).mp h
        have hi : ¬s.IsPrefix t ∧ ¬t.IsPrefix s :=
          ⟨fun hp => hinc.1 (List.cons_prefix_cons.mpr ⟨rfl,hp⟩),
           fun hp => hinc.2 (List.cons_prefix_cons.mpr ⟨rfl,hp⟩)⟩
        simpa [Sparse.lexLess] using ih hi hst
      · cases a <;> cases b <;>
          cases hs : parseWord s <;> cases ht : parseWord t <;>
          simp_all [revisedWordBelow,parseWord,prependBlock,RayTree.Below,
            RayTree.first,binaryLERevised,Sparse.lexLess,Sparse.rank]

theorem revisedWordBelow_one_prefix (p tail v : Sparse.Word)
    (h : revisedWordBelow (p ++ TernaryLetter.one :: tail) v) :
    (p ++ [TernaryLetter.one]).IsPrefix v := by
  have hm := (mirror_below_iff _ _).mpr h
  have h' : wordBelow (mirror p ++ TernaryLetter.one :: mirror tail) (mirror v) := by
    simpa [mirror_append,mirror_cons,mirrorLetter] using hm
  have hp := Sparse.wordBelow_one_prefix _ _ _ h'
  apply (mirror_prefix_iff _ _).mp
  simpa [mirror_append,mirror_singleton,mirrorLetter] using hp

end AllThoseBigRamsey.Pseudotree.RevisedConvention
