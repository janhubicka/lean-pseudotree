import PseudotreeValidation.AmbientPigeonhole
import PseudotreeValidation.RelevantReservoirs

/-! Assemble the independently proved concrete axioms. -/
namespace AllThoseBigRamsey.Pseudotree.CriticalCopies

/-- The actual A.1--A.4 package on critical copies of R. -/
noncomputable def ramseySpace : RamseySpace.AbstractRamseySpace system :=
  RamseySpace.AbstractRamseySpace.ofPublishedAxioms finitization
    amalgamation_nonempty
    (by
      intro n a B d hd A hAB hne
      obtain ⟨A',hA',hsub⟩ := amalgamation_refine a B hd hAB hne
      exact ⟨A',hA',amalgamation_nonempty a B hd hA',hsub⟩)
    (by
      intro n a B d hd O
      obtain ⟨A,hA,h⟩ := pigeonhole a B hd O
      refine ⟨A,hA,?_⟩
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Set.disjoint_left.mpr (fun _ hb ho => h hb ho)))

/-- Concrete Ellentuck theorem in the exact published abstract interface.
Transfer to the expanded-copy topology is a separate identification. -/
theorem concrete_ellentuck :
    RamseySpace.IsTopologicalRamseySpaceTextbook (S := system) :=
  ellentuck_of_axioms ramseySpace

end AllThoseBigRamsey.Pseudotree.CriticalCopies
