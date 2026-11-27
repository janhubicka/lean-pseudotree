import PseudotreeValidation.GeneralizedCanonization

/-! Normalization of a subset of the coding set of ANY generalized
diary. Lift the full diary into the sparse tree, normalize the image
of the subset there, and transfer back by the checked naturality.
This removes the sparse-specific premise of the raw grammar proof. -/
namespace AllThoseBigRamsey.Pseudotree.GeneralizedNormalization
open RayEmbeddings SparseNormalization

theorem subset_diary_axioms (D : GeneralizedDiary n) {C : Finset Word}
    (hsub : C ⊆ D.codes) (hne : C.Nonempty) :
    ∃ h, GeneralizedTreeAxioms (nodes C) (codes C) h := by
  classical
  obtain ⟨g,_,hg⟩ := FIFOLifting.diary_lift D RayStrongMap.identity
  have hP : ∀ w ∈ C.image g.map, Point w := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    rw [hg v (hsub hv)]
    exact FIFOLifting.HFin_point v
  have hT := normalized_axioms hP (hne.image g.map)
  rw [nodes_image,codes_image] at hT
  exact ⟨_,hT⟩

noncomputable def normalize_subset (D : GeneralizedDiary n) {C : Finset Word}
    (hsub : C ⊆ D.codes) (hne : C.Nonempty) : GeneralizedDiary C.card :=
  ⟨nodes C,codes C,subset_diary_axioms D hsub hne,codes_card hne⟩

end AllThoseBigRamsey.Pseudotree.GeneralizedNormalization
