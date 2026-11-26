import PseudotreeValidation.ChartReservoir
import PseudotreeValidation.RevisedDiaryExpansion

/-! Actual infinite recurrence in the manuscript's literal revised
sparse model, including native reduct and expansion embeddings. -/
namespace AllThoseBigRamsey.Pseudotree.RevisedConvention
open RayEmbeddings RayMapModel
open SparseNormalization (Point)
open scoped FirstOrder

/-- A critical map inside every revised structural copy. The queue
and passing-digit convention remain literally unchanged. -/
theorem revised_recurrence (f : Reservoir.Target)
    (hf : ∀ z ∈ Set.range f, Sparse.InSparse (revisedFromBlocks z)) :
    ∃ X : CriticalCopies.CriticalMap, ∀ w, Point w →
      revisedToBlocks (((CriticalCopies.total X).map w).map toLetter) ∈ Set.range f :=
  ChartReservoir.recurrence revisedChart f hf

/-- Recurrence of every finite normalized code set simultaneously. -/
theorem revised_recurrent_code_sets (f : Reservoir.Target)
    (hf : ∀ z ∈ Set.range f, Sparse.InSparse (revisedFromBlocks z)) :
    ∃ X : CriticalCopies.CriticalMap,
      (∀ w, Point w →
        revisedToBlocks (((CriticalCopies.total X).map w).map toLetter) ∈ Set.range f) ∧
      ∀ C : Finset RayEmbeddings.Word,
        GeneralizedNormalization.codes (C.image (CriticalCopies.total X).map) =
          GeneralizedNormalization.codes C :=
  ChartReservoir.recurrent_code_sets revisedChart f hf

end AllThoseBigRamsey.Pseudotree.RevisedConvention

namespace AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion
open RevisedConvention (RevisedSparseModel revisedFromBlocks revisedToBlocks revised_recurrence)
open RayEmbeddings RayMapModel
open scoped FirstOrder

/-- Every revised native reduct self-copy contains a native expanded
self-copy. This uses the chart-independent geometric recurrence,
not an assumed identification of the two orientations on the queue. -/
theorem native_recurrence (e : RevisedSparseModel ↪[language] RevisedSparseModel) :
    ∃ g : RevisedSparseModel ↪[expandedLanguage] RevisedSparseModel,
      Set.range g ⊆ Set.range e := by
  let f := RevisedSparseModel.inclusion.comp (e.comp RevisedSparseModel.equiv.toEmbedding)
  have hf (z : TernaryModel) (hz : z ∈ Set.range f) :
      Sparse.InSparse (revisedFromBlocks z) := by
    obtain ⟨t,rfl⟩ := hz
    exact (e (RevisedSparseModel.equiv t)).property
  obtain ⟨X,hX⟩ := revised_recurrence f hf
  refine ⟨criticalEmbedding X,?_⟩
  rintro _ ⟨x,rfl⟩
  obtain ⟨t,ht⟩ := hX (word x) (word_point x)
  refine ⟨RevisedSparseModel.equiv t,?_⟩
  apply Subtype.ext
  change f t = revisedToBlocks (((CriticalCopies.total X).map (word x)).map toLetter)
  exact ht

end AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion
