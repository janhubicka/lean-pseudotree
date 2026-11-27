import PseudotreeValidation.ReservoirTransitions

/-! Original-coordinate recurrence, obtained by specialization rather
than a second infinite assembly proof. -/
namespace AllThoseBigRamsey.Pseudotree.Reservoir
open RayEmbeddings RayMapModel
open SparseNormalization (Point)
open scoped FirstOrder

theorem recurrence (f : Target)
    (hsparse : ∀ x ∈ Set.range f, Sparse.InSparse (fromBlocks x)) :
    ∃ X : CriticalCopies.CriticalMap, ∀ w, Point w →
      DiaryChains.model ((CriticalCopies.total X).map w) ∈ Set.range f :=
  ChartReservoir.recurrence ReservoirChart.original f hsparse

theorem recurrent_code_sets (f : Target)
    (hsparse : ∀ x ∈ Set.range f, Sparse.InSparse (fromBlocks x)) :
    ∃ X : CriticalCopies.CriticalMap,
      (∀ w, Point w → DiaryChains.model ((CriticalCopies.total X).map w) ∈ Set.range f) ∧
      ∀ C : Finset Word,
        GeneralizedNormalization.codes (C.image (CriticalCopies.total X).map) =
          GeneralizedNormalization.codes C :=
  ChartReservoir.recurrent_code_sets ReservoirChart.original f hsparse

end AllThoseBigRamsey.Pseudotree.Reservoir
