import PseudotreeValidation.RevisedChainDegrees
import PseudotreeValidation.RevisedCopyCanonization

/-! The paper states its chain degree for literal copies. The finite
chain is rigid, so its copy and embedding palette bounds coincide. -/
namespace AllThoseBigRamsey.Pseudotree.RevisedChainDegrees
open scoped FirstOrder
open RevisedConvention (RevisedSparseModel)
open NoInfiniteCanonical (Copy copyOf representative representative_copy copy_range_eq)
open RevisedChainDiaries (ChainDiary)

abbrev P := RevisedSparseModel

theorem chain_copyOf_injective (n : Nat) :
    Function.Injective (fun e : Fin n ↪[language] P => copyOf e) := by
  intro e g h
  apply words_injective
  exact (RevisedCopyCanonization.words_range_iff e g).mpr ((copy_range_eq e g).mp h)

def CopyBigRamseyBound (n d : Nat) : Prop :=
  ∀ r : Nat, 0 < r → ∀ χ : Copy (Fin n) P → Fin r,
    ∃ f : P ↪[language] P, ∃ palette : Finset (Fin r),
      palette.card ≤ d ∧ ∀ e : Fin n ↪[language] P, χ (copyOf (f.comp e)) ∈ palette

theorem copy_bound_iff (n d : Nat) :
    CopyBigRamseyBound n d ↔ GenericIncomparables.FunctionalBigRamseyBound (Fin n) P d := by
  constructor
  · intro h r hr χ
    obtain ⟨f,palette,hcard,hcover⟩ := h r hr (fun C => χ (representative C))
    refine ⟨f,palette,hcard,?_⟩
    intro e
    have he : representative (copyOf (f.comp e)) = f.comp e :=
      chain_copyOf_injective n (representative_copy _)
    simpa only [he] using hcover e
  · intro h r hr χ
    exact h r hr (fun e => χ (copyOf e))

theorem exact_copy_degree {n : Nat} (hn : 0 < n) :
    CopyBigRamseyBound n (Fintype.card (ChainDiary n)) ∧
      ∀ d, CopyBigRamseyBound n d → Fintype.card (ChainDiary n) ≤ d := by
  rw [RevisedChainDiaries.chainDiary_card]
  exact ⟨(copy_bound_iff n _).mpr (exact_degree hn).1,
    fun d hd => (exact_degree hn).2 d ((copy_bound_iff n d).mp hd)⟩

end AllThoseBigRamsey.Pseudotree.RevisedChainDegrees
