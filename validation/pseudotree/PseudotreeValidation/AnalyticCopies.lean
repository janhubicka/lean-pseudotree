import PseudotreeValidation.AnalyticApproximation
import PseudotreeValidation.CopySpaceTopology
import PseudotreeValidation.ConcreteEllentuck
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Analytic transfer in the native expanded-copy space. -/
namespace AllThoseBigRamsey.Pseudotree.DiaryExpansion
open RayEmbeddings FirstOrder
open scoped FirstOrder
open CriticalCopies (CriticalMap system approx codingRange)
open SparseNormalization (Point)
open RamseySpace.Souslin

local instance analyticBoolTopology : TopologicalSpace Bool := ⊥
local instance analyticBoolDiscrete : DiscreteTopology Bool := ⟨rfl⟩

/-- Equal finite branch prefixes imply equality of each earlier
coordinate. -/
theorem branchPrefix_coord {b c : Nat → Nat} {k i : Nat}
    (h : branchPrefix c k = branchPrefix b k) (hi : i < k) : c i = b i := by
  have ht := congrArg (List.take (i+1)) h
  rw [take_branchPrefix c hi,take_branchPrefix b hi] at ht
  have he := congrArg (fun l : List Nat => l[i]?) ht
  simp only [branchPrefix_succ,List.concat_eq_append] at he
  rw [List.getElem?_append_right (show (branchPrefix c i).length ≤ i by simp),
    List.getElem?_append_right (show (branchPrefix b i).length ≤ i by simp)] at he
  simp only [length_branchPrefix,Nat.sub_self] at he
  change some (c i) = some (b i) at he
  exact Option.some.inj he

/-- Continuity into the literal product subspace implies the local
prefix continuity required by the Souslin-image lemma. -/
theorem prefixContinuous_of_continuous (f : (Nat → Nat) → CopySpace)
    (hf : Continuous f) :
    RamseySpace.PrefixContinuous (S := system) (copyEquiv.symm ∘ f) := by
  classical
  intro b n
  let X := copyEquiv.symm (f b)
  obtain ⟨L,hL⟩ := finite_copy_cylinder X n
  let I := {x : SparseModel // (word x).length ≤ L}
  letI : Finite I := (bounded_points_finite L).to_subtype
  let U : Set (Nat → Nat) :=
    ⋂ x : I, {c | (f c).val x.val = (f b).val x.val}
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro x
    change IsOpen ((fun c => (f c).val x.val) ⁻¹' {(f b).val x.val})
    exact (isOpen_discrete _).preimage
      ((continuous_apply x.val).comp (continuous_subtype_val.comp hf))
  have hb : b ∈ U := by simp [U]
  obtain ⟨J,V,hJV,hsub⟩ := (isOpen_pi_iff.mp hU) b hb
  obtain ⟨k,hk⟩ := J.exists_nat_subset_range
  refine ⟨k,?_⟩
  intro c hc
  have hcU : c ∈ U := by
    apply hsub
    intro i hi
    have hlt : i < k := Finset.mem_range.mp (hk hi)
    rw [branchPrefix_coord hc hlt]
    exact (hJV i hi).2
  have hcoord (x : SparseModel) (hx : (word x).length ≤ L) :
      (toCopy X).val x = (toCopy (copyEquiv.symm (f c))).val x := by
    have h := Set.mem_iInter.mp hcU (⟨x,hx⟩ : I)
    change (f c).val x = (f b).val x at h
    have hb' : toCopy X = f b := copyEquiv.apply_symm_apply (f b)
    have hc' : toCopy (copyEquiv.symm (f c)) = f c := copyEquiv.apply_symm_apply (f c)
    rw [hb',hc']
    exact h.symm
  exact (hL _ hcoord).symm

/-- Every analytic subset of the actual expanded-copy space is
completely Ramsey for the transported whole-block approximations. -/
set_option backward.isDefEq.respectTransparency false in
theorem analytic_copies_ramsey (A : Set CopySpace)
    (hA : MeasureTheory.AnalyticSet A) :
    RamseySpace.IsRamseyOnBasicNeighborhoods (S := system) (toCopy ⁻¹' A) := by
  let T : system.Point → CopySpace := fun X => toCopy X
  change RamseySpace.IsRamseyOnBasicNeighborhoods (S := system) (T ⁻¹' A)
  rw [MeasureTheory.AnalyticSet] at hA
  apply (RamseySpace.isRamsey_iff_onBasicNeighborhoods CriticalCopies.ramseySpace _).mp
  rcases hA with rfl | ⟨f,hf,rfl⟩
  · rw [Set.preimage_empty]
    exact RamseySpace.isRamsey_empty CriticalCopies.ramseySpace
  · let F : (Nat → Nat) → system.Point := fun b => copyEquiv.symm (f b)
    have hEq : T ⁻¹' Set.range f = Set.range F := by
      ext X
      constructor
      · rintro ⟨b,hb⟩
        refine ⟨b,?_⟩
        apply toCopy_injective
        change toCopy (copyEquiv.symm (f b)) = toCopy X
        rw [show toCopy (copyEquiv.symm (f b)) = f b from copyEquiv.apply_symm_apply _]
        exact hb
      · rintro ⟨b,rfl⟩
        exact ⟨b,(copyEquiv.apply_symm_apply (f b)).symm⟩
    rw [hEq]
    exact RamseySpace.prefixContinuous_range_isRamsey CriticalCopies.ramseySpace
      CriticalCopies.closed F (prefixContinuous_of_continuous f hf)

end AllThoseBigRamsey.Pseudotree.DiaryExpansion
