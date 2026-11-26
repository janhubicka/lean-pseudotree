import RamseySpace.TwoSorted.SouslinClosure
import RamseySpace.TwoSorted.Diagonal
import RamseySpace.Standard

/-! Analytic-image transfer through finite approximations. This lemma
does not assume a topology on the point type. The relevant continuity
condition is exactly that each finite approximation of a Baire-space
image is determined locally by a finite initial segment of the branch.
The existing two-sorted Souslin theorem supplies the Ramsey conclusion. -/
namespace RamseySpace
open Souslin

universe u v
variable {S : ApproximationSystem.{u,v}}

/-- Any set determined by a single finite approximation is Ramsey. -/
theorem isRamsey_of_approxDependent
    (R : AbstractRamseySpace S) (hclosed : S.IsMetricallyClosed)
    (A : Set S.Point) (m : Nat)
    (hA : ∀ X Y, S.approx m X = S.approx m Y → (X ∈ A ↔ Y ∈ A)) :
    IsRamsey R A := by
  apply IsAbstractBaire.isRamsey R (fusionComplete_of_isMetricallyClosed R hclosed)
  intro n a Y hne
  obtain ⟨X,hX⟩ := hne
  let j := max n m
  have hn : n ≤ j := le_max_left _ _
  have hm : m ≤ j := le_max_right _ _
  have ha : S.IsInitial a (S.approx j X) := by
    rw [← hX.2]
    exact S.isInitial_of_point hn X
  refine ⟨j,S.approx j X,X,ha,hX.1,⟨X,S.le_refl X,rfl⟩,?_⟩
  have he (Z : S.Point) (hZ : Z ∈ S.neighborhood (S.approx j X) X) :
      Z ∈ A ↔ X ∈ A := by
    apply hA
    rcases lt_or_eq_of_le hm with hlt | heq
    · exact S.coherent hZ.2 m hlt
    · rw [heq]
      exact hZ.2
  by_cases hmem : X ∈ A
  · exact Or.inl (fun Z hZ => (he Z hZ).mpr hmem)
  · exact Or.inr (Set.disjoint_left.mpr (fun Z hZ hZA => hmem ((he Z hZ).mp hZA)))

/-- A formulation of local continuity in the approximation metric.
It is the finite-prefix form of continuity of every discrete
approximation coordinate. -/
def PrefixContinuous (F : (Nat → Nat) → S.Point) : Prop :=
  ∀ b m, ∃ k : Nat, ∀ c : Nat → Nat,
    branchPrefix c k = branchPrefix b k →
      S.approx m (F c) = S.approx m (F b)

/-- At a node of the Souslin scheme, retain all possible images of
branches through the node, modulo its finite approximation. -/
def approxImageScheme (F : (Nat → Nat) → S.Point) : Scheme S.Point :=
  fun s => {X | ∃ b : Nat → Nat, Extends b s ∧
    S.approx s.length X = S.approx s.length (F b)}

theorem operation_approxImageScheme (F : (Nat → Nat) → S.Point)
    (hF : PrefixContinuous (S := S) F) :
    operation (approxImageScheme (S := S) F) = Set.range F := by
  ext X
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨b,?_⟩
    apply S.separated
    intro m
    obtain ⟨k,hk⟩ := hF b m
    let n := max k m
    obtain ⟨c,hc,hX⟩ := hb n
    have hprefix : branchPrefix c n = branchPrefix b n := by
      unfold Extends at hc
      simpa only [length_branchPrefix] using hc
    have hpre : branchPrefix c k = branchPrefix b k := by
      have hh := congrArg (List.take k) hprefix
      rwa [take_branchPrefix c (le_max_left k m),take_branchPrefix b (le_max_left k m)] at hh
    have hn : S.approx n X = S.approx n (F c) := by
      simpa only [length_branchPrefix] using hX
    have hm : S.approx m X = S.approx m (F c) := by
      rcases lt_or_eq_of_le (show m ≤ n from le_max_right k m) with hlt | heq
      · exact S.coherent hn m hlt
      · rw [heq]
        exact hn
    exact (hm.trans (hk c hpre)).symm
  · rintro ⟨b,rfl⟩
    refine ⟨b,fun n => ⟨b,?_,rfl⟩⟩
    unfold Extends
    rw [length_branchPrefix]

/-- Every locally prefix-continuous Baire-space image is completely
Ramsey. This uses the pinned checked Souslin closure on the diagonal,
not a new Ramsey-theoretic assumption. -/
theorem prefixContinuous_range_isRamsey
    (R : AbstractRamseySpace S) (hclosed : S.IsMetricallyClosed)
    (F : (Nat → Nat) → S.Point) (hF : PrefixContinuous (S := S) F) :
    IsRamsey R (Set.range F) := by
  rw [← operation_approxImageScheme F hF]
  apply (TwoSorted.diagonal_isRamsey_iff R _).mp
  apply TwoSorted.isRamsey_souslin (TwoSorted.diagonalAbstractRamseySystem R)
    (fusionComplete_of_isMetricallyClosed R hclosed)
  intro s
  apply (TwoSorted.diagonal_isRamsey_iff R _).mpr
  apply isRamsey_of_approxDependent R hclosed _ s.length
  intro X Y heq
  change (∃ b, Extends b s ∧ S.approx s.length X = S.approx s.length (F b)) ↔
    (∃ b, Extends b s ∧ S.approx s.length Y = S.approx s.length (F b))
  rw [heq]

end RamseySpace
