import PseudotreeValidation.SlotReservoirs
import PseudotreeValidation.RelativeSlots

/-! Initialization of a relative reservoir frontier, from actual
rational reservoirs in the prescribed incoming cones. The assigned
target is allowed to vary between slots; no common target-copy
hypothesis is imposed. -/

namespace AllThoseBigRamsey.Pseudotree.Reservoir
open LowerGeometry RayEmbeddings RayMapModel
open SparseNormalization (critical)
open CriticalCopies (FiniteCritical Node Boundary slot oldParent)
open scoped FirstOrder

/-- All the required initialization data on a fixed whole-block frontier.
This is the exact input obtained by using slot rays in the ambient copy
or in the given critical subcopy, according to the relevance of a slot. -/
structure BoundarySeeds {j : Nat} (e : FiniteCritical (j+1))
    (targets : Word → Target) where
  copies : Boundary j → RayCopy
  inside : ∀ u, Set.range (copies u).embedding ⊆ Set.range (targets u.val)
  tail : ∀ u q, ∃ b : Sparse.Word,
    fromBlocks (copies u q) = (slot e u).map toLetter ++ b ∧
      (last u ≠ 1 → .one ∉ b)

/-- Simultaneously refine arbitrary boundary reservoirs past the top
height and every ray address. The synchronized prefixes retain the
required incoming digit and binary padding. -/
theorem relativeInitial {j : Nat} {e : FiniteCritical (j+1)}
    {targets : Word → Target} (Q : BoundarySeeds e targets) :
    ∃ P : Layer sparseSource targets (j+1),
      e.level j < P.bound ∧
      ∀ u : Boundary j, ∃ b : Sparse.Word,
        P.prefixes u = (slot e u).map toLetter ++ b ∧
          (last u ≠ 1 → .one ∉ b) := by
  classical
  obtain ⟨L,hL,R,p,_,hsub,hlen,hp,hroot⟩ :=
    LowerRealization.finite_common_prefix Q.copies (e.level j)
  have ht (u : Boundary j) : ∃ b : Sparse.Word,
      p u = (slot e u).map toLetter ++ b ∧ (last u ≠ 1 → .one ∉ b) := by
    obtain ⟨q,hq⟩ := hsub u ⟨0,rfl⟩
    obtain ⟨b,hb,hbin⟩ := Q.tail u q
    have hpre : (slot e u).map toLetter <+: fromBlocks (R u 0) := by
      rw [← hq,hb]
      exact List.prefix_append _ _
    have hs : (slot e u).map toLetter <+: p u :=
      List.prefix_of_prefix_length_le hpre (hp u 0) (by
        rw [List.length_map,CriticalCopies.slot_length,hlen]
        omega)
    obtain ⟨c,hc⟩ := hs
    refine ⟨c,hc.symm,?_⟩
    intro ha
    have hcb : c <+: b := by
      have h := hp u 0
      rw [← hc,← hq,hb] at h
      exact (List.prefix_append_right_inj _).mp h
    exact fun hm => hbin ha (hcb.subset hm)
  let P : Layer sparseSource targets (j+1) := {
    bound := L
    copies := R
    prefixes := p
    prefix_length := hlen
    common_prefix := hp
    root_short := hroot
    inside := fun u => (hsub u).trans (Q.inside u)
    ordered := by
      intro u v huv
      have hlt := CriticalCopies.slot_ordered e u v huv
      obtain ⟨b,hb,_⟩ := ht u
      obtain ⟨c,hc,_⟩ := ht v
      rw [hb,hc,Sparse.lexLess_append_of_ne
        (by simp only [List.length_map,CriticalCopies.slot_length])
        (fun h => (ne_of_lt hlt) (SparseNormalization.map_toLetter_eq.mp h))]
      exact (Sparse.lexLess_fin_iff _ _).mpr hlt }
  exact ⟨P,hL,ht⟩

/-- Each reservoir step retains explicit prefix witnesses in the
assigned structural copy. This follows directly from the next-layer
reservoirs and needs no new geometry. -/
theorem Step.root_supported {targets : Word → Target} {j : Nat}
    {P : Layer sparseSource targets j} (S : Step P)
    (stable : ∀ (u : Level sparseSource j) a, child u.val a ∈ sparseSource.nodes →
      targets (child u.val a) = targets u.val) (u : Level sparseSource j) :
    ∃ z ∈ Set.range (targets u.val), (S.roots u).IsPrefix (fromBlocks z) := by
  have htree : SparseNormalization.Tree u.val := u.property.1
  have hchild : ∃ a : Fin 3, SparseNormalization.Tree (child u.val a) := by
    by_cases hc : u.val = SparseNormalization.critical j
    · by_cases hm : j % 3 = 2
      · exact ⟨1,(SparseNormalization.tree_children j u.val htree u.property.2 1).mpr
          (by simp [hc,hm])⟩
      · exact ⟨0,(SparseNormalization.tree_children j u.val htree u.property.2 0).mpr
          (by simp [hc,hm])⟩
    · by_cases hl : u.val < SparseNormalization.critical j
      · exact ⟨0,(SparseNormalization.tree_children j u.val htree u.property.2 0).mpr
          (by simp [hc,hl])⟩
      · exact ⟨2,(SparseNormalization.tree_children j u.val htree u.property.2 2).mpr
          (by simp [hc,hl])⟩
  obtain ⟨a,ha⟩ := hchild
  let v := childNode u a ha
  let z := S.next.copies v 0
  have hz := S.next.inside v ⟨0,rfl⟩
  change z ∈ Set.range (targets (child u.val a)) at hz
  rw [stable u a ha] at hz
  obtain ⟨b,hb,_⟩ := S.edge u a ha
  refine ⟨z,hz,?_⟩
  have hp := S.next.common_prefix v 0
  rw [hb] at hp
  exact (List.prefix_append _ _).trans hp

/-- A split is witnessed by two actual points of the assigned copy
with different next digits, at exactly the selected height. -/
theorem Step.split_supported {targets : Word → Target} {j : Nat}
    {P : Layer sparseSource targets j} (S : Step P)
    (stable : ∀ (u : Level sparseSource j) a, child u.val a ∈ sparseSource.nodes →
      targets (child u.val a) = targets u.val) (hj : j % 3 ≠ 2) :
    ∃ y ∈ Set.range (targets (SparseNormalization.critical j)), ∃ z ∈ Set.range (targets (SparseNormalization.critical j)),
      (S.roots (criticalAt sparseSource j) ++ [TernaryLetter.zero]).IsPrefix (fromBlocks y) ∧
      (S.roots (criticalAt sparseSource j) ++ [TernaryLetter.two]).IsPrefix (fromBlocks z) := by
  let u := criticalAt sparseSource j
  have ha0 : SparseNormalization.Tree (child u.val 0) := by
    change SparseNormalization.Tree (child (SparseNormalization.critical j) 0)
    have hc : SparseNormalization.Tree (SparseNormalization.critical j) := (CriticalCopies.criticalNode j).property
    rw [SparseNormalization.tree_children j (SparseNormalization.critical j) hc
      (SparseNormalization.critical_length j)]
    simp [hj]
  have ha2 : SparseNormalization.Tree (child u.val 2) := by
    change SparseNormalization.Tree (child (SparseNormalization.critical j) 2)
    have hc : SparseNormalization.Tree (SparseNormalization.critical j) := (CriticalCopies.criticalNode j).property
    rw [SparseNormalization.tree_children j (SparseNormalization.critical j) hc
      (SparseNormalization.critical_length j)]
    simp [hj]
  let u0 := childNode u 0 ha0
  let u2 := childNode u 2 ha2
  have h0 := S.next.inside u0 ⟨0,rfl⟩
  have h2 := S.next.inside u2 ⟨0,rfl⟩
  change S.next.copies u0 0 ∈ Set.range (targets (child u.val 0)) at h0
  change S.next.copies u2 0 ∈ Set.range (targets (child u.val 2)) at h2
  rw [stable u 0 ha0] at h0
  rw [stable u 2 ha2] at h2
  refine ⟨S.next.copies u0 0,h0,S.next.copies u2 0,h2,?_,?_⟩
  · obtain ⟨b,hb,_⟩ := S.edge u 0 ha0
    have hp := S.next.common_prefix u0 0
    rw [hb] at hp
    have hh : (S.roots (criticalAt sparseSource j) ++ [TernaryLetter.zero] ++ b).IsPrefix
        (fromBlocks (S.next.copies u0 0)) := by
      change (S.roots u ++ [TernaryLetter.zero] ++ b).IsPrefix _
      have hzero : toLetter (0 : Fin 3) = TernaryLetter.zero := rfl
      simpa only [ReservoirChart.original,List.append_assoc,List.singleton_append,hzero] using hp
    exact (List.prefix_append _ _).trans hh
  · obtain ⟨b,hb,_⟩ := S.edge u 2 ha2
    have hp := S.next.common_prefix u2 0
    rw [hb] at hp
    have hh : (S.roots (criticalAt sparseSource j) ++ [TernaryLetter.two] ++ b).IsPrefix
        (fromBlocks (S.next.copies u2 0)) := by
      change (S.roots u ++ [TernaryLetter.two] ++ b).IsPrefix _
      have htwo : toLetter (2 : Fin 3) = TernaryLetter.two := rfl
      simpa only [ReservoirChart.original,List.append_assoc,List.singleton_append,htwo] using hp
    exact (List.prefix_append _ _).trans hh

end AllThoseBigRamsey.Pseudotree.Reservoir
