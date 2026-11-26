import PseudotreeValidation.RelativeSlots
import PseudotreeValidation.NextBlockMilliken

/-! Extract synchronized suffix maps from a strong map fixing the old
block. The first retained edge supplies the binary-root condition.
Transporting the suffix family along the relevant-slot injection gives
the precise forest input to the relative FIFO formula. -/

namespace AllThoseBigRamsey.Pseudotree.CriticalCopies
open RayEmbeddings RayMapModel
open SparseNormalization (critical critical_length tree_prefix)
open Reservoir (sparseSource)

namespace ConeSuffix

/-- Every descendant of a retained root has the same literal prefix. -/
theorem descendant_prefix {f : RayStrongMap} {w : Word} (hw : w.IsPrefix (f.map w)) (z : Word) :
    w.IsPrefix (f.map (w ++ z)) :=
  hw.trans (DiaryRecovery.map_prefix f (List.prefix_append w z))

def value (f : RayStrongMap) (w z : Word) : Word :=
  (f.map (w ++ z)).drop w.length

theorem append_value {f : RayStrongMap} {w : Word}
    (hw : w.IsPrefix (f.map w)) (z : Word) :
    w ++ value f w z = f.map (w ++ z) := by
  have he := List.prefix_iff_eq_take.mp (descendant_prefix hw z)
  calc
    w ++ value f w z = (f.map (w++z)).take w.length ++ value f w z :=
      congrArg (fun p => p ++ value f w z) he
    _ = f.map (w++z) := List.take_append_drop _ _

/-- Removal of the fixed literal cone root does not affect any edge
condition, and removes the same constant from all image heights. -/
def map (f : RayStrongMap) (w : Word) (hw : w.IsPrefix (f.map w)) : RayStrongMap where
  map := value f w
  level := fun i => f.level (w.length+i)-w.length
  level_strict := by
    intro i j hij
    have h := f.level_strict (Nat.add_lt_add_left hij w.length)
    have hlo := hw.length_le
    rw [f.length_map] at hlo
    have hle : f.level w.length ≤ f.level (w.length+i) := by
      have hmono : StrictMono f.level := fun _ _ h => f.level_strict h
      exact hmono.monotone (by omega)
    omega
  length_map := by
    intro z
    simp only [value,List.length_drop,f.length_map,List.length_append]
  step := by
    intro z a
    obtain ⟨p,hp,hpb⟩ := f.step (w++z) a
    have he : w ++ value f w (z++[a]) =
        w ++ (value f w z ++ a :: p) := by
      rw [append_value hw,← List.append_assoc, hp,← append_value hw]
      simp only [List.append_assoc]
    exact ⟨p,List.append_cancel_left he,hpb⟩

theorem map_apply {f : RayStrongMap} {w : Word}
    (hw : w.IsPrefix (f.map w)) (z : Word) :
    w ++ (map f w hw).map z = f.map (w++z) :=
  append_value hw z

end ConeSuffix

/-- A strong map fixing the old block maps every immediate source slot
to that slot with padding, binary precisely when the incoming edge is
binary. This includes roots of all relevant binary factors. -/
theorem fixesSlot {n : Nat} (hn : 0 < n) (f : RayStrongMap)
    (hf : FixesBlock f n) (w : Boundary (3*n-1)) :
    ∃ p : Word, f.map w.val = w.val ++ p ∧
      (Reservoir.last w ≠ 1 → Binary p) := by
  let u := oldParent w
  let a := Reservoir.last w
  have hu : u.val.length < 3*n := by
    rw [show u.val.length = 3*n-1 from oldParent_length w]
    omega
  have hparent : u.val ++ [a] = w.val := Reservoir.child_parent w
  obtain ⟨p,hp,hbin⟩ := f.step u.val a
  rw [hparent,hf u hu] at hp
  exact ⟨p,by simpa only [← hparent,List.append_assoc,List.singleton_append] using hp,hbin⟩

theorem fixesSlot_prefix {n : Nat} (hn : 0 < n) (f : RayStrongMap)
    (hf : FixesBlock f n) (w : Boundary (3*n-1)) :
    w.val.IsPrefix (f.map w.val) := by
  obtain ⟨p,hp,_⟩ := fixesSlot hn f hf w
  exact ⟨p,hp.symm⟩

/-- The common level schedule and all binary-root conditions are derived,
not added as assumptions. -/
def slotMapsOfStrong {n : Nat} (hn : 0 < n) (f : RayStrongMap)
    (hf : FixesBlock f n) : SlotMaps (3*n-1) where
  maps w := ConeSuffix.map f w.val (fixesSlot_prefix hn f hf w)
  level i := f.level ((3*n-1)+1+i)-((3*n-1)+1)
  strict := by
    intro i j hij
    have h := f.level_strict (Nat.add_lt_add_left hij ((3*n-1)+1))
    have hlo := fixesBlock_level f hn hf
    have hlt := f.level_strict (show 3*n-1 < (3*n-1)+1+i by omega)
    change f.level ((3*n-1)+1+i)-((3*n-1)+1) <
      f.level ((3*n-1)+1+j)-((3*n-1)+1)
    omega
  levels := by
    intro w i
    change f.level (w.val.length+i)-w.val.length = _
    rw [w.property.2]
  binary_root := by
    intro w ha
    obtain ⟨p,hp,hbin⟩ := fixesSlot hn f hf w
    change Binary ((f.map (w.val++[])).drop w.val.length)
    rw [List.append_nil,hp,List.drop_left' rfl]
    exact hbin ha

/-- Exact local action of the suffix family on all future nodes. -/
theorem slotMapsOfStrong_apply {n : Nat} (hn : 0 < n) (f : RayStrongMap)
    (hf : FixesBlock f n) (w : Boundary (3*n-1)) (z : Word) :
    w.val ++ ((slotMapsOfStrong hn f hf).maps w).map z = f.map (w.val++z) :=
  ConeSuffix.map_apply (fixesSlot_prefix hn f hf w) z

/-- Identity on the old block gives a canonical lower embedding for
any chosen synchronized family of suffix maps. This is the reverse
direction of the finite-gadget forest representation. -/
noncomputable def suffixLiftMap {j : Nat} (G : SlotMaps j) (w : Word) : Word := by
  classical
  exact if hw : SparseNormalization.Tree w ∧ j+1 ≤ w.length then
    let u := boundaryOf w hw.1 hw.2
    u.val ++ (G.maps u).map (w.drop (j+1))
  else w

theorem suffixLiftMap_eq {j : Nat} (G : SlotMaps j)
    (w : Word) (hw : SparseNormalization.Tree w) (hl : j+1 ≤ w.length) :
    suffixLiftMap G w =
      (boundaryOf w hw hl).val ++ (G.maps (boundaryOf w hw hl)).map (w.drop (j+1)) := by
  simp [suffixLiftMap,hw,hl]

theorem suffixLiftMap_old {j : Nat} (G : SlotMaps j)
    (w : Word) (hw : w.length < j+1) : suffixLiftMap G w = w := by
  simp [suffixLiftMap,show ¬ j+1 ≤ w.length by omega]

def suffixLiftLevels {j : Nat} (G : SlotMaps j) (i : Nat) : Nat :=
  if i < j+1 then i else j+1+G.level (i-(j+1))

theorem suffixLiftLevels_strict {j : Nat} (G : SlotMaps j) :
    StrictMono (suffixLiftLevels G) := by
  intro i k hik
  by_cases hk : k < j+1
  · simp [suffixLiftLevels,hk,hik.trans hk,hik]
  · by_cases hi : i < j+1
    · simp only [suffixLiftLevels,if_pos hi,if_neg hk]
      omega
    · simp only [suffixLiftLevels,if_neg hi,if_neg hk]
      exact Nat.add_lt_add_left (G.strict (by omega)) _

/-- A synchronized family is realized by one total ray-preserving
strong map on the literal R domain, fixing the whole old block.
Only ordinary completion is used outside R. -/
noncomputable def suffixLift {j : Nat} (G : SlotMaps j) : PrefixRayMap SparseNormalization.Tree where
  root_mem := sparseSource.root_mem
  prefix_closed := fun s t h => tree_prefix h (List.prefix_append s t)
  map := suffixLiftMap G
  level := suffixLiftLevels G
  level_strict := fun h => suffixLiftLevels_strict G h
  length_map := by
    intro w hw
    by_cases hl : w.length < j+1
    · rw [suffixLiftMap_old G w hl,suffixLiftLevels,if_pos hl]
    · rw [suffixLiftMap_eq G w hw (by omega),suffixLiftLevels,if_neg hl,
        List.length_append,(G.maps _).length_map,G.levels,List.length_drop]
      rw [(boundaryOf w hw (by omega : j+1 ≤ w.length)).property.2]
  step := by
    intro s a hs
    have hs0 := tree_prefix hs (List.prefix_append s [a])
    by_cases hchild : (s++[a]).length < j+1
    · have hparent : s.length < j+1 := by simp at hchild; omega
      rw [suffixLiftMap_old G _ hchild,suffixLiftMap_old G _ hparent]
      exact ⟨[],rfl,fun _ => binary_nil⟩
    · by_cases hparent : j+1 ≤ s.length
      · have hl' : j+1 ≤ (s++[a]).length := by simp; omega
        rw [suffixLiftMap_eq G _ hs hl',suffixLiftMap_eq G _ hs0 hparent,
          boundaryOf_append s a hs hparent]
        have hdrop : (s++[a]).drop (j+1) = s.drop (j+1)++[a] := by
          simp [List.drop_append,Nat.sub_eq_zero_of_le hparent]
        rw [hdrop]
        obtain ⟨p,hp,hpb⟩ := (G.maps (boundaryOf s hs0 hparent)).step (s.drop (j+1)) a
        exact ⟨p,by rw [hp,List.append_assoc],hpb⟩
      · have hl : (s++[a]).length = j+1 := by simp at hchild ⊢; omega
        have hparent' : s.length = j := by simp at hl; omega
        let u : Boundary j := ⟨s++[a],hs,hl⟩
        have hu : boundaryOf (s++[a]) hs hl.ge = u := by
          apply Subtype.ext
          exact List.take_of_length_le hl.le
        rw [suffixLiftMap_eq G _ hs hl.ge,suffixLiftMap_old G _ (by omega),
          hu,List.drop_of_length_le hl.le]
        have hlast : Reservoir.last u = a := by
          let v : Reservoir.Level sparseSource j := ⟨s,hs0,hparent'⟩
          exact Reservoir.last_childNode v a hs
        refine ⟨(G.maps u).map [],?_,fun ha => G.binary_root u (by rwa [hlast])⟩
        change (s++[a])++(G.maps u).map [] = s++a::(G.maps u).map []
        simp only [List.append_assoc,List.singleton_append]

theorem suffixLift_agrees {j : Nat} (G : SlotMaps j) (w : Word)
    (hw : SparseNormalization.Tree w) :
    (suffixLift G).completion.map w = suffixLiftMap G w :=
  PrefixRayMap.completion_agrees _ _ hw

theorem suffixLift_fixesBlock {n : Nat} (hn : 0 < n) (G : SlotMaps (3*n-1)) :
    FixesBlock (suffixLift G).completion n := by
  intro u hu
  rw [suffixLift_agrees G u.val u.property,suffixLiftMap_old]
  omega

end AllThoseBigRamsey.Pseudotree.CriticalCopies
