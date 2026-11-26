import PseudotreeValidation.SlotSuffixMaps
import PseudotreeValidation.CriticalDepth

/-!
# Transport of synchronized slot maps

A finite critical prefix determines an ordered injection between live
frontiers, preserving the entering digit. Restrict an ambient family
of FIFO label roots to those slots; extend a synchronized family of
suffix maps in the reverse direction by binary zero padding on the
unused slots. These operations use the actual finite critical prefix.
-/

namespace AllThoseBigRamsey.Pseudotree.CriticalCopies
open RayEmbeddings RayMapModel
open SparseNormalization (critical critical_length tree_prefix)
open Reservoir (sparseSource)

theorem slot_identity_word {j : Nat} (w : Boundary j) :
    slot (restrictCritical identity (j+1)) w = w.val :=
  Reservoir.child_parent w

/-- A finite critical map whose last level is a coding level. -/
structure SlotTransport (j k : Nat) where
  prefixMap : FiniteCritical (j+1)
  source_phase : j % 3 = 2
  top : prefixMap.level j = k

namespace SlotTransport

def inject (T : SlotTransport j k) (w : Boundary j) : Boundary k :=
  ⟨slot T.prefixMap w, slot_tree T.prefixMap T.source_phase w,
    (slot_length T.prefixMap w).trans (congrArg (·+1) T.top)⟩

theorem inject_val (T : SlotTransport j k) (w : Boundary j) :
    (T.inject w).val = slot T.prefixMap w := rfl

theorem inject_ordered (T : SlotTransport j k) (u v : Boundary j) (h : u.val < v.val) :
    (T.inject u).val < (T.inject v).val :=
  slot_ordered T.prefixMap u v h

theorem inject_injective (T : SlotTransport j k) : Function.Injective T.inject := by
  intro u v h
  rcases lt_trichotomy u.val v.val with hlt | heq | hgt
  · have ht := T.inject_ordered u v hlt
    rw [h] at ht
    exact False.elim (lt_irrefl _ ht)
  · exact Subtype.ext heq
  · have ht := T.inject_ordered v u hgt
    rw [h] at ht
    exact False.elim (lt_irrefl _ ht)

/-- This includes the unique ternary slot, not merely the binary ones. -/
theorem inject_last (T : SlotTransport j k) (w : Boundary j) :
    Reservoir.last (T.inject w) = Reservoir.last w := by
  have hw := Reservoir.child_parent (T.inject w)
  have he' : (some (Reservoir.last (T.inject w)) : Option (Fin 3)) =
      some (Reservoir.last w) := by
    change (Reservoir.parent (T.inject w)).val ++ [Reservoir.last (T.inject w)] =
      slot T.prefixMap w at hw
    simpa only [child,slot,List.getLast?_concat] using congrArg List.getLast? hw
  exact Option.some.inj he'

/-- The relevant source slots use exactly the ambient label roots,
not a second independently chosen synchronized family. -/
def restrictRoots (T : SlotTransport j k)
    (B : SlotFamily (restrictCritical identity (k+1))) : SlotFamily T.prefixMap where
  k := B.k
  root w := B.root (T.inject w)
  length w := B.length (T.inject w)
  ordered u v h := B.ordered _ _ (T.inject_ordered u v h)
  head := by
    intro w
    simpa only [slot_identity_word,inject_val] using B.head (T.inject w)

end SlotTransport

namespace SlotMaps

/-- A strong map with arbitrary prescribed increasing levels, using
only zero padding. It can fill every unused ambient slot. -/
def zeroPrefix (L : Nat → Nat) (hL : StrictMono L) : PrefixRayMap (fun w : Word => w = []) where
    root_mem := rfl
    prefix_closed := by
      intro s t h
      change s ++ t = [] at h
      cases s <;> simp_all
    map := fun _ => List.replicate (L 0) 0
    level := L
    level_strict := fun h => hL h
    length_map := by intro w hw; subst w; simp
    step := by intro s a hs; simp at hs


noncomputable def zeroMap (L : Nat → Nat) (hL : StrictMono L) : RayStrongMap :=
  (zeroPrefix L hL).completion

theorem zeroMap_level (L : Nat → Nat) (hL : StrictMono L) (i : Nat) :
    (zeroMap L hL).level i = L i := rfl

theorem zeroMap_binary_root (L : Nat → Nat) (hL : StrictMono L) :
    Binary ((zeroMap L hL).map []) := by
  change Binary ((zeroPrefix L hL).completion.map [])
  rw [PrefixRayMap.completion_agrees (zeroPrefix L hL) [] rfl]
  change Binary (List.replicate (L 0) 0)
  intro a ha
  rw [List.eq_of_mem_replicate ha]
  decide

noncomputable def transportMap (T : SlotTransport j k) (G : SlotMaps j)
    (v : Boundary k) : RayStrongMap := by
  classical
  exact if h : ∃ w, T.inject w = v then G.maps h.choose
    else zeroMap G.level G.strict

theorem transportMap_inject (T : SlotTransport j k) (G : SlotMaps j) (w : Boundary j) :
    transportMap T G (T.inject w) = G.maps w := by
  classical
  unfold transportMap
  have h : ∃ u, T.inject u = T.inject w := ⟨w,rfl⟩
  rw [dif_pos h]
  rw [T.inject_injective h.choose_spec]

noncomputable def transport (T : SlotTransport j k) (G : SlotMaps j) : SlotMaps k where
  maps := transportMap T G
  level := G.level
  strict := G.strict
  levels := by
    classical
    intro v i
    unfold transportMap
    split
    · exact G.levels _ i
    · exact zeroMap_level _ _ _
  binary_root := by
    classical
    intro v hv
    unfold transportMap
    split
    · rename_i h
      have hlast := T.inject_last h.choose
      rw [h.choose_spec] at hlast
      exact G.binary_root _ (hlast ▸ hv)
    · exact zeroMap_binary_root _ _

@[simp] theorem transport_inject (T : SlotTransport j k) (G : SlotMaps j) (w : Boundary j) :
    (transport T G).maps (T.inject w) = G.maps w :=
  transportMap_inject T G w

/-- Synchronized composition retains binary roots in every binary slot. -/
def comp (G H : SlotMaps j) : SlotMaps j where
  maps w := (G.maps w).comp (H.maps w)
  level := G.level ∘ H.level
  strict := G.strict.comp H.strict
  levels := by
    intro w i
    change (G.maps w).level ((H.maps w).level i) = G.level (H.level i)
    rw [G.levels,H.levels]
  binary_root := by
    intro w hw
    obtain ⟨p,hp,he⟩ := (G.maps w).maps_binary_ray [] ((H.maps w).map [])
      (H.binary_root w hw)
    change Binary ((G.maps w).map ((H.maps w).map []))
    rw [show [] ++ (H.maps w).map [] = (H.maps w).map [] by rfl] at he
    rw [he,binary_append]
    exact ⟨G.binary_root w hw,hp⟩

end SlotMaps

namespace BetweenCones

/-- Unlike ConeSuffix, the retained target cone can have a different
length from the source cone. The common subtraction is the target
slot height, so all suffix maps still synchronize. -/
def value (f : RayStrongMap) (w v z : Word) : Word :=
  (f.map (w ++ z)).drop v.length

theorem append_value {f : RayStrongMap} {w v : Word}
    (hv : v.IsPrefix (f.map w)) (z : Word) :
    v ++ value f w v z = f.map (w++z) := by
  have hp := hv.trans (DiaryRecovery.map_prefix f (List.prefix_append w z))
  have he := List.prefix_iff_eq_take.mp hp
  calc
    v ++ value f w v z = (f.map (w++z)).take v.length ++ value f w v z :=
      congrArg (fun p => p ++ value f w v z) he
    _ = f.map (w++z) := List.take_append_drop _ _

def map (f : RayStrongMap) (w v : Word) (hv : v.IsPrefix (f.map w)) : RayStrongMap where
  map := value f w v
  level := fun i => f.level (w.length+i)-v.length
  level_strict := by
    intro i j hij
    have h := f.level_strict (Nat.add_lt_add_left hij w.length)
    have hlo := hv.length_le
    rw [f.length_map] at hlo
    have hm : StrictMono f.level := fun _ _ h => f.level_strict h
    have hle := hm.monotone (show w.length ≤ w.length+i by omega)
    omega
  length_map := by
    intro z
    simp only [value,List.length_drop,f.length_map,List.length_append]
  step := by
    intro z a
    obtain ⟨p,hp,hpb⟩ := f.step (w++z) a
    have he : v ++ value f w v (z++[a]) =
        v ++ (value f w v z ++ a :: p) := by
      calc
        v ++ value f w v (z++[a]) = f.map (w++(z++[a])) := append_value hv _
        _ = f.map ((w++z)++[a]) := by rw [List.append_assoc]
        _ = f.map (w++z) ++ a :: p := hp
        _ = v ++ (value f w v z ++ a :: p) := by
          rw [← append_value hv z,List.append_assoc]
    exact ⟨p,List.append_cancel_left he,hpb⟩

theorem map_apply {f : RayStrongMap} {w v : Word}
    (hv : v.IsPrefix (f.map w)) (z : Word) :
    v ++ (map f w v hv).map z = f.map (w++z) :=
  append_value hv z

end BetweenCones

namespace SlotTransport

theorem image_boundary (T : SlotTransport j k) (H : CriticalMap)
    (he : Extends H T.prefixMap) (w : Boundary j) :
    ∃ p : Word, (total H).map w.val = (T.inject w).val ++ p ∧
      (Reservoir.last w ≠ 1 → Binary p) := by
  let u := oldParent w
  let a := Reservoir.last w
  have hlen : u.val.length < j+1 := by rw [oldParent_length]; omega
  have hform : u.val ++ [a] = w.val := Reservoir.child_parent w
  obtain ⟨p,hp,hpb⟩ := (total H).step u.val a
  rw [hform,total_agrees H u,he u hlen] at hp
  refine ⟨p,?_,hpb⟩
  change (total H).map w.val = (T.prefixMap.map u ++ [a]) ++ p
  simpa only [List.append_assoc,List.singleton_append] using hp

theorem image_boundary_prefix (T : SlotTransport j k) (H : CriticalMap)
    (he : Extends H T.prefixMap) (w : Boundary j) :
    (T.inject w).val.IsPrefix ((total H).map w.val) := by
  obtain ⟨p,hp,_⟩ := T.image_boundary H he w
  exact ⟨p,hp.symm⟩

theorem image_boundary_level (T : SlotTransport j k) (H : CriticalMap)
    (he : Extends H T.prefixMap) :
    k+1 ≤ H.level (j+1) := by
  have hl : H.level j = k := by
    change (H.map (criticalNode j)).length = k
    rw [he _ (by simp)]
    exact T.top
  have hlt := H.level_strict (Nat.lt_succ_self j)
  change H.level j < H.level (j+1) at hlt
  omega

/-- Recover the actual synchronized suffixes of any critical map
extending the prescribed prefix. This is the pullback forest family. -/
noncomputable def suffixes (T : SlotTransport j k) (H : CriticalMap)
    (he : Extends H T.prefixMap) : SlotMaps j where
  maps w := BetweenCones.map (total H) w.val (T.inject w).val
    (T.image_boundary_prefix H he w)
  level i := H.level (j+1+i)-(k+1)
  strict := by
    intro i l hil
    have hlt := H.level_strict (Nat.add_lt_add_left hil (j+1))
    change H.level (j+1+i) < H.level (j+1+l) at hlt
    have hm : H.level (j+1) ≤ H.level (j+1+i) :=
      H.level_strict.monotone (show j+1 ≤ j+1+i by omega)
    have hlo := T.image_boundary_level H he
    change H.level (j+1+i)-(k+1) < H.level (j+1+l)-(k+1)
    omega
  levels := by
    intro w i
    change H.level (w.val.length+i)-(T.inject w).val.length = _
    rw [w.property.2,(T.inject w).property.2]
  binary_root := by
    intro w ha
    obtain ⟨p,hp,hpb⟩ := T.image_boundary H he w
    change Binary (((total H).map (w.val++[])).drop (T.inject w).val.length)
    rw [List.append_nil,hp,List.drop_left' rfl]
    exact hpb ha

theorem suffixes_apply (T : SlotTransport j k) (H : CriticalMap)
    (he : Extends H T.prefixMap) (w : Boundary j) (z : Word) :
    (T.inject w).val ++ ((T.suffixes H he).maps w).map z =
      (total H).map (w.val++z) :=
  BetweenCones.map_apply (T.image_boundary_prefix H he w) z

theorem suffixes_node (T : SlotTransport j k) (H : CriticalMap)
    (he : Extends H T.prefixMap) (u : Node) (hu : j+1 ≤ u.val.length) :
    let w := boundaryOf u.val u.property hu
    H.map u = (T.inject w).val ++ ((T.suffixes H he).maps w).map (u.val.drop (j+1)) := by
  dsimp only
  let w := boundaryOf u.val u.property hu
  have h := T.suffixes_apply H he w (u.val.drop (j+1))
  change (T.inject w).val ++ ((T.suffixes H he).maps w).map (u.val.drop (j+1)) =
    (total H).map (u.val.take (j+1) ++ u.val.drop (j+1)) at h
  rw [List.take_append_drop,total_agrees H u] at h
  exact h.symm

/-- The ambient relative lift and the source relative lift use the same
label on every image node. This is an exact equation, not an isomorphism
of finite configurations up to renaming. -/
theorem labels_comp (T : SlotTransport j k)
    (B : SlotFamily (restrictCritical identity (k+1))) (G : SlotMaps j)
    (H : CriticalMap) (he : Extends H T.prefixMap)
    (u : Node) (hu : j+1 ≤ u.val.length) :
    B.labelsMap (SlotMaps.transport T G) (H.map u) =
      (T.restrictRoots B).labelsMap (G.comp (T.suffixes H he)) u.val := by
  let w := boundaryOf u.val u.property hu
  let v := T.inject w
  let z := ((T.suffixes H he).maps w).map (u.val.drop (j+1))
  have hw : H.map u = v.val ++ z := T.suffixes_node H he u hu
  have hlen : k+1 ≤ (H.map u).length := by
    rw [hw,List.length_append,v.property.2]
    omega
  let V := boundaryOf (H.map u) (H.maps_tree u) hlen
  have hv : V = v := by
    apply Subtype.ext
    change (H.map u).take (k+1) = v.val
    rw [hw]
    have hvlen : v.val.length = k+1 := v.property.2
    have ht : (v.val ++ z).take v.val.length = v.val := List.take_append_length
    simpa only [hvlen] using ht
  have hz : (H.map u).drop (k+1) = z := by
    rw [hw]
    exact List.drop_left' v.property.2
  rw [B.labelsMap_eq _ (H.maps_tree u) hlen,
    (T.restrictRoots B).labelsMap_eq _ u.property hu]
  change B.root V ++ ((SlotMaps.transport T G).maps V).map ((H.map u).drop (k+1)) =
    B.root v ++ (G.maps w).map z
  rw [hv,hz,SlotMaps.transport_inject]

/-- Exact relative FIFO locality, including the ambient critical
label and its phase. This proves the comparison used for A.4 at
every future level, not just the three levels of the next gadget. -/
theorem lift_comp (T : SlotTransport j k)
    (B : SlotFamily (restrictCritical identity (k+1))) (G : SlotMaps j)
    (H : CriticalMap) (he : Extends H T.prefixMap)
    (u : Node) (hu : j+1 ≤ u.val.length) :
    (B.tailLabels (SlotMaps.transport T G)).liftWord (H.map u) =
      ((T.restrictRoots B).tailLabels (G.comp (T.suffixes H he))).liftWord u.val := by
  have hnode := T.labels_comp B G H he u hu
  have hc := T.labels_comp B G H he (criticalNode u.val.length) (by simpa using hu)
  have hcrit : H.map (criticalNode u.val.length) = critical (H.map u).length := by
    rw [H.critical_image,← H.length_map u]
  have hphase : (H.map u).length % 3 = 2 ↔ u.val.length % 3 = 2 := by
    rw [H.length_map u]
    exact H.phase _
  have hs : decide ((H.map u).length % 3 ≠ 2) = decide (u.val.length % 3 ≠ 2) := by
    simp only [ne_eq,hphase]
  change B.labelsMap (SlotMaps.transport T G) (H.map (criticalNode u.val.length)) =
    (T.restrictRoots B).labelsMap (G.comp (T.suffixes H he)) (critical u.val.length) at hc
  rw [hcrit] at hc
  -- Make the critical-node equality explicit before rewriting the label.
  unfold TailLabels.liftWord TailLabels.label
  change (Sparse.FIFO.liftedNode
    ((B.labelsMap (SlotMaps.transport T G) (H.map u)).map toLetter)
    ((B.labelsMap (SlotMaps.transport T G) (critical (H.map u).length)).map toLetter)
    (decide ((H.map u).length % 3 ≠ 2))).map toFin =
    (Sparse.FIFO.liftedNode
      (((T.restrictRoots B).labelsMap (G.comp (T.suffixes H he)) u.val).map toLetter)
      (((T.restrictRoots B).labelsMap (G.comp (T.suffixes H he)) (critical u.val.length)).map toLetter)
      (decide (u.val.length % 3 ≠ 2))).map toFin
  rw [hnode,hc,hs]

end SlotTransport
end AllThoseBigRamsey.Pseudotree.CriticalCopies
