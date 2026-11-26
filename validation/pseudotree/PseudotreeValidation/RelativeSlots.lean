import PseudotreeValidation.RelativeFIFO
import PseudotreeValidation.SparseRecurrence

/-! Synchronized relative FIFO lifting above a finite critical prefix.
The frontier is the first level after the prefix. All its target slots
are genuine live queue slots because the top level is a coding level.
The suffix maps can be arbitrary synchronized strong maps; binary
incoming slots require binary roots. -/

namespace AllThoseBigRamsey.Pseudotree.CriticalCopies
open RayEmbeddings RayMapModel Sparse.FIFO
open SparseNormalization (critical critical_length tree_prefix tree_children)
open Reservoir (sparseSource)

/-- Completion as an ordinary strong map preserves the finite domain.
No claim about its values in R outside the domain is made here. -/
theorem finite_completion_exists {h : Nat} (e : FiniteCritical h) (hh : 0 < h) :
    ∃ f : RayStrongMap, ∀ u : Node, u.val.length < h → f.map u.val = e.map u := by
  classical
  let F := fun s : Word => SparseNormalization.Tree s ∧ s.length < h
  let M := fun s : Word => if hs : SparseNormalization.Tree s then e.map ⟨s,hs⟩ else []
  have hroot : SparseNormalization.Tree [] := by
    have hr := (criticalNode 0).property
    have heq : critical 0 = [] := List.length_eq_zero_iff.mp (critical_length 0)
    simpa only [criticalNode,heq] using hr
  have hM (u : Node) : M u.val = e.map u := by simp [M,u.property]
  obtain ⟨f,hf,_⟩ := finite_completion F ⟨[],hroot,hh⟩
    (by
      intro s t hs
      exact ⟨tree_prefix hs.1 (List.prefix_append s t),
        by have := hs.2; simp only [List.length_append] at this; omega⟩)
    h (fun _ hs => hs.2) M e.level
    (fun hij hj => e.level_strict hij hj)
    (by
      intro s hs
      rw [hM (⟨s,hs.1⟩ : Node)]
      exact e.length_map ⟨s,hs.1⟩ hs.2)
    (by
      intro s a hs
      obtain ⟨p,hp,hpb⟩ := e.step s a hs.1 hs.2
      refine ⟨p,?_,hpb⟩
      rw [hM (⟨s ++ [a],hs.1⟩ : Node),
        hM (⟨s,tree_prefix hs.1 (List.prefix_append s [a])⟩ : Node)]
      exact hp)
  exact ⟨f,fun u hu => (hf u.val ⟨u.property,hu⟩).trans (hM u)⟩

theorem finite_lt_iff {h : Nat} (e : FiniteCritical h) (hh : 0 < h)
    (u v : Node) (hu : u.val.length < h) (hv : v.val.length < h) :
    e.map u < e.map v ↔ u.val < v.val := by
  obtain ⟨f,hf⟩ := finite_completion_exists e hh
  rw [← hf u hu,← hf v hv]
  exact (DiaryNormalization.rayMap_strictMono f).lt_iff_lt

theorem finite_inj {h : Nat} (e : FiniteCritical h) (hh : 0 < h)
    (u v : Node) (hu : u.val.length < h) (hv : v.val.length < h)
    (heq : e.map u = e.map v) : u = v := by
  obtain ⟨f,hf⟩ := finite_completion_exists e hh
  apply Subtype.ext
  apply f.injective
  rw [hf u hu,hf v hv,heq]

abbrev Boundary (j : Nat) := Reservoir.Level sparseSource (j+1)

def oldParent {j : Nat} (w : Boundary j) : Node :=
  ⟨(Reservoir.parent w).val,(Reservoir.parent w).property.1⟩

@[simp] theorem oldParent_length {j : Nat} (w : Boundary j) :
    (oldParent w).val.length = j := (Reservoir.parent w).property.2

/-- The image of the parent followed by the retained first digit. -/
def slot {j : Nat} (e : FiniteCritical (j+1)) (w : Boundary j) : Word :=
  e.map (oldParent w) ++ [Reservoir.last w]

theorem slot_length {j : Nat} (e : FiniteCritical (j+1)) (w : Boundary j) :
    (slot e w).length = e.level j + 1 := by
  unfold slot
  rw [List.length_append,List.length_singleton,e.length_map _ (by simp),oldParent_length]
  rfl

theorem slot_tree {j : Nat} (e : FiniteCritical (j+1))
    (hj : j % 3 = 2) (w : Boundary j) : SparseNormalization.Tree (slot e w) := by
  let s := oldParent w
  let a := Reservoir.last w
  let C := criticalNode j
  have hs : s.val.length < j+1 := by simp [s]
  have hC : C.val.length < j+1 := by simp [C]
  have heq : e.map C = critical (e.level j) := e.critical_image j (by omega)
  have hc : e.map s = critical (e.level j) ↔ s.val = critical j := by
    rw [← heq]
    constructor
    · intro h
      exact congrArg Subtype.val (finite_inj e (by omega) s C hs hC h)
    · intro h
      exact congrArg e.map (Subtype.ext h : s = C)
  have hlex : e.map s < critical (e.level j) ↔ s.val < critical j := by
    rw [← heq]
    exact finite_lt_iff e (by omega) s C hs hC
  have hphase : e.level j % 3 = 2 := (e.phase j (by omega)).mpr hj
  have hlen : (e.map s).length = e.level j := by
    rw [e.length_map s hs]
    change e.level s.val.length = e.level j
    rw [show s.val.length = j from oldParent_length w]
  have hsource := (tree_children j s.val s.property (oldParent_length w) a).mp
    (Reservoir.parent_child_mem w)
  change SparseNormalization.Tree (child (e.map s) a)
  rw [tree_children _ _ (e.maps_tree s hs) hlen a]
  simpa only [hc,hlex,hphase,hj,if_true] using hsource

/-- The ordered frontier of target slots is inherited from the finite
strong map. This reuses the exact child ordering lemma for reservoirs. -/
theorem slot_ordered {j : Nat} (e : FiniteCritical (j+1)) (u v : Boundary j)
    (huv : u.val < v.val) : slot e u < slot e v := by
  let roots (w : Reservoir.Level sparseSource j) : Sparse.Word :=
    (e.map ⟨w.val,w.property.1⟩).map toLetter
  have hlen (w : Reservoir.Level sparseSource j) : (roots w).length = e.level j := by
    change ((e.map (⟨w.val,w.property.1⟩ : Node)).map toLetter).length = _
    rw [List.length_map,e.length_map _ (by have := w.property.2; simp; omega)]
    change e.level w.val.length = e.level j
    rw [w.property.2]
  have hord (s t : Reservoir.Level sparseSource j) (h : s.val < t.val) :
      Sparse.lexLess (roots s) (roots t) = true := by
    apply (Sparse.lexLess_fin_iff _ _).mpr
    apply (finite_lt_iff e (by omega) ⟨s.val,s.property.1⟩ ⟨t.val,t.property.1⟩
      (by simp [s.property.2]) (by simp [t.property.2])).mpr
    exact h
  let q (w : Boundary j) := (slot e w).map toLetter
  have hp (w : Reservoir.Level sparseSource j) (a : Fin 3)
      (ha : child w.val a ∈ sparseSource.nodes) :
      (roots w ++ [toLetter a]).IsPrefix (q (Reservoir.childNode w a ha)) := by
    have he : q (Reservoir.childNode w a ha) = roots w ++ [toLetter a] := by
      simp only [q,slot,oldParent,Reservoir.parent_childNode,Reservoir.last_childNode,
        List.map_append,List.map_cons,List.map_nil,roots]
    rw [he]
  exact (Sparse.lexLess_fin_iff (slot e u) (slot e v)).mp
    (Reservoir.ordered_children roots (e.level j) hlen hord q hp u v huv)

/-- Synchronized label roots for the target slots of a finite critical
prefix. The roots are data; the geometry is proved from the FIFO queue. -/
structure SlotFamily {j : Nat} (e : FiniteCritical (j+1)) where
  k : Nat
  root : Boundary j → Word
  length : ∀ w, (root w).length = k
  ordered : ∀ u v, u.val < v.val → root u < root v
  head : ∀ w, ∃ b : Sparse.Word, .one ∉ b ∧
    U ((root w).map toLetter) = (slot e w).map toLetter ++ b

theorem slotFamily_exists {j : Nat} (e : FiniteCritical (j+1))
    (hj : j % 3 = 2) : Nonempty (SlotFamily e) := by
  classical
  let d := (e.level j + 1)/3
  have hphase : e.level j % 3 = 2 := (e.phase j (by omega)).mpr hj
  have hlength : e.level j + 1 = 3*d := by dsimp [d]; omega
  obtain ⟨k,p,hp,hU⟩ := synchronized_slot_labels d
    (fun w : Boundary j => (slot e w).map toLetter)
    (slot_tree e hj)
    (by intro w; rw [List.length_map,slot_length,hlength])
  refine ⟨{
    k := k
    root := fun w => (p w).map toFin
    length := fun w => by simp only [List.length_map,hp]
    ordered := ?_
    head := ?_ }⟩
  · intro u v huv
    have hslots : slot e u < slot e v := slot_ordered e u v huv
    have hne : (slot e u).map toLetter ≠ (slot e v).map toLetter :=
      fun h => (ne_of_lt hslots) (SparseNormalization.map_toLetter_eq.mp h)
    obtain ⟨b,hb,hbu⟩ := hU u
    obtain ⟨c,hc,hcv⟩ := hU v
    have he := slot_label_lex
      (by simp only [List.length_map,slot_length]) hne
      ((hp u).trans (hp v).symm) ⟨b,hbu.symm⟩ ⟨c,hcv.symm⟩
    apply (Sparse.lexLess_iff_fin _ _).mp
    rw [he]
    exact (Sparse.lexLess_fin_iff _ _).mpr hslots
  · intro w
    simpa [List.map_map,Function.comp_def] using hU w

/-- Arbitrary synchronized strong maps in all live slots. A binary
incoming edge cannot have a root containing new 1s. -/
structure SlotMaps (j : Nat) where
  maps : Boundary j → RayStrongMap
  level : Nat → Nat
  strict : StrictMono level
  levels : ∀ w i, (maps w).level i = level i
  binary_root : ∀ w, Reservoir.last w ≠ 1 → Binary ((maps w).map [])

def SlotMaps.identity (j : Nat) : SlotMaps j where
  maps := fun _ => RayStrongMap.identity
  level := id
  strict := fun _ _ h => h
  levels := fun _ _ => rfl
  binary_root := fun _ _ => binary_nil

private theorem append_lt_iff_of_ne {s t : Word}
    (hlen : s.length = t.length) (hne : s ≠ t) (a b : Word) :
    (s ++ a < t ++ b) ↔ s < t := by
  rw [← Sparse.lexLess_fin_iff (s ++ a) (t ++ b),← Sparse.lexLess_fin_iff s t]
  simp only [List.map_append]
  rw [Sparse.lexLess_append_of_ne (by simpa using hlen)
    (fun h => hne (SparseNormalization.map_toLetter_eq.mp h))]

private theorem append_lt_iff_common (p s t : Word) :
    (p ++ s < p ++ t) ↔ s < t := by
  rw [← Sparse.lexLess_fin_iff (p ++ s) (p ++ t),← Sparse.lexLess_fin_iff s t]
  simp only [List.map_append,Sparse.lexLess_common_prefix]

def boundaryOf {j : Nat} (s : Word) (hs : SparseNormalization.Tree s) (hl : j+1 ≤ s.length) : Boundary j :=
  ⟨s.take (j+1),tree_prefix hs (List.take_prefix _ _),by simp [Nat.min_eq_left hl]⟩

theorem boundaryOf_append {j : Nat} (s : Word) (a : Fin 3) (hs : SparseNormalization.Tree (s ++ [a]))
    (hl : j+1 ≤ s.length) :
    boundaryOf (s ++ [a]) hs (by simp; omega) =
      boundaryOf s (tree_prefix hs (List.prefix_append s [a])) hl := by
  apply Subtype.ext
  change (s ++ [a]).take (j+1) = s.take (j+1)
  simp [List.take_append,Nat.sub_eq_zero_of_le hl]

namespace SlotFamily

noncomputable def labelsMap {j : Nat} {e : FiniteCritical (j+1)}
    (B : SlotFamily e) (G : SlotMaps j) (s : Word) : Word := by
  classical
  exact if hs : SparseNormalization.Tree s ∧ j+1 ≤ s.length then
    let w := boundaryOf s hs.1 hs.2
    B.root w ++ (G.maps w).map (s.drop (j+1))
  else []

theorem labelsMap_eq {j : Nat} {e : FiniteCritical (j+1)}
    (B : SlotFamily e) (G : SlotMaps j) {s : Word} (hs : SparseNormalization.Tree s)
    (hl : j+1 ≤ s.length) :
    B.labelsMap G s =
      B.root (boundaryOf s hs hl) ++ (G.maps (boundaryOf s hs hl)).map (s.drop (j+1)) := by
  classical
  simp [labelsMap,hs,hl]

theorem labelsMap_length {j : Nat} {e : FiniteCritical (j+1)}
    (B : SlotFamily e) (G : SlotMaps j) {s : Word} (hs : SparseNormalization.Tree s)
    (hl : j+1 ≤ s.length) :
    (B.labelsMap G s).length = B.k + G.level (s.length-(j+1)) := by
  rw [B.labelsMap_eq G hs hl,List.length_append,B.length,
    (G.maps _).length_map,G.levels,List.length_drop]

theorem labelsMap_ordered {j : Nat} {e : FiniteCritical (j+1)}
    (B : SlotFamily e) (G : SlotMaps j) {s t : Word} (hs : SparseNormalization.Tree s) (ht : SparseNormalization.Tree t)
    (hl : j+1 ≤ s.length) (hlen : s.length = t.length) (hst : s < t) :
    B.labelsMap G s < B.labelsMap G t := by
  have hlt : j+1 ≤ t.length := hlen ▸ hl
  rw [B.labelsMap_eq G hs hl,B.labelsMap_eq G ht hlt]
  let u := boundaryOf s hs hl
  let v := boundaryOf t ht hlt
  change B.root u ++ (G.maps u).map (s.drop (j+1)) <
    B.root v ++ (G.maps v).map (t.drop (j+1))
  have hsrc : u.val ++ s.drop (j+1) < v.val ++ t.drop (j+1) := by
    change s.take (j+1) ++ s.drop (j+1) < t.take (j+1) ++ t.drop (j+1)
    simpa only [List.take_append_drop] using hst
  by_cases heq : u = v
  · rw [heq] at hsrc ⊢
    have hsuf := (append_lt_iff_common v.val _ _).mp hsrc
    exact (append_lt_iff_common (B.root v) _ _).mpr
      ((DiaryNormalization.rayMap_strictMono (G.maps v)) hsuf)
  · have hne : u.val ≠ v.val := fun h => heq (Subtype.ext h)
    have huv := (append_lt_iff_of_ne (u.property.2.trans v.property.2.symm) hne _ _).mp hsrc
    have hroot := B.ordered u v huv
    exact (append_lt_iff_of_ne ((B.length u).trans (B.length v).symm)
      (ne_of_lt hroot) _ _).mpr hroot

theorem labelsMap_step {j : Nat} {e : FiniteCritical (j+1)}
    (B : SlotFamily e) (G : SlotMaps j) (s : Word) (a : Fin 3)
    (hs : SparseNormalization.Tree (s ++ [a])) (hl : j+1 ≤ s.length) :
    ∃ p : Word, B.labelsMap G (s ++ [a]) = B.labelsMap G s ++ a :: p ∧
      (a ≠ 1 → Binary p) := by
  have hs0 := tree_prefix hs (List.prefix_append s [a])
  have hl' : j+1 ≤ (s ++ [a]).length := by simp; omega
  rw [B.labelsMap_eq G hs hl',B.labelsMap_eq G hs0 hl,boundaryOf_append s a hs hl]
  have hdrop : (s ++ [a]).drop (j+1) = s.drop (j+1) ++ [a] := by
    simp [List.drop_append,Nat.sub_eq_zero_of_le hl]
  rw [hdrop]
  obtain ⟨p,hp,hpb⟩ := (G.maps (boundaryOf s hs0 hl)).step (s.drop (j+1)) a
  exact ⟨p,by rw [hp,List.append_assoc],hpb⟩

noncomputable def tailLabels {j : Nat} {e : FiniteCritical (j+1)}
    (B : SlotFamily e) (G : SlotMaps j) : TailLabels (j+1) where
  map := B.labelsMap G
  level := fun i => B.k + G.level (i-(j+1))
  strict := by
    intro i l hi hil
    exact Nat.add_lt_add_left (G.strict (by omega)) _
  length_map := fun _ hs hl => B.labelsMap_length G hs hl
  ordered := fun hs ht hl heq hlt => B.labelsMap_ordered G hs ht hl heq hlt
  step := B.labelsMap_step G

theorem labelsMap_on_boundary {j : Nat} {e : FiniteCritical (j+1)}
    (B : SlotFamily e) (G : SlotMaps j) (w : Boundary j) :
    B.labelsMap G w.val = B.root w ++ (G.maps w).map [] := by
  rw [B.labelsMap_eq G w.property.1 w.property.2.ge]
  have heq : boundaryOf w.val w.property.1 w.property.2.ge = w := by
    apply Subtype.ext
    change w.val.take (j+1) = w.val
    exact List.take_of_length_le w.property.2.le
  rw [heq,List.drop_of_length_le w.property.2.le]

theorem head_on_boundary {j : Nat} {e : FiniteCritical (j+1)}
    (B : SlotFamily e) (G : SlotMaps j) (w : Boundary j) :
    ∃ b : Sparse.Word,
      U ((B.labelsMap G w.val).map toLetter) = (slot e w).map toLetter ++ b ∧
      (Reservoir.last w ≠ 1 → .one ∉ b) := by
  obtain ⟨b,hb,hU⟩ := B.head w
  rw [B.labelsMap_on_boundary G w,List.map_append]
  obtain ⟨p,hp,hpb⟩ := U_slot_descendant hU hb (((G.maps w).map []).map toLetter)
  refine ⟨p,hp,?_⟩
  intro hlast
  apply hpb
  have hno := (noOne_map _).mpr (G.binary_root w hlast)
  intro hmem
  exact hno .one hmem rfl

/-- The head condition supplies both the incoming edge and the strict
gap after the fixed prefix. No reservoir or extension hypothesis is
used in this relative FIFO construction. -/
noncomputable def relativeLabels {j : Nat} {e : FiniteCritical (j+1)}
    (B : SlotFamily e) (G : SlotMaps j) : RelativeLabels e where
  toTailLabels := B.tailLabels G
  after := by
    let w : Boundary j :=
      ⟨critical (j+1),(criticalNode (j+1)).property,critical_length _⟩
    obtain ⟨b,hb,_⟩ := B.head_on_boundary G w
    have hl := congrArg List.length hb
    simp only [U_length,List.length_append,List.length_map,slot_length] at hl
    change e.level ((j+1)-1) <
      eventLength ((B.labelsMap G (critical (j+1))).map toLetter)
        (decide ((j+1)%3 ≠ 2))
    change 3 * labelStage ((B.labelsMap G (critical (j+1))).map toLetter) =
      e.level j + 1 + b.length at hl
    rw [show j+1-1 = j by omega]
    unfold eventLength
    split <;> omega
  boundary := by
    intro s a hs hj
    have hlen : s.length = j := by simp at hj; omega
    let u : Reservoir.Level sparseSource j :=
      ⟨s,tree_prefix hs (List.prefix_append s [a]),hlen⟩
    let w := Reservoir.childNode u a hs
    obtain ⟨b,hb,hbbin⟩ := B.head_on_boundary G w
    have hpar : Reservoir.parent w = u := Reservoir.parent_childNode u a hs
    have hlast : Reservoir.last w = a := Reservoir.last_childNode u a hs
    have hslot : slot e w = e.map (parentNode s a hs) ++ [a] := by
      have he : oldParent w = parentNode s a hs := by
        apply Subtype.ext
        exact congrArg (fun v : Reservoir.Level sparseSource j => v.val) hpar
      rw [slot,he,hlast]
    rw [hslot,List.map_append,List.map_cons,List.map_nil] at hb
    refine ⟨b,?_,?_⟩
    · change U ((B.labelsMap G (s ++ [a])).map toLetter) =
        (e.map (parentNode s a hs)).map toLetter ++ toLetter a :: b
      change U ((B.labelsMap G (s ++ [a])).map toLetter) =
        (e.map (parentNode s a hs)).map toLetter ++ [toLetter a] ++ b at hb
      simpa only [List.append_assoc,List.singleton_append] using hb
    · intro ha
      apply hbbin
      rwa [hlast]

/-- Relative lifting at a fixed whole-block boundary, with any
synchronized family of maps satisfying the incoming root condition. -/
theorem relative_lift {j : Nat} {e : FiniteCritical (j+1)}
    (B : SlotFamily e) (G : SlotMaps j) :
    ∃ X : CriticalMap, Extends X e ∧
      ∀ u : Node, j+1 ≤ u.val.length →
        X.map u = (B.tailLabels G).liftWord u.val := by
  let L := B.relativeLabels G
  refine ⟨L.extendCritical (by omega), L.extends_prefix (by omega),?_⟩
  intro u hu
  change L.mapWord u = _
  simp only [RelativeLabels.mapWord,if_neg (Nat.not_lt_of_ge hu), L,
    relativeLabels]

end SlotFamily

/-- Every finite critical embedding at a whole-block boundary extends
to an actual infinite critical embedding. The empty case is immediate;
otherwise take identity suffix maps in the synchronized label cones. -/
theorem wholeBlockExtension : WholeBlockExtension := by
  intro n
  cases n with
  | zero =>
    intro e
    refine ⟨identity,?_⟩
    intro u hu
    omega
  | succ n =>
    rw [show 3 * (n+1) = (3*n+2)+1 by omega]
    intro e
    obtain ⟨B⟩ := slotFamily_exists e (by omega)
    obtain ⟨X,hX,_⟩ := B.relative_lift (SlotMaps.identity (3*n+2))
    exact ⟨X,hX⟩

/-- The actual A.3(1) field, with no remaining finite-extension premise. -/
theorem amalgamation_nonempty {n d : Nat} (a : system.Approx n) (Y : CriticalMap)
    (hd : finitization.HasDepth a Y d)
    {Z : CriticalMap} (hZ : Z ∈ system.levelNeighborhood d Y) :
    (system.neighborhood a Z).Nonempty :=
  amalgamation_nonempty_of_extension wholeBlockExtension a Y hd hZ

end AllThoseBigRamsey.Pseudotree.CriticalCopies
