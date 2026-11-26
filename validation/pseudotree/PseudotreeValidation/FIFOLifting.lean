import PseudotreeValidation.FIFOEdges
import PseudotreeValidation.GeneralizedDiaryGrammar
import PseudotreeValidation.CriticalCopies

/-! The absolute FIFO lift, for the actual finite generalized diaries and
for the entire sparse tree R. A local event tree is just the child-rule
data used in the manuscript, with dummy critical words beyond its height.
The map is the literal serialization formula, not a chosen embedding. -/

namespace AllThoseBigRamsey.Pseudotree.FIFOLifting
open RayEmbeddings RayMapModel
open Sparse.FIFO
open SparseNormalization (Tree Point critical critical_length tree_children)

structure EventTree where
  nodes : Word → Prop
  root_mem : nodes []
  prefix_closed : ∀ s t, nodes (s ++ t) → nodes s
  criticalWord : Nat → Word
  critical_length : ∀ j, (criticalWord j).length = j
  critical_mem : ∀ s, nodes s → nodes (criticalWord s.length)
  split : Nat → Bool
  active_step : ∀ s a, nodes (s ++ [a]) → s = criticalWord s.length →
    if split s.length then a ≠ 1 else a = 1
  passing_step : ∀ s a, nodes (s ++ [a]) → s ≠ criticalWord s.length →
    a = if s < criticalWord s.length then 0 else 2

def label (f : RayStrongMap) (w : Word) : Sparse.Word := (f.map w).map toLetter

@[simp] theorem label_length (f : RayStrongMap) (w : Word) :
    (label f w).length = f.level w.length := by simp [label, f.length_map]

theorem label_injective (f : RayStrongMap) : Function.Injective (label f) := by
  intro s t h
  apply f.injective
  exact SparseNormalization.map_toLetter_eq.mp h

theorem label_lex (f : RayStrongMap) (s t : Word) :
    Sparse.lexLess (label f s) (label f t) = decide (s < t) := by
  unfold label
  rw [SparseNormalization.lexLess_map]
  simp only [(DiaryNormalization.rayMap_strictMono f).lt_iff_lt]

def HFin (w : Word) : Word := (H (w.map toLetter)).map toFin

theorem HFin_point (w : Word) : Point (HFin w) := by
  change Sparse.InSparse ((HFin w).map toLetter)
  simpa [HFin, List.map_map, Function.comp_def] using H_inSparse (w.map toLetter)

def liftLevel (F : EventTree) (f : RayStrongMap) (j : Nat) : Nat :=
  eventLength (label f (F.criticalWord j)) (F.split j)

def liftWord (F : EventTree) (f : RayStrongMap) (s : Word) : Word :=
  (liftedNode (label f s) (label f (F.criticalWord s.length)) (F.split s.length)).map toFin

theorem liftLevel_strict (F : EventTree) (f : RayStrongMap) : StrictMono (liftLevel F f) := by
  intro i j h
  apply eventLength_strict_of_depth
  simp only [label_length, F.critical_length]
  exact f.level_strict h

theorem liftWord_length (F : EventTree) (f : RayStrongMap) (s : Word) :
    (liftWord F f s).length = liftLevel F f s.length := by
  unfold liftWord liftLevel
  rw [List.length_map, liftedNode_length]
  simp only [label_length, F.critical_length]

theorem liftWord_tree (F : EventTree) (f : RayStrongMap) (s : Word) :
    Tree (liftWord F f s) := by
  change Sparse.InTree ((liftWord F f s).map toLetter)
  simpa [liftWord, List.map_map, Function.comp_def] using
    liftedNode_inTree (label f s) (label f (F.criticalWord s.length)) (F.split s.length)

theorem liftWord_critical (F : EventTree) (f : RayStrongMap) (j : Nat) :
    liftWord F f (F.criticalWord j) = critical (liftLevel F f j) := by
  unfold liftWord liftLevel
  rw [F.critical_length, liftedNode, if_pos rfl, eventNode_critical]
  rfl

theorem liftWord_code (F : EventTree) (f : RayStrongMap) {s : Word}
    (hs : s = F.criticalWord s.length) (hn : F.split s.length = false) :
    liftWord F f s = HFin (f.map s) := by
  simp [liftWord, ← hs, liftedNode, hn, eventNode, label, HFin]

theorem liftWord_step (F : EventTree) (f : RayStrongMap) (s : Word) (a : Fin 3)
    (hs : F.nodes (s ++ [a])) :
    ∃ p : Word, liftWord F f (s ++ [a]) = liftWord F f s ++ a :: p ∧
      (a ≠ 1 → Binary p) := by
  obtain ⟨p, hp, hpb⟩ := f.step s a
  let x := label f s
  let t := label f (F.criticalWord s.length)
  let y := label f (s ++ [a])
  let z := label f (F.criticalWord (s ++ [a]).length)
  have hx : x.length = t.length := by simp [x,t,F.critical_length]
  have hy : y.length = z.length := by simp [y,z,F.critical_length]
  have hform : y = x ++ toLetter a :: p.map toLetter := by
    simp only [y,x,label,hp,List.map_append,List.map_cons]
  have hb (ha : toLetter a ≠ .one) : .one ∉ p.map toLetter := by
    have ha' : a ≠ 1 := by simpa using ha
    have hno := (noOne_map p).mpr (hpb ha')
    intro hm
    exact hno .one hm rfl
  have hactive (heq : x = t) :
      if F.split s.length then toLetter a ≠ .one else toLetter a = .one := by
    have h := F.active_step s a hs (label_injective f heq)
    cases hsplit : F.split s.length <;> simpa [hsplit] using h
  have hpass (hne : x ≠ t) : toLetter a = passingDigit x t := by
    have hs' : s ≠ F.criticalWord s.length := fun h => hne (congrArg (label f) h)
    have ha := F.passing_step s a hs hs'
    have hc : Sparse.lexLess x t = decide (s < F.criticalWord s.length) := label_lex f _ _
    by_cases hl : s < F.criticalWord s.length <;>
      simp [ha, passingDigit, hc, hl, toLetter]
  obtain ⟨q, hq, hqb⟩ := liftedNode_step hx hy hform hb
    (F.split s.length) (F.split (s ++ [a]).length) hactive hpass
  refine ⟨q.map toFin, ?_, ?_⟩
  · simpa only [liftWord, x, t, y, z, List.map_append, List.map_cons,
      toFin_toLetter] using congrArg (List.map toFin) hq
  · intro ha
    apply (binary_map q).mpr
    intro b hb' h
    subst b
    exact hqb (by simpa using ha) hb'

/-- The exact map on the actual source domain. Completion only supplies
irrelevant values off that domain. -/
noncomputable def liftPartial (F : EventTree) (f : RayStrongMap) : PrefixRayMap F.nodes where
  root_mem := F.root_mem
  prefix_closed := F.prefix_closed
  map := liftWord F f
  level := liftLevel F f
  level_strict := fun h => liftLevel_strict F f h
  length_map := fun s _ => liftWord_length F f s
  step := liftWord_step F f

noncomputable def liftTotal (F : EventTree) (f : RayStrongMap) : RayStrongMap :=
  (liftPartial F f).completion

theorem liftTotal_agrees (F : EventTree) (f : RayStrongMap) (s : Word) (hs : F.nodes s) :
    (liftTotal F f).map s = liftWord F f s :=
  PrefixRayMap.completion_agrees (liftPartial F f) s hs

/-! Instantiate the local event-tree interface for literal generalized
diaries, without requiring an indexed event grammar or finite height
bound in terms of the number of coding nodes. -/

noncomputable def diaryHeight (D : GeneralizedDiary n) : Nat := D.axioms.choose

theorem diaryHeight_spec (D : GeneralizedDiary n) :
    GeneralizedTreeAxioms D.nodes D.codes (diaryHeight D) := D.axioms.choose_spec

noncomputable def diaryEvent (D : GeneralizedDiary n) (j : Nat) : PaperKind × Word :=
  if hj : j < diaryHeight D then
    let h := (diaryHeight_spec D).level j hj
    (h.choose, h.choose_spec.choose)
  else (.leaf, List.replicate j 0)

theorem diaryEvent_spec (D : GeneralizedDiary n) {j : Nat} (hj : j < diaryHeight D) :
    GeneralizedLevel D.nodes D.codes j (diaryEvent D j).1 (diaryEvent D j).2 := by
  unfold diaryEvent
  rw [dif_pos hj]
  exact ((diaryHeight_spec D).level j hj).choose_spec.choose_spec

theorem diaryEvent_length (D : GeneralizedDiary n) (j : Nat) :
    (diaryEvent D j).2.length = j := by
  by_cases hj : j < diaryHeight D
  · exact (diaryEvent_spec D hj).critical_length
  · simp [diaryEvent, hj]

noncomputable def diaryEvents (D : GeneralizedDiary n) : EventTree where
  nodes := fun s => s ∈ D.nodes
  root_mem := D.shape.root_mem
  prefix_closed := D.shape.prefix_closed
  criticalWord := fun j => (diaryEvent D j).2
  critical_length := diaryEvent_length D
  critical_mem := by
    intro s hs
    exact (diaryEvent_spec D ((diaryHeight_spec D).bounded s hs)).critical_mem
  split := fun j => decide ((diaryEvent D j).1 = .split)
  active_step := by
    intro s a hs heq
    have hnode := D.shape.prefix_closed s [a] hs
    have P := diaryEvent_spec D ((diaryHeight_spec D).bounded s hnode)
    have h := (P.children s hnode rfl a).mp hs
    change s = (diaryEvent D s.length).2 at heq
    simp only [localChild, heq, if_pos rfl] at h
    cases hk : (diaryEvent D s.length).1 <;> simp_all [PaperKind.special]
  passing_step := by
    intro s a hs heq
    have hnode := D.shape.prefix_closed s [a] hs
    have P := diaryEvent_spec D ((diaryHeight_spec D).bounded s hnode)
    have h := (P.children s hnode rfl a).mp hs
    change s ≠ (diaryEvent D s.length).2 at heq
    by_cases hl : s < (diaryEvent D s.length).2 <;>
      simpa [localChild, heq, hl] using h

theorem diary_code_is_critical (D : GeneralizedDiary n) {s : Word} (hs : s ∈ D.codes) :
    s = (diaryEvents D).criticalWord s.length ∧ (diaryEvents D).split s.length = false := by
  have hnode := D.code_node hs
  have P := diaryEvent_spec D ((diaryHeight_spec D).bounded s hnode)
  obtain ⟨heq, hk⟩ := (P.coding s hnode rfl).mp hs
  refine ⟨heq, ?_⟩
  change decide ((diaryEvent D s.length).1 = .split) = false
  cases h : (diaryEvent D s.length).1 <;> simp_all [PaperKind.coded]

/-- Absolute FIFO lift for a literal generalized diary: its image is
in R and each coding word is mapped to H of the original embedded word. -/
theorem diary_lift (D : GeneralizedDiary n) (f : RayStrongMap) :
    ∃ g : RayStrongMap, (∀ s ∈ D.nodes, Tree (g.map s)) ∧
      ∀ s ∈ D.codes, g.map s = HFin (f.map s) := by
  refine ⟨liftTotal (diaryEvents D) f, ?_, ?_⟩
  · intro s hs
    rw [liftTotal_agrees _ _ s hs]
    exact liftWord_tree _ _ _
  · intro s hs
    rw [liftTotal_agrees _ _ s (D.code_node hs)]
    obtain ⟨h, hn⟩ := diary_code_is_critical D hs
    exact liftWord_code _ _ h hn

/-! The infinite instance gives actual critical self-maps, rather than
only a family of finite realizations. -/
def sparseEvents : EventTree where
  nodes := Tree
  root_mem := by
    have h := (CriticalCopies.criticalNode 0).property
    have hz : critical 0 = [] := List.length_eq_zero_iff.mp (critical_length 0)
    simpa [CriticalCopies.criticalNode,hz] using h
  prefix_closed := fun s t h => SparseNormalization.tree_prefix h (List.prefix_append s t)
  criticalWord := critical
  critical_length := critical_length
  critical_mem := fun s _ => (CriticalCopies.criticalNode s.length).property
  split := fun j => decide (j % 3 ≠ 2)
  active_step := by
    intro s a hs heq
    have hnode := SparseNormalization.tree_prefix hs (List.prefix_append s [a])
    have h := (tree_children s.length s hnode rfl a).mp hs
    change s = critical s.length at heq
    by_cases hm : s.length % 3 = 2
    · simpa [heq, hm] using h
    · have ha : a = 0 ∨ a = 2 := by simpa [heq, hm] using h
      simp only [hm, ne_eq, not_false_eq_true, decide_true, if_true]
      rcases ha with rfl | rfl <;> decide
  passing_step := by
    intro s a hs heq
    have hnode := SparseNormalization.tree_prefix hs (List.prefix_append s [a])
    have h := (tree_children s.length s hnode rfl a).mp hs
    change s ≠ critical s.length at heq
    by_cases hl : s < critical s.length <;> simpa [heq,hl] using h

noncomputable def liftCritical (f : RayStrongMap) : CriticalCopies.CriticalMap where
  map := fun s => liftWord sparseEvents f s.val
  level_strict := by
    intro i j h
    change (liftWord sparseEvents f (critical i)).length <
      (liftWord sparseEvents f (critical j)).length
    rw [liftWord_length, liftWord_length, critical_length, critical_length]
    exact liftLevel_strict _ _ h
  length_map := by
    intro s
    change (liftWord sparseEvents f s.val).length =
      (liftWord sparseEvents f (critical s.val.length)).length
    rw [liftWord_length, liftWord_length, critical_length]
  step := fun s a hs => liftWord_step sparseEvents f s a hs
  maps_tree := fun _ => liftWord_tree _ _ _
  critical_image := by
    intro j
    change liftWord sparseEvents f (critical j) =
      critical (liftWord sparseEvents f (critical j)).length
    rw [liftWord_length, critical_length]
    exact liftWord_critical sparseEvents f j
  phase := by
    intro j
    change (liftWord sparseEvents f (critical j)).length % 3 = 2 ↔ j % 3 = 2
    rw [liftWord_length, critical_length]
    change eventLength (label f (critical j)) (decide (j % 3 ≠ 2)) % 3 = 2 ↔ _
    by_cases hm : j % 3 = 2 <;> simp [hm,eventLength] <;> omega

theorem liftCritical_code (f : RayStrongMap) (s : CriticalCopies.Node) (hs : Point s.val) :
    (liftCritical f).map s = HFin (f.map s.val) := by
  obtain ⟨hm, heq⟩ := (SparseNormalization.point_at_level rfl).mp hs
  apply liftWord_code sparseEvents f
  · exact heq
  · change decide (s.val.length % 3 ≠ 2) = false
    simp [hm]

end AllThoseBigRamsey.Pseudotree.FIFOLifting
