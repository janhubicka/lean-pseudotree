import PseudotreeValidation.FIFOBoundary
import PseudotreeValidation.FIFOLifting
import PseudotreeValidation.CriticalPullback

/-! The FIFO formula on a tail of the sparse tree, with arbitrary
synchronized slot maps. No global strong map of the earlier levels
is needed. The boundary condition explicitly retains binary padding
on an incoming binary edge. -/
namespace AllThoseBigRamsey.Pseudotree.CriticalCopies
open RayEmbeddings RayMapModel Sparse.FIFO
open SparseNormalization (Tree critical critical_length tree_prefix)

/-- Label data only on the levels being extended. -/
structure TailLabels (h : Nat) where
  map : Word → Word
  level : Nat → Nat
  strict : ∀ {i j}, h ≤ i → i < j → level i < level j
  length_map : ∀ s, Tree s → h ≤ s.length → (map s).length = level s.length
  ordered : ∀ {s t}, Tree s → Tree t → h ≤ s.length →
    s.length = t.length → s < t → map s < map t
  step : ∀ s a, Tree (s ++ [a]) → h ≤ s.length →
    ∃ p : Word, map (s ++ [a]) = map s ++ a :: p ∧
      (a ≠ 1 → Binary p)

namespace TailLabels

def label (L : TailLabels h) (s : Word) : Sparse.Word := (L.map s).map toLetter

theorem label_length (L : TailLabels h) {s : Word} (hs : Tree s)
    (hj : h ≤ s.length) :
    (L.label s).length = L.level s.length := by
  rw [label,List.length_map,L.length_map s hs hj]

theorem label_lex (L : TailLabels h) {s t : Word} (hs : Tree s) (ht : Tree t)
    (hj : h ≤ s.length) (hlen : s.length = t.length) :
    Sparse.lexLess (L.label s) (L.label t) = decide (s < t) := by
  have hjt : h ≤ t.length := hlen ▸ hj
  unfold label
  rw [SparseNormalization.lexLess_map]
  have he : L.map s < L.map t ↔ s < t := by
    constructor
    · intro hlt
      rcases lt_trichotomy s t with h' | h' | h'
      · exact h'
      · subst t
        exact False.elim (lt_irrefl _ hlt)
      · exact False.elim (lt_asymm hlt (L.ordered ht hs hjt hlen.symm h'))
    · exact L.ordered hs ht hj hlen
  simp only [he]

theorem label_injective_at (L : TailLabels h) {s t : Word}
    (hs : Tree s) (ht : Tree t) (hj : h ≤ s.length) (hlen : s.length = t.length)
    (heq : L.label s = L.label t) : s = t := by
  have hjt : h ≤ t.length := hlen ▸ hj
  have he : L.map s = L.map t := SparseNormalization.map_toLetter_eq.mp heq
  rcases lt_trichotomy s t with hlt | heq' | hgt
  · have h' := L.ordered hs ht hj hlen hlt
    rw [he] at h'
    exact False.elim (lt_irrefl _ h')
  · exact heq'
  · have h' := L.ordered ht hs hjt hlen.symm hgt
    rw [he] at h'
    exact False.elim (lt_irrefl _ h')

/-- This is the same critical-level formula used in the absolute lift. -/
def liftLevel (L : TailLabels h) (j : Nat) : Nat :=
  eventLength (L.label (critical j)) (decide (j % 3 ≠ 2))

def liftWord (L : TailLabels h) (s : Word) : Word :=
  (liftedNode (L.label s) (L.label (critical s.length))
    (decide (s.length % 3 ≠ 2))).map toFin

theorem liftLevel_strict (L : TailLabels h) {i j : Nat}
    (hi : h ≤ i) (hij : i < j) : L.liftLevel i < L.liftLevel j := by
  unfold liftLevel
  apply eventLength_strict_of_depth
  rw [L.label_length (criticalNode i).property (by simpa using hi),
    L.label_length (criticalNode j).property (by have := hi.trans hij.le; simpa using this),
    critical_length,critical_length]
  exact L.strict hi hij

theorem liftWord_length (L : TailLabels h) {s : Word}
    (hs : Tree s) (hj : h ≤ s.length) :
    (L.liftWord s).length = L.liftLevel s.length := by
  unfold liftWord liftLevel
  rw [List.length_map,liftedNode_length]
  rw [L.label_length hs hj,
    L.label_length (criticalNode s.length).property (by simpa using hj),
    critical_length]

theorem liftWord_tree (L : TailLabels h) (s : Word) :
    Tree (L.liftWord s) := by
  change Sparse.InTree ((L.liftWord s).map toLetter)
  simpa [liftWord,List.map_map,Function.comp_def] using
    liftedNode_inTree (L.label s) (L.label (critical s.length)) (decide (s.length % 3 ≠ 2))

theorem liftWord_critical (L : TailLabels h) (j : Nat) :
    L.liftWord (critical j) = critical (L.liftLevel j) := by
  unfold liftWord liftLevel
  rw [critical_length,liftedNode,if_pos rfl,eventNode_critical]
  rfl

theorem liftLevel_phase (L : TailLabels h) (j : Nat) :
    L.liftLevel j % 3 = 2 ↔ j % 3 = 2 := by
  unfold liftLevel
  by_cases hm : j % 3 = 2 <;> simp [hm,eventLength] <;> omega

theorem liftWord_step (L : TailLabels h) (s : Word) (a : Fin 3)
    (hs : Tree (s ++ [a])) (hj : h ≤ s.length) :
    ∃ p : Word, L.liftWord (s ++ [a]) = L.liftWord s ++ a :: p ∧
      (a ≠ 1 → Binary p) := by
  have hs0 := tree_prefix hs (List.prefix_append s [a])
  have hj' : h ≤ (s ++ [a]).length := by simp; omega
  obtain ⟨p,hp,hpb⟩ := L.step s a hs hj
  let x := L.label s
  let t := L.label (critical s.length)
  let y := L.label (s ++ [a])
  let z := L.label (critical (s ++ [a]).length)
  have hcrit : Tree (critical s.length) := (criticalNode s.length).property
  have hcrit' : Tree (critical (s ++ [a]).length) := (criticalNode (s ++ [a]).length).property
  have hx : x.length = t.length := by
    dsimp only [x,t]
    rw [L.label_length hs0 hj,L.label_length hcrit (by simpa using hj),critical_length]
  have hy : y.length = z.length := by
    dsimp only [y,z]
    rw [L.label_length hs hj',L.label_length hcrit' (by simpa using hj'),critical_length]
  have hform : y = x ++ toLetter a :: p.map toLetter := by
    simp only [x,y,label,hp,List.map_append,List.map_cons]
  have hb (ha : toLetter a ≠ .one) : .one ∉ p.map toLetter := by
    have ha' : a ≠ 1 := by simpa using ha
    have hno := (noOne_map p).mpr (hpb ha')
    intro hm
    exact hno .one hm rfl
  have hactive (heq : x = t) :
      if decide (s.length % 3 ≠ 2) then toLetter a ≠ .one else toLetter a = .one := by
    have he := L.label_injective_at hs0 hcrit hj (critical_length _).symm heq
    have hv := FIFOLifting.sparseEvents.active_step s a hs he
    change (if decide (s.length % 3 ≠ 2) then a ≠ 1 else a = 1) at hv
    by_cases hm : s.length % 3 = 2 <;> simpa [hm] using hv
  have hpass (hne : x ≠ t) : toLetter a = passingDigit x t := by
    have hs' : s ≠ critical s.length := fun h => hne (congrArg L.label h)
    have ha := FIFOLifting.sparseEvents.passing_step s a hs hs'
    change a = (if s < critical s.length then 0 else 2) at ha
    have hc : Sparse.lexLess x t = decide (s < critical s.length) :=
      L.label_lex hs0 hcrit hj (critical_length _).symm
    by_cases hl : s < critical s.length <;>
      simp [ha,passingDigit,hc,hl,toLetter]
  obtain ⟨q,hq,hqb⟩ := liftedNode_step hx hy hform hb
    (decide (s.length % 3 ≠ 2)) (decide ((s ++ [a]).length % 3 ≠ 2)) hactive hpass
  refine ⟨q.map toFin,?_,?_⟩
  · simpa only [liftWord,x,t,y,z,List.map_append,List.map_cons,toFin_toLetter] using
      congrArg (List.map toFin) hq
  · intro ha
    apply (binary_map q).mpr
    intro b hb' h
    subst b
    exact hqb (by simpa using ha) hb'

end TailLabels

/-- The label heads at the first new level lie in the required incoming
slots. For a binary incoming edge the head is on that same ray. -/
structure RelativeLabels {h : Nat} (e : FiniteCritical h) extends TailLabels h where
  after : e.level (h-1) < toTailLabels.liftLevel h
  boundary : ∀ s a (hs : Tree (s ++ [a])), (s ++ [a]).length = h →
    ∃ b : Sparse.Word,
      U (toTailLabels.label (s ++ [a])) =
        (e.map (parentNode s a hs)).map toLetter ++ toLetter a :: b ∧
      (a ≠ 1 → .one ∉ b)

namespace RelativeLabels

/-- The sample of the incoming slot can be truncated at the selected
critical level without losing the retained digit. -/
theorem boundary_step {e : FiniteCritical h} (L : RelativeLabels e)
    (s : Word) (a : Fin 3) (hs : Tree (s ++ [a]))
    (hj : (s ++ [a]).length = h) :
    ∃ p : Word, L.toTailLabels.liftWord (s ++ [a]) =
      e.map (parentNode s a hs) ++ a :: p ∧ (a ≠ 1 → Binary p) := by
  let x := L.toTailLabels.label (s ++ [a])
  let t := L.toTailLabels.label (critical (s ++ [a]).length)
  let split : Bool := decide ((s ++ [a]).length % 3 ≠ 2)
  let r := (e.map (parentNode s a hs)).map toLetter
  obtain ⟨b,hb,hbbin⟩ := L.boundary s a hs hj
  obtain ⟨c,hc,hcbin⟩ := H_descendant x (sampleTail x t)
  have hsample : H (x ++ sampleTail x t) = r ++ toLetter a :: (b ++ c) := by
    change U x = r ++ toLetter a :: b at hb
    rw [hc,hb]
    simp only [List.append_assoc,List.cons_append]
  have hpre := liftedNode_prefix_sample x t split
  rw [hsample] at hpre
  have hpLen : r.length = e.level (h-1) := by
    have hh : s.length + 1 = h := by simpa using hj
    have hslt : (parentNode s a hs).val.length < h := by
      change s.length < h
      omega
    dsimp only [r]
    rw [List.length_map,e.length_map _ hslt]
    change e.level s.length = e.level (h-1)
    congr 1
    omega
  have hl : r.length < (liftedNode x t split).length := by
    rw [hpLen]
    have hlen := L.toTailLabels.liftWord_length hs hj.ge
    change ((liftedNode x t split).map toFin).length =
      L.toTailLabels.liftLevel (s ++ [a]).length at hlen
    rw [List.length_map,hj] at hlen
    rw [hlen]
    exact L.after
  obtain ⟨q,hq,hqbin⟩ := trim_edge hpre hl
  refine ⟨q.map toFin,?_,?_⟩
  · simpa [TailLabels.liftWord,x,t,split,r,List.map_map,Function.comp_def] using
      congrArg (List.map toFin) hq
  · intro ha
    apply (binary_map q).mpr
    intro d hd hd1
    subst d
    have hbc : .one ∉ b ++ c := by
      simp only [List.mem_append,not_or]
      exact ⟨hbbin ha,hcbin (sampleTail_binary x t)⟩
    exact hqbin hbc hd

def mapWord {e : FiniteCritical h} (L : RelativeLabels e) (u : Node) : Word :=
  if u.val.length < h then e.map u else L.toTailLabels.liftWord u.val

def levelWord {e : FiniteCritical h} (L : RelativeLabels e) (j : Nat) : Nat :=
  if j < h then e.level j else L.toTailLabels.liftLevel j

theorem mapWord_length {e : FiniteCritical h} (L : RelativeLabels e) (u : Node) :
    (L.mapWord u).length = L.levelWord u.val.length := by
  by_cases hj : u.val.length < h
  · simp only [mapWord,levelWord,if_pos hj]
    exact e.length_map u hj
  · simp only [mapWord,levelWord,if_neg hj]
    exact L.toTailLabels.liftWord_length u.property (by omega)

theorem levelWord_strict {e : FiniteCritical h} (L : RelativeLabels e)
    (hh : 0 < h) : StrictMono L.levelWord := by
  intro i j hij
  by_cases hj : j < h
  · have hi := hij.trans hj
    simp only [levelWord,if_pos hi,if_pos hj]
    exact e.level_strict hij hj
  · by_cases hi : i < h
    · simp only [levelWord,if_pos hi,if_neg hj]
      have hle : e.level i ≤ e.level (h-1) := by
        have hi' : i ≤ h-1 := by omega
        rcases lt_or_eq_of_le hi' with hlt | heq
        · exact (e.level_strict hlt (by omega)).le
        · rw [heq]
      have hafter : L.toTailLabels.liftLevel h ≤ L.toTailLabels.liftLevel j := by
        rcases lt_or_eq_of_le (Nat.le_of_not_gt hj) with hlt | heq
        · exact (L.toTailLabels.liftLevel_strict le_rfl hlt).le
        · rw [heq]
      exact hle.trans_lt (L.after.trans_le hafter)
    · simp only [levelWord,if_neg hi,if_neg hj]
      exact L.toTailLabels.liftLevel_strict (by omega) hij

/-- The relative lift produces a genuine critical self-map extending the
fixed finite map. This lemma only consumes the local slot label data. -/
noncomputable def extendCritical {e : FiniteCritical h} (L : RelativeLabels e)
    (hh : 0 < h) : CriticalMap where
  map := L.mapWord
  level_strict := by
    intro i j hij
    rw [L.mapWord_length,L.mapWord_length,criticalNode_length,criticalNode_length]
    exact L.levelWord_strict hh hij
  length_map := by
    intro u
    rw [L.mapWord_length,L.mapWord_length,criticalNode_length]
  step := by
    intro s a hs
    have hp : (parentNode s a hs).val.length = s.length := rfl
    have hc : (⟨s ++ [a],hs⟩ : Node).val.length = s.length + 1 := by simp
    by_cases hbefore : s.length+1 < h
    · have hpar : s.length < h := by omega
      simpa only [mapWord,hc,hp,if_pos hbefore,if_pos hpar] using
        e.step s a hs (by simpa using hbefore)
    · by_cases htail : h ≤ s.length
      · have hn : ¬s.length < h := by omega
        simpa only [mapWord,hc,hp,if_neg hbefore,if_neg hn,parentNode] using
          L.toTailLabels.liftWord_step s a hs htail
      · have hpar : s.length < h := by omega
        have hj : (s ++ [a]).length = h := by simp; omega
        simpa only [mapWord,hc,hp,if_neg hbefore,if_pos hpar] using
          L.boundary_step s a hs hj
  maps_tree := by
    intro u
    by_cases hj : u.val.length < h
    · simpa only [mapWord,if_pos hj] using e.maps_tree u hj
    · simpa only [mapWord,if_neg hj] using L.toTailLabels.liftWord_tree u.val
  critical_image := by
    intro j
    rw [L.mapWord_length,criticalNode_length]
    by_cases hj : j < h
    · simpa only [mapWord,criticalNode_length,if_pos hj,levelWord] using e.critical_image j hj
    · simpa only [mapWord,criticalNode_length,if_neg hj,levelWord] using
        L.toTailLabels.liftWord_critical j
  phase := by
    intro j
    rw [L.mapWord_length,criticalNode_length]
    by_cases hj : j < h
    · simpa only [levelWord,if_pos hj] using e.phase j hj
    · simpa only [levelWord,if_neg hj] using L.toTailLabels.liftLevel_phase j

theorem extends_prefix {e : FiniteCritical h} (L : RelativeLabels e) (hh : 0 < h) :
    Extends (L.extendCritical hh) e := by
  intro u hu
  change L.mapWord u = e.map u
  simp only [mapWord,if_pos hu]

end RelativeLabels
end AllThoseBigRamsey.Pseudotree.CriticalCopies
