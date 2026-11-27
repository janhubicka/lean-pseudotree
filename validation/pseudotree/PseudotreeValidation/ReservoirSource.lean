import PseudotreeValidation.CriticalCopies
import PseudotreeValidation.SparseLex
import PseudotreeValidation.LowerGeometry

/-! The common source event tree and its ordered frontiers. Independent
of the ambient coordinate chart; used by both absolute recurrence and
relative amalgamation. -/
namespace AllThoseBigRamsey.Pseudotree.Reservoir
open LowerGeometry
open RayEmbeddings RayMapModel
open scoped FirstOrder

abbrev Target := TernaryModel ↪[language] TernaryModel

structure SourceLevel (nodes codes : Set Word) (j : Nat)
    (kind : PaperKind) (critical : Word) : Prop where
  critical_mem : critical ∈ nodes
  critical_length : critical.length = j
  coding : ∀ w ∈ nodes, w.length = j → (w ∈ codes ↔ w = critical ∧ kind.coded = true)
  children : ∀ w ∈ nodes, w.length = j → ∀ a : Fin 3,
    child w a ∈ nodes ↔ localChild critical kind.special w a

/-- Only local rules, with one critical word at each level. There is no
finiteness bound on height and no realization premise. -/
structure Source where
  nodes : Set Word
  codes : Set Word
  root_mem : [] ∈ nodes
  prefix_closed : ∀ w ∈ nodes, ∀ j ≤ w.length, w.take j ∈ nodes
  kind : Nat → PaperKind
  critical : Nat → Word
  rule : ∀ j, SourceLevel nodes codes j (kind j) (critical j)

abbrev Level (D : Source) (j : Nat) :=
  {u : Word // u ∈ D.nodes ∧ u.length = j}

instance (D : Source) (j : Nat) : Finite (Level D j) := by
  let enc (u : Level D j) : List.Vector (Fin 3) j := ⟨u.val, u.property.2⟩
  apply Finite.of_injective enc
  intro u v h
  exact Subtype.ext (congrArg (fun z : List.Vector (Fin 3) j => z.val) h)

noncomputable instance (D : Source) (j : Nat) : Fintype (Level D j) := Fintype.ofFinite _

def criticalAt (D : Source) (j : Nat) : Level D j :=
  ⟨D.critical j, (D.rule j).critical_mem, (D.rule j).critical_length⟩

def childNode {D : Source} {j : Nat} (u : Level D j) (a : Fin 3)
    (ha : child u.val a ∈ D.nodes) : Level D (j+1) :=
  ⟨child u.val a, ha, by simp [child, u.property.2]⟩

variable {D : Source} {j : Nat}

def parent (v : Level D (j + 1)) : Level D j :=
  ⟨v.val.take j,
    D.prefix_closed v.val v.property.1 j (by rw [v.property.2]; omega),
    by simp [v.property.2]⟩

def last (v : Level D (j + 1)) : Fin 3 := v.val[j]'(by rw [v.property.2]; omega)

theorem child_parent (v : Level D (j + 1)) :
    child (parent v).val (last v) = v.val := by
  change v.val.take j ++ [v.val[j]'(by rw [v.property.2]; omega)] = v.val
  rw [List.take_append_getElem]
  exact List.take_of_length_le (by rw [v.property.2])

theorem parent_child_mem (v : Level D (j + 1)) :
    child (parent v).val (last v) ∈ D.nodes := by
  rw [child_parent]
  exact v.property.1

theorem childNode_parent (v : Level D (j + 1)) :
    childNode (parent v) (last v) (parent_child_mem v) = v :=
  Subtype.ext (child_parent v)

@[simp] theorem parent_childNode     (u : Level D j) (a : Fin 3) (ha : child u.val a ∈ D.nodes) :
    parent (childNode u a ha) = u := by
  apply Subtype.ext
  have h := child_parent (childNode u a ha)
  exact List.append_inj_left' h rfl

@[simp] theorem last_childNode     (u : Level D j) (a : Fin 3) (ha : child u.val a ∈ D.nodes) :
    last (childNode u a ha) = a := by
  have h := child_parent (childNode u a ha)
  rw [parent_childNode] at h
  have hsingle := List.append_cancel_left h
  exact List.singleton_inj.mp hsingle

theorem child_lt_same_iff (u : DiaryWord) (a b : Fin 3) :
    child u a < child u b ↔ a < b := by
  induction u with
  | nil => exact List.lex_singleton_iff a b
  | cons c u ih =>
    change List.Lex (· < ·) (c :: child u a) (c :: child u b) ↔ a < b
    rw [List.lex_cons_iff]
    exact ih

/-- Ordered distinct roots keep their order under arbitrary extensions;
children of the same root are ordered by their retained first letters. -/
theorem ordered_children     (roots : Level D j → List TernaryLetter) (k : Nat)
    (hlen : ∀ u, (roots u).length = k)
    (hord : ∀ u v, u.val < v.val → Sparse.lexLess (roots u) (roots v) = true)
    (q : Level D (j + 1) → List TernaryLetter)
    (hp : ∀ u a (ha : child u.val a ∈ D.nodes),
      (roots u ++ [RayMapModel.toLetter a]).IsPrefix (q (childNode u a ha))) :
    ∀ v w, v.val < w.val → Sparse.lexLess (q v) (q w) = true := by
  intro v w hvw
  have hvp := hp (parent v) (last v) (parent_child_mem v)
  have hwp := hp (parent w) (last w) (parent_child_mem w)
  rw [childNode_parent] at hvp hwp
  obtain ⟨sv, hsv⟩ := hvp
  obtain ⟨sw, hsw⟩ := hwp
  have hsource : child (parent v).val (last v) < child (parent w).val (last w) := by
    rw [child_parent, child_parent]
    exact hvw
  rcases lt_trichotomy (parent v).val (parent w).val with hlt | heq | hgt
  · have hr := hord (parent v) (parent w) hlt
    have hne : roots (parent v) ≠ roots (parent w) := by
      intro he
      rw [he, Sparse.lexLess_self] at hr
      contradiction
    rw [← hsv, ← hsw]
    simp only [List.append_assoc, List.singleton_append]
    rw [Sparse.lexLess_append_of_ne ((hlen _).trans (hlen _).symm) hne]
    exact hr
  · have hparents : parent v = parent w := Subtype.ext heq
    rw [hparents] at hsource
    have hletters : last v < last w := (child_lt_same_iff _ _ _).mp hsource
    rw [← hsv, ← hsw, hparents]
    simp only [List.append_assoc, List.singleton_append, Sparse.lexLess_common_prefix,
      Sparse.lexLess, Sparse.rank_toLetter]
    have hval : (last v).val < (last w).val := hletters
    simp [Nat.ne_of_lt hval, hval]
  · have hrev := child_lt_child_of_lt hgt
      ((parent w).property.2.trans (parent v).property.2.symm) (last w) (last v)
    exact False.elim (not_lt_of_gt hsource hrev)


open SparseNormalization (Tree Point critical critical_length point_at_level tree_children)

def sparseSource : Source where
  nodes := {w | Tree w}
  codes := {w | Point w}
  root_mem := by
    change Tree []
    have h := (CriticalCopies.criticalNode 0).property
    have hz : critical 0 = [] := List.length_eq_zero_iff.mp (critical_length 0)
    simpa only [CriticalCopies.criticalNode, hz] using h
  prefix_closed := by
    intro w hw j _
    exact SparseNormalization.tree_prefix hw (List.take_prefix _ _)
  kind := fun j => if j % 3 = 2 then .code else .split
  critical := critical
  rule := by
    intro j
    refine ⟨(CriticalCopies.criticalNode j).property, critical_length j, ?_, ?_⟩
    · intro w hw hlen
      change Point w ↔ w = critical j ∧
        (if j % 3 = 2 then PaperKind.code else PaperKind.split).coded = true
      rw [point_at_level hlen]
      by_cases hm : j % 3 = 2 <;> simp [hm, PaperKind.coded]
    · intro w hw hlen a
      change Tree (child w a) ↔
        localChild (critical j) (if j % 3 = 2 then PaperKind.code else PaperKind.split).special w a
      rw [tree_children j w hw hlen a]
      by_cases hm : j % 3 = 2 <;> by_cases hc : w = critical j <;>
        simp only [localChild, hm, hc, if_true, if_false, PaperKind.special]


end AllThoseBigRamsey.Pseudotree.Reservoir
