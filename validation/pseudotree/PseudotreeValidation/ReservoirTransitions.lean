import PseudotreeValidation.LowerTransition
import PseudotreeValidation.CriticalCopies

/-!
# Rational reservoir transitions for unbounded event trees

The earlier checked split, opposite-cone, and common-prefix lemmas are
used unchanged. The frontier bookkeeping is generalized to unbounded
event trees, with a possibly different prescribed structural copy for
each vertex. On a transition the prescribed copy agrees across each
source edge. This permits relative uses with distinct boundary targets.
-/

namespace AllThoseBigRamsey.Pseudotree.Reservoir
open LowerGeometry
open LowerRealization (ray_prefix_binary binary_prefix_between
  inTree_of_sparse fork_critical finite_common_prefix)
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

/-- Every prescribed copy is a self-copy of the reduct, contained in the
actual sparse code set. -/
def SparseTargets (f : Word → Target) : Prop :=
  ∀ u x, x ∈ Set.range (f u) → Sparse.InSparse (fromBlocks x)

/-- Each frontier vertex may have its own target. -/
structure Layer (D : Source)
    (f : Word → Target) (j : Nat) where
  bound : Nat
  copies : Level D j → RayCopy
  prefixes : Level D j → List TernaryLetter
  prefix_length : ∀ u, (prefixes u).length = bound
  common_prefix : ∀ u q, prefixes u <+: fromBlocks (copies u q)
  root_short : ∀ u, (rayRoot (copies u).stem).length < bound
  inside : ∀ u, Set.range (copies u).embedding ⊆ Set.range (f u.val)
  ordered : ∀ u v, u.val < v.val → Sparse.lexLess (prefixes u) (prefixes v) = true

/-- A genuine one-level transition. The old level is realized at `level`,
then each new candidate cylinder starts after the prescribed first letter.
Only these local equations are needed by the finite-map assembly. -/
structure Step {D : Source} {f : Word → Target}
    {j : Nat} (P : Layer D f j) where
  next : Layer D f (j + 1)
  level : Nat
  lower : P.bound ≤ level
  upper : level < next.bound
  roots : Level D j → List TernaryLetter
  root_length : ∀ u, (roots u).length = level
  root_binary : ∀ u, ∃ b : List TernaryLetter,
    .one ∉ b ∧ roots u = P.prefixes u ++ b
  coding : ∀ u, u.val ∈ D.codes → toBlocks (roots u) ∈ Set.range (f u.val)
  root_tree : ∀ u, Sparse.InTree (roots u)
  critical : roots (criticalAt D j) = Sparse.critical level
  phase : level % 3 = 2 ↔ D.kind j ≠ .split
  edge : ∀ u a (ha : child u.val a ∈ D.nodes),
    ∃ b : List TernaryLetter,
      next.prefixes (childNode u a ha) = roots u ++ RayMapModel.toLetter a :: b ∧
      (a ≠ 1 → .one ∉ b)

/-- The root candidate layer is obtained inside an actual source interval and
then refined past its ray root. -/
theorem initial (D : Source) (f : Word → Target) :
    Nonempty (Layer D f 0) := by
  let y : TernaryModel := .point ⟨[]⟩
  obtain ⟨w, hyw⟩ := exists_gt y
  obtain ⟨Q, hQ⟩ := interval_rayCopy (embeddingOrderEmbedding (f [])) hyw
  obtain ⟨R, hstem, hsub, p, hplen, hp⟩ := Q.common_prefix
    ((rayRoot Q.stem).length + 1) (by omega)
  refine ⟨{
    bound := (rayRoot Q.stem).length + 1
    copies := fun _ => R
    prefixes := fun _ => p
    prefix_length := fun _ => hplen
    common_prefix := fun _ => hp
    root_short := fun _ => by rw [hstem]; omega
    inside := ?_
    ordered := ?_
  }⟩
  · intro u x hx
    have hu : u.val = [] := List.length_eq_zero_iff.mp u.property.2
    rw [hu]
    obtain ⟨q, hq⟩ := hsub hx
    obtain ⟨z, _, _, hz⟩ := hQ q
    exact ⟨z, (hz.symm.trans hq)⟩
  · intro u v huv
    have hu : u.val = [] := List.length_eq_zero_iff.mp u.property.2
    have hv : v.val = [] := List.length_eq_zero_iff.mp v.property.2
    rw [hu, hv] at huv
    exact False.elim ((lt_irrefl _) huv)

/-- The geometric data for the selected critical node at one source level. -/
structure CriticalChoice {D : Source} {f : Word → Target}
    {j : Nat} (P : Layer D f j) (kind : PaperKind) (c : Level D j) where
  word : List TernaryLetter
  binary : ∃ b : List TernaryLetter, .one ∉ b ∧ word = P.prefixes c ++ b
  critical : word = Sparse.critical word.length
  phase : word.length % 3 = 2 ↔ kind ≠ .split
  coding : kind.coded = true → toBlocks word ∈ Set.range (f c.val)
  children : ∀ a : Fin 3, kind.special a → ∃ R : RayCopy,
    Set.range R.embedding ⊆ Set.range (f c.val) ∧ ∀ q, ∃ b : List TernaryLetter,
      fromBlocks (R q) = word ++ RayMapModel.toLetter a :: b ∧ (a ≠ 1 → .one ∉ b)

/-- All four critical events are produced inside the actual self-copy by the
proved split and opposite-cone constructions. -/
theorem critical_choice {D : Source} {f : Word → Target}
    {j : Nat} (P : Layer D f j)
    (hsparse : SparseTargets f)
    (kind : PaperKind) (c : Level D j) : Nonempty (CriticalChoice P kind c) := by
  classical
  have hsQ : ∀ q, Sparse.InSparse (fromBlocks (P.copies c q)) :=
    fun q => hsparse c.val _ (P.inside c ⟨q, rfl⟩)
  have choosePoint : ∃ v : List TernaryLetter,
      (∃ b : List TernaryLetter, .one ∉ b ∧ v = P.prefixes c ++ b) ∧
      v = Sparse.critical v.length ∧ v.length % 3 = 2 ∧ toBlocks v ∈ Set.range (f c.val) ∧
      v = fromBlocks (P.copies c 0) := by
    let v := fromBlocks (P.copies c 0)
    refine ⟨v, ray_prefix_binary (P.copies c) (P.prefixes c) 0
      (by rw [P.prefix_length]; exact (P.root_short c).le) (P.common_prefix c 0), ?_, ?_, ?_, rfl⟩
    · exact ((Sparse.inSparse_at_level v.length v rfl).mp (hsQ 0)).2
    · exact ((Sparse.inSparse_at_level v.length v rfl).mp (hsQ 0)).1
    · simpa only [v, toBlocks_fromBlocks] using P.inside c ⟨0, rfl⟩
  cases kind with
  | split =>
      obtain ⟨v, Q0, Q2, hpv, h0stem, h2stem, h0range, h2range, h0, h2⟩ :=
        (P.copies c).sparse_split hsQ (P.prefixes c) (P.common_prefix c)
          (by rw [P.prefix_length]; exact (P.root_short c).le)
      have h0S : Set.range Q0.embedding ⊆ Set.range (f c.val) := h0range.trans (P.inside c)
      have h2S : Set.range Q2.embedding ⊆ Set.range (f c.val) := h2range.trans (P.inside c)
      obtain ⟨b0, hb0, he0⟩ := h0 0
      obtain ⟨b2, hb2, he2⟩ := h2 0
      have hv0 : v ++ [.zero] <+: fromBlocks (Q0 0) := ⟨b0, by simpa using he0.symm⟩
      have hv2 : v ++ [.two] <+: fromBlocks (Q2 0) := ⟨b2, by simpa using he2.symm⟩
      have hcrit := fork_critical
        (Sparse.inTree_prefix (inTree_of_sparse (hsparse c.val _ (h0S ⟨0, rfl⟩))) hv0)
        (Sparse.inTree_prefix (inTree_of_sparse (hsparse c.val _ (h2S ⟨0, rfl⟩))) hv2)
      have hv0tree := Sparse.inTree_prefix
        (inTree_of_sparse (hsparse c.val _ (h0S ⟨0, rfl⟩))) hv0
      have hphase : v.length % 3 ≠ 2 := by
        intro hm
        have hvTree := Sparse.inTree_prefix hv0tree (List.prefix_append _ _)
        have hh := (Sparse.critical_children v.length v hvTree rfl .zero).mp hv0tree
        simp only [Sparse.CriticalChildren, if_pos hcrit, hm, decide_true, if_true] at hh
        contradiction
      obtain ⟨q, hq⟩ := h0range ⟨0, rfl⟩
      have hvQ : v <+: fromBlocks (P.copies c q) := by
        rw [hq]
        exact (List.prefix_append v [.zero]).trans hv0
      refine ⟨{
        word := v
        binary := binary_prefix_between hpv hvQ
          (ray_prefix_binary (P.copies c) (P.prefixes c) q
            (by rw [P.prefix_length]; exact (P.root_short c).le) (P.common_prefix c q))
        critical := hcrit
        phase := by simp [hphase]
        coding := by simp [PaperKind.coded]
        children := ?_
      }⟩
      intro a ha
      rcases ha with rfl | rfl
      · exact ⟨Q0, h0S, fun q => by
          obtain ⟨b, hb, he⟩ := h0 q
          exact ⟨b, he, fun _ => hb⟩⟩
      · exact ⟨Q2, h2S, fun q => by
          obtain ⟨b, hb, he⟩ := h2 q
          exact ⟨b, he, fun _ => hb⟩⟩
  | leaf =>
      obtain ⟨v, hv, hcrit, hphase, hmem, _⟩ := choosePoint
      exact ⟨⟨v, hv, hcrit, by simp [hphase], fun _ => hmem, fun _ h => False.elim h⟩⟩
  | code =>
      obtain ⟨v, hv, hcrit, hphase, hmem, heq⟩ := choosePoint
      obtain ⟨R, hR, hturn⟩ := (P.copies c).opposite_continuation (f c.val) (P.inside c) 0
      refine ⟨⟨v, hv, hcrit, by simp [hphase], fun _ => hmem, ?_⟩⟩
      intro a ha
      have ha' : a = 1 := ha
      subst a
      refine ⟨R, hR, fun q => ?_⟩
      obtain ⟨b, hb⟩ := (hturn q).2
      refine ⟨b, ?_, by simp⟩
      change fromBlocks (R q) = v ++ .one :: b
      rw [heq]
      simpa only [List.append_assoc, List.singleton_append] using hb.symm
  | turn =>
      obtain ⟨v, hv, hcrit, hphase, _, heq⟩ := choosePoint
      obtain ⟨R, hR, hturn⟩ := (P.copies c).opposite_continuation (f c.val) (P.inside c) 0
      refine ⟨⟨v, hv, hcrit, by simp [hphase], by simp [PaperKind.coded], ?_⟩⟩
      intro a ha
      have ha' : a = 1 := ha
      subst a
      refine ⟨R, hR, fun q => ?_⟩
      obtain ⟨b, hb⟩ := (hturn q).2
      refine ⟨b, ?_, by simp⟩
      change fromBlocks (R q) = v ++ .one :: b
      rw [heq]
      simpa only [List.append_assoc, List.singleton_append] using hb.symm

/-- Refine each old branch to a prefix just beyond the chosen critical level.
This makes the noncritical letter at that level visible. -/
structure OldRefinement {D : Source} {f : Word → Target}
    {j : Nat} (P : Layer D f j) (k : Nat) where
  copies : Level D j → RayCopy
  prefixes : Level D j → List TernaryLetter
  same_stem : ∀ u, (copies u).stem = (P.copies u).stem
  inside : ∀ u, Set.range (copies u).embedding ⊆ Set.range (P.copies u).embedding
  length : ∀ u, (prefixes u).length = k + 1
  common : ∀ u q, prefixes u <+: fromBlocks (copies u q)
  binary : ∀ u, ∃ b : List TernaryLetter, .one ∉ b ∧ prefixes u = P.prefixes u ++ b

theorem old_refinement {D : Source} {f : Word → Target}
    {j : Nat} (P : Layer D f j) (k : Nat) (hk : P.bound ≤ k) :
    Nonempty (OldRefinement P k) := by
  classical
  have hchoice : ∀ u : Level D j, ∃ R : RayCopy, R.stem = (P.copies u).stem ∧
      Set.range R.embedding ⊆ Set.range (P.copies u).embedding ∧
      ∃ p : List TernaryLetter, p.length = k + 1 ∧ ∀ q, p <+: fromBlocks (R q) := by
    intro u
    apply (P.copies u).common_prefix (k + 1)
    have h := P.root_short u
    omega
  choose R hstem hsub p hlen hp using hchoice
  refine ⟨⟨R, p, hstem, hsub, hlen, hp, ?_⟩⟩
  intro u
  obtain ⟨q, hq⟩ := hsub u ⟨0, rfl⟩
  have hold : P.prefixes u <+: fromBlocks (R u 0) := by
    rw [← hq]
    exact P.common_prefix u q
  have hpp : P.prefixes u <+: p u := List.prefix_of_prefix_length_le hold (hp u 0)
    (by rw [P.prefix_length, hlen]; omega)
  have hpQ : p u <+: fromBlocks (P.copies u q) := by rw [hq]; exact hp u 0
  exact binary_prefix_between hpp hpQ (ray_prefix_binary (P.copies u) (P.prefixes u) q
    (by rw [P.prefix_length]; exact (P.root_short u).le) (P.common_prefix u q))

noncomputable def chosenRoot {D : Source} {f : Word → Target}
    {j : Nat} {P : Layer D f j} {kind : PaperKind} {c : Level D j}
    (C : CriticalChoice P kind c) (O : OldRefinement P C.word.length) (u : Level D j) :
    List TernaryLetter := if u = c then C.word else (O.prefixes u).dropLast

@[simp] theorem chosenRoot_critical {D : Source}
    {f : Word → Target} {j : Nat} {P : Layer D f j}
    {kind : PaperKind} {c : Level D j} (C : CriticalChoice P kind c)
    (O : OldRefinement P C.word.length) : chosenRoot C O c = C.word := by
  simp [chosenRoot]

theorem critical_length_ge {D : Source} {f : Word → Target}
    {j : Nat} {P : Layer D f j} {kind : PaperKind} {c : Level D j}
    (C : CriticalChoice P kind c) : P.bound ≤ C.word.length := by
  obtain ⟨b, _, hb⟩ := C.binary
  rw [hb, List.length_append, P.prefix_length]
  omega

theorem chosenRoot_length {D : Source} {f : Word → Target}
    {j : Nat} {P : Layer D f j} {kind : PaperKind} {c : Level D j}
    (C : CriticalChoice P kind c) (O : OldRefinement P C.word.length) (u : Level D j) :
    (chosenRoot C O u).length = C.word.length := by
  by_cases h : u = c
  · simp [chosenRoot, h]
  · simp [chosenRoot, h, O.length]

theorem chosenRoot_binary {D : Source} {f : Word → Target}
    {j : Nat} {P : Layer D f j} {kind : PaperKind} {c : Level D j}
    (C : CriticalChoice P kind c) (O : OldRefinement P C.word.length) (u : Level D j) :
    ∃ b : List TernaryLetter, .one ∉ b ∧ chosenRoot C O u = P.prefixes u ++ b := by
  by_cases h : u = c
  · subst u
    simpa only [chosenRoot_critical] using C.binary
  · obtain ⟨b, hb, heq⟩ := O.binary u
    have hbne : b ≠ [] := by
      intro hnil
      have hlen := O.length u
      rw [heq, hnil, List.append_nil, P.prefix_length] at hlen
      have hk := critical_length_ge C
      omega
    refine ⟨b.dropLast, fun hmem => hb ((List.dropLast_prefix b).subset hmem), ?_⟩
    simp only [chosenRoot, h, ↓reduceIte, heq, List.dropLast_append_of_ne_nil hbne]

theorem chosenRoot_ordered {D : Source} {f : Word → Target}
    {j : Nat} {P : Layer D f j} {kind : PaperKind} {c : Level D j}
    (C : CriticalChoice P kind c) (O : OldRefinement P C.word.length)
    (u v : Level D j) (huv : u.val < v.val) :
    Sparse.lexLess (chosenRoot C O u) (chosenRoot C O v) = true := by
  obtain ⟨b, _, hb⟩ := chosenRoot_binary C O u
  obtain ⟨d, _, hd⟩ := chosenRoot_binary C O v
  have hne : P.prefixes u ≠ P.prefixes v := by
    intro h
    have hlt := P.ordered u v huv
    rw [h, Sparse.lexLess_self] at hlt
    contradiction
  rw [hb, hd, Sparse.lexLess_append_of_ne ((P.prefix_length u).trans (P.prefix_length v).symm) hne]
  exact P.ordered u v huv

/-- The future rational candidates above a noncritical node have exactly the
forced sparse-tree letter at the newly selected level. -/
theorem noncritical_child {D : Source} {f : Word → Target}
    {j : Nat} {P : Layer D f j} {kind : PaperKind} {c : Level D j}
    (C : CriticalChoice P kind c) (O : OldRefinement P C.word.length)
    (hsparse : SparseTargets f)
    (LP : SourceLevel D.nodes D.codes j kind c.val)
    (u : Level D j) (hne : u ≠ c) (a : Fin 3) (ha : child u.val a ∈ D.nodes) :
    ∀ q, ∃ b : List TernaryLetter,
      fromBlocks (O.copies u q) = chosenRoot C O u ++ RayMapModel.toLetter a :: b ∧
      (a ≠ 1 → .one ∉ b) := by
  classical
  have hune : u.val ≠ c.val := fun h => hne (Subtype.ext h)
  have hsour := (LP.children u.val u.property.1 u.property.2 a).mp ha
  have hpnil : O.prefixes u ≠ [] := by
    intro h
    have hl := O.length u
    rw [h] at hl
    simp at hl
  let letter := (O.prefixes u).getLast hpnil
  have hdecomp : chosenRoot C O u ++ [letter] = O.prefixes u := by
    simpa only [chosenRoot, hne, ↓reduceIte, letter] using List.dropLast_concat_getLast hpnil
  have hprefixTree : Sparse.InTree (O.prefixes u) :=
    Sparse.inTree_prefix
      (inTree_of_sparse (hsparse u.val _ (P.inside u (O.inside u ⟨0, rfl⟩)))) (O.common u 0)
  have hrootTree : Sparse.InTree (chosenRoot C O u) :=
    Sparse.inTree_prefix hprefixTree (by rw [← hdecomp]; exact List.prefix_append _ _)
  have hrootne : chosenRoot C O u ≠ C.word := by
    intro heq
    rcases lt_or_gt_of_ne hune with h | h
    · have hlt := chosenRoot_ordered C O u c h
      rw [chosenRoot_critical, heq, Sparse.lexLess_self] at hlt
      contradiction
    · have hlt := chosenRoot_ordered C O c u h
      rw [chosenRoot_critical, heq, Sparse.lexLess_self] at hlt
      contradiction
  have hactual : letter = Sparse.direction C.word (chosenRoot C O u) := by
    have hh := (Sparse.critical_children C.word.length (chosenRoot C O u) hrootTree
      (chosenRoot_length C O u) letter).mp (hdecomp ▸ hprefixTree)
    rw [← C.critical] at hh
    simpa only [Sparse.CriticalChildren, hrootne, ↓reduceIte] using hh
  have hletter : letter = RayMapModel.toLetter a := by
    by_cases hlt : u.val < c.val
    · have hzero : a = 0 := by simpa only [localChild, hune, hlt, ↓reduceIte] using hsour
      have hlex : Sparse.lexLess (chosenRoot C O u) C.word = true := by
        simpa only [chosenRoot_critical] using chosenRoot_ordered C O u c hlt
      rw [hactual, Sparse.direction, hlex]
      subst a
      rfl
    · have htwo : a = 2 := by simpa only [localChild, hune, hlt, ↓reduceIte] using hsour
      have hcu : c.val < u.val := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hune)
      have hlex : Sparse.lexLess C.word (chosenRoot C O u) = true := by
        simpa only [chosenRoot_critical] using chosenRoot_ordered C O c u hcu
      rw [hactual, Sparse.direction, Sparse.lexLess_asymm hlex]
      subst a
      rfl
  intro q
  obtain ⟨b, hb, heq⟩ := ray_prefix_binary (O.copies u) (O.prefixes u) q
    (by rw [O.same_stem, O.length]; have h := P.root_short u; have hk := critical_length_ge C; omega)
    (O.common u q)
  refine ⟨b, ?_, fun _ => hb⟩
  rw [heq, ← hdecomp, hletter]
  simp

/-- Old-level images and actual rational candidate copies for every allowed
next child, before synchronizing their next prefixes. -/
structure RootChoices {D : Source} {f : Word → Target}
    {j : Nat} (P : Layer D f j) where
  level : Nat
  lower : P.bound ≤ level
  roots : Level D j → List TernaryLetter
  length : ∀ u, (roots u).length = level
  binary : ∀ u, ∃ b : List TernaryLetter, .one ∉ b ∧ roots u = P.prefixes u ++ b
  ordered : ∀ u v, u.val < v.val → Sparse.lexLess (roots u) (roots v) = true
  coding : ∀ u, u.val ∈ D.codes → toBlocks (roots u) ∈ Set.range (f u.val)
  tree : ∀ u, Sparse.InTree (roots u)
  critical : roots (criticalAt D j) = Sparse.critical level
  phase : level % 3 = 2 ↔ D.kind j ≠ .split
  children : ∀ u a (ha : child u.val a ∈ D.nodes), ∃ R : RayCopy,
    Set.range R.embedding ⊆ Set.range (f u.val) ∧ ∀ q, ∃ b : List TernaryLetter,
      fromBlocks (R q) = roots u ++ RayMapModel.toLetter a :: b ∧ (a ≠ 1 → .one ∉ b)

/-- All one-level geometric choices, including forced noncritical letters,
come from the actual sparse construction. -/
theorem root_choices {D : Source} {f : Word → Target}
    {j : Nat} (P : Layer D f j)
    (hsparse : SparseTargets f) : Nonempty (RootChoices P) := by
  classical
  let kind := D.kind j
  let c := D.critical j
  have LP : SourceLevel D.nodes D.codes j kind c := D.rule j
  let cp : Level D j := criticalAt D j
  obtain ⟨C⟩ := critical_choice P hsparse kind cp
  obtain ⟨O⟩ := old_refinement P C.word.length (critical_length_ge C)
  refine ⟨{
    level := C.word.length
    lower := critical_length_ge C
    roots := chosenRoot C O
    length := chosenRoot_length C O
    binary := chosenRoot_binary C O
    ordered := chosenRoot_ordered C O
    coding := ?_
    tree := ?_
    critical := (chosenRoot_critical C O).trans C.critical
    phase := C.phase
    children := ?_
  }⟩
  · intro u hu
    obtain ⟨huc, hcode⟩ := (LP.coding u.val u.property.1 u.property.2).mp hu
    have heq : u = cp := Subtype.ext huc
    subst u
    simpa only [chosenRoot_critical] using C.coding hcode
  · intro u
    by_cases heq : u = cp
    · subst u
      rw [chosenRoot_critical, C.critical]
      exact Sparse.critical_inTree _
    · have hp : Sparse.InTree (O.prefixes u) :=
        Sparse.inTree_prefix (inTree_of_sparse
          (hsparse u.val _ (P.inside u (O.inside u ⟨0,rfl⟩)))) (O.common u 0)
      rw [chosenRoot, if_neg heq]
      exact Sparse.inTree_prefix hp (List.dropLast_prefix _)
  · intro u a ha
    by_cases heq : u = cp
    · subst u
      have hspecial : kind.special a := by
        have h := (LP.children c LP.critical_mem LP.critical_length a).mp ha
        simpa only [localChild, ↓reduceIte] using h
      simpa only [chosenRoot_critical] using C.children a hspecial
    · exact ⟨O.copies u, (O.inside u).trans (P.inside u),
        noncritical_child C O hsparse LP u heq a ha⟩

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

/-- Finite simultaneous refinement turns the actual rational candidate copies
at the children into synchronized next-level prefixes. -/
theorem step_of_root_choices {D : Source}
    {f : Word → Target} {j : Nat}
    (P : Layer D f j)
    (stable : ∀ (u : Level D j) a, child u.val a ∈ D.nodes →
      f (child u.val a) = f u.val)
    (H : RootChoices P) : Nonempty (Step P) := by
  classical
  have hchoice : ∀ v : Level D (j + 1), ∃ Q : RayCopy,
      Set.range Q.embedding ⊆ Set.range (f v.val) ∧ ∀ q, ∃ b : List TernaryLetter,
        fromBlocks (Q q) = H.roots (parent v) ++ RayMapModel.toLetter (last v) :: b ∧
        (last v ≠ 1 → .one ∉ b) := by
    intro v
    have heq : f v.val = f (parent v).val :=
      (congrArg f (child_parent v).symm).trans
        (stable (parent v) (last v) (parent_child_mem v))
    rw [heq]
    exact H.children (parent v) (last v) (parent_child_mem v)
  choose Q hQinside hQtail using hchoice
  obtain ⟨L, hL, R, p, hstem, hsub, hlen, hp, hroot⟩ := finite_common_prefix Q H.level
  have htail : ∀ v : Level D (j + 1), ∃ b : List TernaryLetter,
      p v = H.roots (parent v) ++ RayMapModel.toLetter (last v) :: b ∧
      (last v ≠ 1 → .one ∉ b) := by
    intro v
    obtain ⟨q, hq⟩ := hsub v ⟨0, rfl⟩
    obtain ⟨b, hb, hbinary⟩ := hQtail v q
    have hpre : p v <+: H.roots (parent v) ++ RayMapModel.toLetter (last v) :: b := by
      rw [← hb, hq]
      exact hp v 0
    have hfirst : H.roots (parent v) ++ [RayMapModel.toLetter (last v)] <+: p v := by
      exact List.prefix_of_prefix_length_le ⟨b, by simp⟩ hpre (by
        rw [List.length_append, H.length, List.length_singleton, hlen]
        omega)
    obtain ⟨tail, htail⟩ := hfirst
    refine ⟨tail, by simpa only [List.append_assoc, List.singleton_append] using htail.symm, ?_⟩
    intro hlast
    have hsubtail : tail <+: b := by
      apply (List.prefix_append_right_inj
        (H.roots (parent v) ++ [RayMapModel.toLetter (last v)])).mp
      rw [htail]
      simpa only [List.append_assoc, List.singleton_append] using hpre
    exact fun hmem => hbinary hlast (hsubtail.subset hmem)
  have hedge : ∀ u a (ha : child u.val a ∈ D.nodes),
      ∃ b : List TernaryLetter,
        p (childNode u a ha) = H.roots u ++ RayMapModel.toLetter a :: b ∧
        (a ≠ 1 → .one ∉ b) := by
    intro u a ha
    simpa only [parent_childNode, last_childNode] using htail (childNode u a ha)
  let next : Layer D f (j + 1) := {
    bound := L
    copies := R
    prefixes := p
    prefix_length := hlen
    common_prefix := hp
    root_short := hroot
    inside := fun v => (hsub v).trans (hQinside v)
    ordered := ordered_children H.roots H.level H.length H.ordered p (by
      intro u a ha
      obtain ⟨b, hb, _⟩ := hedge u a ha
      exact ⟨b, by simpa only [List.append_assoc, List.singleton_append] using hb.symm⟩)
  }
  exact ⟨⟨next, H.level, H.lower, hL, H.roots, H.length, H.binary, H.coding,
    H.tree, H.critical, H.phase, hedge⟩⟩


theorem exists_step {D : Source} {f : Word → Target} {j : Nat}
    (P : Layer D f j) (hsparse : SparseTargets f)
    (stable : ∀ (u : Level D j) a, child u.val a ∈ D.nodes →
      f (child u.val a) = f u.val) : Nonempty (Step P) := by
  obtain ⟨H⟩ := root_choices P hsparse
  exact step_of_root_choices P stable H

/-- The target assignment can vary across slots; in this iteration it is
constant on each edge, so the assigned copy is retained through all steps. -/
noncomputable def layerSequence (D : Source) (f : Word → Target)
    (P0 : Layer D f 0) (pick : ∀ j, (P : Layer D f j) → Step P) :
    (j : Nat) → Layer D f j
  | 0 => P0
  | j+1 => (pick j (layerSequence D f P0 pick j)).next

end AllThoseBigRamsey.Pseudotree.Reservoir
