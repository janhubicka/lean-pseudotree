import PseudotreeValidation.GeneralizedProjection
import PseudotreeValidation.SparseNormalization
import PseudotreeValidation.DiaryCanonization

/-! The generalized literal diary grammar, with neither a distinguished
branch nor a bound on the number of turns. The local geometry of the
sparse construction is reused unchanged. -/
namespace AllThoseBigRamsey.Pseudotree
open RayEmbeddings

/-- The manuscript's four rules at one level, stated directly on finite
SETS of words, with lexicographic comparison and an actual critical word. -/
structure GeneralizedLevel (nodes codes : Finset DiaryWord) (j : Nat)
    (kind : PaperKind) (critical : DiaryWord) : Prop where
  critical_mem : critical ∈ nodes
  critical_length : critical.length = j
  coding : ∀ w ∈ nodes, w.length = j → (w ∈ codes ↔ w = critical ∧ kind.coded = true)
  children : ∀ w ∈ nodes, w.length = j → ∀ a : Fin 3,
    child w a ∈ nodes ↔ localChild critical kind.special w a

/-- Raw finite-set formulation. Height is a bound with a critical node at
each smaller level, so trailing empty levels are excluded. -/
structure GeneralizedTreeAxioms (nodes codes : Finset DiaryWord) (height : Nat) : Prop where
  height_pos : 0 < height
  bounded : ∀ w ∈ nodes, w.length < height
  prefix_closed : ∀ w ∈ nodes, ∀ j ≤ w.length, w.take j ∈ nodes
  code_subset : codes ⊆ nodes
  level : ∀ j < height, ∃ kind critical, GeneralizedLevel nodes codes j kind critical
  initial : ∀ critical, ¬GeneralizedLevel nodes codes 0 .turn critical
  following : ∀ j critical kind previous,
    GeneralizedLevel nodes codes (j + 1) .turn critical →
    GeneralizedLevel nodes codes j kind previous → critical ≠ child previous 1

structure GeneralizedDiary (n : Nat) where
  nodes : Finset DiaryWord
  codes : Finset DiaryWord
  axioms : ∃ height, GeneralizedTreeAxioms nodes codes height
  size : codes.card = n

theorem GeneralizedLevel.unique {nodes codes : Finset DiaryWord} {j : Nat}
    {kind kind' : PaperKind} {c c' : DiaryWord}
    (P : GeneralizedLevel nodes codes j kind c) (Q : GeneralizedLevel nodes codes j kind' c') :
    c = c' ∧ kind = kind' := by
  have hcrit : c = c' := by
    by_contra hne
    have h0 := (P.children c P.critical_mem P.critical_length 0).symm.trans
      (Q.children c P.critical_mem P.critical_length 0)
    have h1 := (P.children c P.critical_mem P.critical_length 1).symm.trans
      (Q.children c P.critical_mem P.critical_length 1)
    have h2 := (P.children c P.critical_mem P.critical_length 2).symm.trans
      (Q.children c P.critical_mem P.critical_length 2)
    cases kind <;> by_cases hlt : c < c' <;>
      simp [localChild, PaperKind.special, hne, hlt] at h0 h1 h2
  subst c'
  refine ⟨rfl, ?_⟩
  have hc := (P.coding c P.critical_mem P.critical_length).symm.trans
    (Q.coding c P.critical_mem P.critical_length)
  have h0 := (P.children c P.critical_mem P.critical_length 0).symm.trans
    (Q.children c P.critical_mem P.critical_length 0)
  have h1 := (P.children c P.critical_mem P.critical_length 1).symm.trans
    (Q.children c P.critical_mem P.critical_length 1)
  cases kind <;> cases kind' <;> simp_all [localChild, PaperKind.special, PaperKind.coded]

namespace GeneralizedDiary

/-- Raw diary axioms imply the exact finite-tree hypothesis of restricted
Milliken. The node set is unchanged. -/
noncomputable def shape (D : GeneralizedDiary n) : RayMilliken.Shape where
  nodes := D.nodes
  root_mem := by
    obtain ⟨height, T⟩ := D.axioms
    obtain ⟨kind, w, P⟩ := T.level 0 T.height_pos
    have hw : w = [] := List.length_eq_zero_iff.mp P.critical_length
    exact hw ▸ P.critical_mem
  prefix_closed := by
    intro s t hst
    obtain ⟨height, T⟩ := D.axioms
    have h := T.prefix_closed (s ++ t) hst s.length (by simp)
    simpa only [List.take_append_length] using h
  one_per_level := by
    intro s hs t ht hlen hs1 ht1
    obtain ⟨p, rfl⟩ := hs1
    obtain ⟨q, rfl⟩ := ht1
    obtain ⟨height, T⟩ := D.axioms
    have hp : p ∈ D.nodes := by
      simpa only [List.take_append_length] using T.prefix_closed _ hs p.length (by simp)
    have hq : q ∈ D.nodes := by
      simpa only [List.take_append_length] using T.prefix_closed _ ht q.length (by simp)
    have heq : p.length = q.length := by
      simpa only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] using hlen
    have hbound := T.bounded p hp
    obtain ⟨kind, c, P⟩ := T.level p.length hbound
    have hp' := (P.children p hp rfl 1).mp hs
    have hq' := (P.children q hq heq.symm 1).mp ht
    have hpc : p = c := by
      by_contra hne
      by_cases hlt : p < c <;> simp [localChild, hne, hlt] at hp'
    have hqc : q = c := by
      by_contra hne
      by_cases hlt : q < c <;> simp [localChild, hne, hlt] at hq'
    rw [hpc, hqc]

@[simp] theorem shape_nodes (D : GeneralizedDiary n) : D.shape.nodes = D.nodes := rfl

theorem code_node (D : GeneralizedDiary n) {w : DiaryWord} (hw : w ∈ D.codes) : w ∈ D.shape.nodes := by
  obtain ⟨_, T⟩ := D.axioms
  exact T.code_subset hw


end GeneralizedDiary

namespace GeneralizedNormalization
open LevelProjection
open DiaryNormalization (essential mem_essential_iff RawNode ForkAt schedule
  schedule_strict schedule_mem schedule_no_between length_mem_essential)
open SparseNormalization (Point Tree critical critical_length point_at_level
  raw_child_at one_critical essential_cases fork_critical tree_children
  rawNode_tree raw_noncritical_children raw_coding kind kind_coded)

theorem raw_one_child {C : Finset Word} (hC : ∀ w ∈ C, Point w)
    {w : Word} (hw : w ∈ C) {j : Nat} (hone : w[j]? = some 1) :
    RawNode C (child (critical j) 1) := by
  obtain ⟨hjw, hletter⟩ := List.getElem?_eq_some_iff.mp hone
  have hchild := raw_child_at hw hjw
  rw [hletter] at hchild
  have heq := (one_critical (j := j) hC hchild (by simp [hjw.le])).1
  simpa only [heq] using hchild

theorem selected_critical {C : Finset Word} (hC : ∀ w ∈ C, Point w)
    {j : Nat} (hj : j ∈ selected C) : RawNode C (critical j) := by
  by_cases he : j ∈ essential C
  · rcases mem_essential_iff.mp he with ⟨w, hw, hlen⟩ | hf
    · have heq := ((point_at_level hlen).mp (hC w hw)).2
      exact ⟨w, hw, by rw [← heq]⟩
    · exact (fork_critical hC hf).2.1
  · obtain ⟨w, hw, hone⟩ := nonessential_event hj he
    obtain ⟨v, hv, hp⟩ := raw_one_child hC hw hone
    exact ⟨v, hv, (List.prefix_append (critical j) [1]).trans hp⟩

theorem kind_turn_not_essential {C : Finset Word} (hC : ∀ w ∈ C, Point w)
    {j : Nat} (ht : kind C j = .turn) : j ∉ essential C := by
  classical
  intro he
  rcases essential_cases hC he with hc | hf
  · simp only [kind, hc, ite_true] at ht
    split at ht <;> cases ht
  · by_cases hc : critical j ∈ C
    · simp only [kind, hc, ite_true] at ht
      split at ht <;> cases ht
    · simp [kind, hc, hf] at ht

theorem raw_critical_children {C : Finset DiaryWord}
    (hC : ∀ w ∈ C, Point w) {j : Nat} (hj : j ∈ selected C)
    (a : Fin 3) :
    RawNode C (child (critical j) a) ↔ (kind C j).special a := by
  classical
  have hr := selected_critical hC hj
  have htree := tree_children j (critical j) (rawNode_tree hC hr) (critical_length j)
  by_cases hc : critical j ∈ C
  · have hphase := ((point_at_level (critical_length j)).mp (hC _ hc)).1
    have hallowed (b : Fin 3) (hb : RawNode C (child (critical j) b)) : b = 1 := by
      simpa [hphase] using (htree b).mp (rawNode_tree hC hb)
    by_cases h1 : RawNode C (child (critical j) 1)
    · simp only [kind, hc, h1, ↓reduceIte, PaperKind.special]
      exact ⟨hallowed a, fun h => h ▸ h1⟩
    · simp only [kind, hc, h1, ↓reduceIte, PaperKind.special, iff_false]
      exact fun ha => h1 (hallowed a ha ▸ ha)
  · by_cases hf : ForkAt C j
    · obtain ⟨hphase, _, h0, h2⟩ := fork_critical hC hf
      simp only [kind, hc, hf, ↓reduceIte, PaperKind.special]
      constructor
      · intro ha
        simpa [hphase] using (htree a).mp (rawNode_tree hC ha)
      · rintro (rfl | rfl)
        · exact h0
        · exact h2
    · have he : j ∉ essential C := fun h => (essential_cases hC h).elim hc hf
      obtain ⟨w, hw, hone⟩ := nonessential_event hj he
      have h1 := raw_one_child hC hw hone
      have hphase := (one_critical hC h1 (critical_length j)).2
      simp only [kind, hc, hf, ↓reduceIte, PaperKind.special]
      constructor
      · intro ha
        simpa [hphase] using (htree a).mp (rawNode_tree hC ha)
      · rintro rfl
        exact h1

theorem raw_children {C : Finset DiaryWord}
    (hC : ∀ w ∈ C, Point w) {j : Nat} (hj : j ∈ selected C)
    {w : DiaryWord} (hw : RawNode C w) (hlen : w.length = j) (a : Fin 3) :
    RawNode C (child w a) ↔ localChild (critical j) (kind C j).special w a := by
  by_cases heq : w = critical j
  · subst w
    simpa [localChild] using raw_critical_children hC hj a
  · simpa only [localChild, heq, ite_false] using raw_noncritical_children hC hw hlen heq a

theorem continues_child {C : Finset DiaryWord}
    (hC : ∀ w ∈ C, Point w) {j : Nat} (hj : j ∈ selected C)
    (hc : (kind C j).continues = true) : RawNode C (child (critical j) 1) := by
  apply (raw_critical_children hC hj 1).mpr
  cases hk : kind C j <;> simp_all [PaperKind.continues, PaperKind.special]

noncomputable def normalizedCritical (C : Finset DiaryWord)  (i : Nat) : DiaryWord :=
  project (schedule (selected C)) (critical (schedule (selected C) i)) i

theorem normalized_critical {C : Finset DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hne : C.Nonempty) {i : Nat} (hi : i < (selected C).card) :
    normalizedCritical C i ∈ nodes C ∧
      inverse (C : Set Word) (schedule (selected C)) (normalizedCritical C i) =
        critical (schedule (selected C) i) :=
  project_of_rawNode hne (selected_critical hC (schedule_mem hi)) (critical_length _)

@[simp] theorem normalizedCritical_length (C : Finset DiaryWord)  (i : Nat) :
    (normalizedCritical C i).length = i := project_length _ _ _

theorem normalized_level_data {C : Finset DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hne : C.Nonempty)
    {i : Nat} (hi : i < (selected C).card)
    {s : DiaryWord} (hs : s ∈ nodes C) (hlen : s.length = i) :
    (s ∈ codes C ↔ s = normalizedCritical C i ∧
      (kind C (schedule (selected C) i)).coded = true) ∧
    (∀ a, child s a ∈ nodes C ↔
      localChild (normalizedCritical C i) (kind C (schedule (selected C) i)).special s a) := by
  obtain ⟨hq, hinvq⟩ := normalized_critical hC hne hi
  have hraw := inverse_rawNode hne hs
  have hrawlen : (inverse (C : Set Word) (schedule (selected C)) s).length =
      schedule (selected C) i := by rw [inverse_length hne hs, hlen]
  have heq : inverse (C : Set Word) (schedule (selected C)) s =
      critical (schedule (selected C) i) ↔ s = normalizedCritical C i := by
    rw [← hinvq]
    exact ⟨inverse_injective hne hs hq, congrArg _⟩
  have hlt : inverse (C : Set Word) (schedule (selected C)) s <
      critical (schedule (selected C) i) ↔ s < normalizedCritical C i := by
    rw [← hinvq]
    exact inverse_lt_iff hne hs hq
  constructor
  · rw [code_iff_inverse hne hs, raw_coding hC hrawlen, heq]
  · intro a
    rw [child_iff_rawChild hne hs, raw_children hC (schedule_mem hi) hraw hrawlen]
    simp only [localChild, heq, hlt]


theorem kind_initial_not_turn {C : Finset Word} (hC : ∀ w ∈ C, Point w)
    (hne : C.Nonempty) : kind C (schedule (selected C) 0) ≠ .turn := by
  intro ht
  exact kind_turn_not_essential hC ht (initial_essential hne)

theorem kind_following {C : Finset Word} (hC : ∀ w ∈ C, Point w)
    (hne : C.Nonempty) {i : Nat} (hi : i+1 < (selected C).card)
    (ht : kind C (schedule (selected C) (i+1)) = .turn) :
    normalizedCritical C (i+1) ≠ child (normalizedCritical C i) 1 := by
  let p := schedule (selected C) i
  let q := schedule (selected C) (i+1)
  have hL := selected_nonempty hne
  have hpq : p < q := schedule_strict hL (Nat.lt_succ_self i)
  have hnext : Next C p q := adjacent_next (schedule_mem (by omega : i < (selected C).card))
    (schedule_mem hi) hpq (fun k hk hlo hhi => schedule_no_between hL hk hlo hhi)
  obtain ⟨w, hw, hnot, hone⟩ := hnext.2.1.resolve_left (kind_turn_not_essential hC ht)
  obtain ⟨hqw, hletter⟩ := List.getElem?_eq_some_iff.mp hone
  have hchild := raw_child_at hw hqw
  rw [hletter] at hchild
  have hcrit := (one_critical (j := q) hC hchild (by simp [hqw.le])).1
  have hn : (critical q)[p]? ≠ some 1 := by
    rw [← hcrit, List.getElem?_take, if_pos hpq]
    exact hnot
  have hgd : ((critical q)[p]?).getD 0 ≠ (1 : Fin 3) := by
    cases h : (critical q)[p]? with
    | none => decide
    | some a => simpa [h] using hn
  intro heq
  have hleft : (normalizedCritical C (i+1))[i]? =
      some (((critical q)[p]?).getD 0) := by
    have hidx : i < (normalizedCritical C (i+1)).length := by simp
    rw [List.getElem?_eq_getElem hidx]
    simp [normalizedCritical, project_get, p, q]
  have hright : (child (normalizedCritical C i) 1)[i]? = some 1 := by
    rw [child, List.getElem?_append_right (by simp), normalizedCritical_length, Nat.sub_self]
    rfl
  have h := congrArg (fun s : Word => s[i]?) heq
  rw [hleft, hright] at h
  exact hgd (Option.some.inj h)

theorem normalized_level {C : Finset Word} (hC : ∀ w ∈ C, Point w)
    (hne : C.Nonempty) {i : Nat} (hi : i < (selected C).card) :
    GeneralizedLevel (nodes C) (codes C) i (kind C (schedule (selected C) i))
      (normalizedCritical C i) where
  critical_mem := (normalized_critical hC hne hi).1
  critical_length := normalizedCritical_length C i
  coding := fun _ hs hlen => (normalized_level_data hC hne hi hs hlen).1
  children := fun _ hs hlen => (normalized_level_data hC hne hi hs hlen).2

/-- The local grammar of the manuscript holds for the normalized image of
every finite nonempty subset of the actual sparse coding set. -/
theorem normalized_axioms {C : Finset Word} (hC : ∀ w ∈ C, Point w)
    (hne : C.Nonempty) :
    GeneralizedTreeAxioms (nodes C) (codes C) (selected C).card where
  height_pos := Finset.card_pos.mpr (selected_nonempty hne)
  bounded := fun _ hw => nodes_bounded hw
  prefix_closed := fun _ hw _ hj => nodes_prefix_closed hw hj
  code_subset := codes_subset_nodes C
  level := fun i hi => ⟨_, _, normalized_level hC hne hi⟩
  initial := by
    intro c P
    have hpos := Finset.card_pos.mpr (selected_nonempty hne)
    have heq := (GeneralizedLevel.unique (normalized_level hC hne hpos) P).2
    exact kind_initial_not_turn hC hne heq
  following := by
    intro i c pk p P Q
    have hi : i+1 < (selected C).card := by
      simpa only [P.critical_length] using nodes_bounded P.critical_mem
    obtain ⟨hc, ht⟩ := GeneralizedLevel.unique (normalized_level hC hne hi) P
    have hp := (GeneralizedLevel.unique (normalized_level hC hne (by omega)) Q).1
    rw [← hc, ← hp]
    exact kind_following hC hne hi ht

noncomputable def normalize {C : Finset Word} (hC : ∀ w ∈ C, Point w)
    (hne : C.Nonempty) : GeneralizedDiary C.card where
  nodes := nodes C
  codes := codes C
  axioms := ⟨_, normalized_axioms hC hne⟩
  size := codes_card hne

/-- Actual extraction into the finite shape class of restricted Milliken. -/
theorem extraction {C : Finset Word} (hC : ∀ w ∈ C, Point w)
    (hne : C.Nonempty) :
    ∃ D : GeneralizedDiary C.card, ∃ f : RayStrongMap, D.codes.image f.map = C :=
  ⟨normalize hC hne, rayMap hne, rayMap_codes hne⟩

end GeneralizedNormalization
end AllThoseBigRamsey.Pseudotree
