import PseudotreeValidation.GeneralizedDiaryGrammar
import PseudotreeValidation.DiaryRecoverySource

/-!
# Literal generalized diaries are fixed by normalization

No chain or maximum hypothesis is needed. Each node has a coding
descendant, every split/coding level is essential, and a turn is eligible
from the immediately preceding level by the generalized adjacency rule.
-/

namespace AllThoseBigRamsey.Pseudotree
open RayEmbeddings

namespace GeneralizedDiary

private theorem noncode_has_child {D : GeneralizedDiary n} {height : Nat}
    (T : GeneralizedTreeAxioms D.nodes D.codes height) {u : Word}
    (hu : u ∈ D.nodes) (hn : u ∉ D.codes) :
    ∃ a : Fin 3, child u a ∈ D.nodes := by
  obtain ⟨kind, c, P⟩ := T.level u.length (T.bounded u hu)
  by_cases heq : u = c
  · subst c
    cases kind with
    | split =>
      exact ⟨0, (P.children u hu rfl 0).mpr (by simp [localChild, PaperKind.special])⟩
    | leaf =>
      exact False.elim (hn ((P.coding u hu rfl).mpr ⟨rfl, rfl⟩))
    | code =>
      exact False.elim (hn ((P.coding u hu rfl).mpr ⟨rfl, rfl⟩))
    | turn =>
      exact ⟨1, (P.children u hu rfl 1).mpr (by simp [localChild, PaperKind.special])⟩
  · by_cases hl : u < c
    · exact ⟨0, (P.children u hu rfl 0).mpr (by simp [localChild, heq, hl])⟩
    · exact ⟨2, (P.children u hu rfl 2).mpr (by simp [localChild, heq, hl])⟩

/-- Prefix closure of the coding set follows from the independent local
grammar and bounded height; it is not an extra realization assumption. -/
theorem nodes_iff_prefix_code (D : GeneralizedDiary n) (s : Word) :
    s ∈ D.nodes ↔ ∃ w ∈ D.codes, s.IsPrefix w := by
  obtain ⟨height, T⟩ := D.axioms
  constructor
  · intro hs
    have aux : ∀ k : Nat, ∀ u : Word, u ∈ D.nodes →
        height - u.length = k → ∃ w ∈ D.codes, u.IsPrefix w := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        intro u hu hk
        by_cases hc : u ∈ D.codes
        · exact ⟨u, hc, List.prefix_rfl⟩
        · obtain ⟨a, ha⟩ := noncode_has_child T hu hc
          have hb := T.bounded (child u a) ha
          have hlt : height - (child u a).length < k := by
            simp only [child, List.length_append, List.length_singleton] at hb ⊢
            omega
          obtain ⟨w, hw, hp⟩ := ih _ hlt (child u a) ha rfl
          exact ⟨w, hw, (List.prefix_append u [a]).trans hp⟩
    exact aux _ s hs rfl
  · rintro ⟨w, hw, hp⟩
    have h := T.prefix_closed w (T.code_subset hw) s.length hp.length_le
    rw [← List.prefix_iff_eq_take.mp hp] at h
    exact h

theorem codes_nonempty (D : GeneralizedDiary n) : D.codes.Nonempty := by
  obtain ⟨w, hw, _⟩ := (D.nodes_iff_prefix_code []).mp D.shape.root_mem
  exact ⟨w, hw⟩

theorem nodes_eq_of_codes_eq {D E : GeneralizedDiary n} (h : D.codes = E.codes) :
    D.nodes = E.nodes := by
  ext w
  rw [D.nodes_iff_prefix_code, E.nodes_iff_prefix_code, h]

end GeneralizedDiary

namespace GeneralizedNormalization
open LevelProjection
open DiaryNormalization (essential mem_essential_iff fork_mem_essential
  length_mem_essential schedule rank)
open DiaryRecovery (schedule_range rank_range)

private theorem code_child_mem {D : GeneralizedDiary n} {height : Nat}
    (T : GeneralizedTreeAxioms D.nodes D.codes height) {w : Word} (hw : w ∈ D.codes)
    {j : Nat} (hj : j < w.length) : child (w.take j) w[j] ∈ D.nodes := by
  have hp := T.prefix_closed w (T.code_subset hw) (j+1) (by omega)
  simpa only [child, List.take_add_one, List.getElem?_eq_getElem hj,
    Option.toList_some] using hp

private theorem prefix_child_get {c w : Word} {a : Fin 3}
    (h : (child c a).IsPrefix w) : w[c.length]? = some a := by
  obtain ⟨tail, rfl⟩ := h
  simp [child]

/-- A split in the raw tree is witnessed by two actual coding descendants. -/
theorem split_essential {D : GeneralizedDiary n} {height j : Nat} {c : Word}
    (_T : GeneralizedTreeAxioms D.nodes D.codes height)
    (P : GeneralizedLevel D.nodes D.codes j .split c) : j ∈ essential D.codes := by
  have h0 : child c 0 ∈ D.nodes :=
    (P.children c P.critical_mem P.critical_length 0).mpr (by
      simp [localChild, PaperKind.special])
  have h2 : child c 2 ∈ D.nodes :=
    (P.children c P.critical_mem P.critical_length 2).mpr (by
      simp [localChild, PaperKind.special])
  obtain ⟨s, hs, hcs⟩ := (D.nodes_iff_prefix_code _).mp h0
  obtain ⟨t, ht, hct⟩ := (D.nodes_iff_prefix_code _).mp h2
  have hjs : j < s.length := by
    have := hcs.length_le
    simp only [child, List.length_append, List.length_singleton, P.critical_length] at this
    omega
  have hjt : j < t.length := by
    have := hct.length_le
    simp only [child, List.length_append, List.length_singleton, P.critical_length] at this
    omega
  have hpreS : s.take j = c := by
    have hc : c.IsPrefix s := (List.prefix_append c [0]).trans hcs
    simpa only [P.critical_length] using (List.prefix_iff_eq_take.mp hc).symm
  have hpreT : t.take j = c := by
    have hc : c.IsPrefix t := (List.prefix_append c [2]).trans hct
    simpa only [P.critical_length] using (List.prefix_iff_eq_take.mp hc).symm
  apply fork_mem_essential
  refine ⟨s, hs, t, ht, hjs, hjt, hpreS.trans hpreT.symm, ?_⟩
  have hsget := prefix_child_get hcs
  have htget := prefix_child_get hct
  rw [P.critical_length] at hsget htget
  simp only [hsget, htget, ne_eq, Option.some.injEq]
  decide

theorem nonturn_essential {D : GeneralizedDiary n} {height j : Nat} {c : Word}
    {kind : PaperKind} (T : GeneralizedTreeAxioms D.nodes D.codes height)
    (P : GeneralizedLevel D.nodes D.codes j kind c) (hk : kind ≠ .turn) :
    j ∈ essential D.codes := by
  cases kind with
  | split => exact split_essential T P
  | leaf =>
    have hc := (P.coding c P.critical_mem P.critical_length).mpr ⟨rfl, rfl⟩
    simpa only [P.critical_length] using length_mem_essential hc
  | code =>
    have hc := (P.coding c P.critical_mem P.critical_length).mpr ⟨rfl, rfl⟩
    simpa only [P.critical_length] using length_mem_essential hc
  | turn => exact (hk rfl).elim

/-- A turn has neither a coding node nor a fork at its level. -/
theorem turn_not_essential_source {D : GeneralizedDiary n} {height j : Nat} {c : Word}
    (T : GeneralizedTreeAxioms D.nodes D.codes height)
    (P : GeneralizedLevel D.nodes D.codes j .turn c) : j ∉ essential D.codes := by
  intro he
  rcases mem_essential_iff.mp he with ⟨w, hw, hlen⟩ | hfork
  · have hc := (P.coding w (T.code_subset hw) hlen).mp hw
    simp [PaperKind.coded] at hc
  · obtain ⟨s, hs, t, ht, hjs, hjt, hpre, hne⟩ := hfork
    have hsnode : s.take j ∈ D.nodes := T.prefix_closed s (T.code_subset hs) j hjs.le
    have htchild := code_child_mem T ht hjt
    rw [← hpre] at htchild
    have ha := (P.children (s.take j) hsnode (by simp [hjs.le]) s[j]).mp
      (code_child_mem T hs hjs)
    have hb := (P.children (s.take j) hsnode (by simp [hjs.le]) t[j]).mp htchild
    have hab : s[j] = t[j] := by
      by_cases heq : s.take j = c
      · simp only [localChild, ite_eq_left heq, PaperKind.special] at ha hb
        exact ha.trans hb.symm
      · by_cases hlt : s.take j < c
        · simp only [localChild, ite_eq_right heq, ite_eq_left hlt] at ha hb
          exact ha.trans hb.symm
        · simp only [localChild, ite_eq_right heq, ite_eq_right hlt] at ha hb
          exact ha.trans hb.symm
    exact hne (by simp only [List.getElem?_eq_getElem hjs,
      List.getElem?_eq_getElem hjt, hab])


/-- A turn at level j+1 has a coding descendant taking 1 there, but
not at level j: otherwise its critical node would be the 1-child of
the preceding critical node. -/
theorem turn_candidate {D : GeneralizedDiary n} {height j : Nat}
    {c previous : Word} {kind : PaperKind}
    (T : GeneralizedTreeAxioms D.nodes D.codes height)
    (P : GeneralizedLevel D.nodes D.codes (j+1) .turn c)
    (Q : GeneralizedLevel D.nodes D.codes j kind previous) :
    Candidate D.codes j (j+1) := by
  have hc : child c 1 ∈ D.nodes :=
    (P.children c P.critical_mem P.critical_length 1).mpr
      (by simp [localChild, PaperKind.special])
  obtain ⟨w, hw, hp⟩ := (D.nodes_iff_prefix_code _).mp hc
  have hget := prefix_child_get hp
  rw [P.critical_length] at hget
  refine Or.inr ⟨w, hw, ?_, hget⟩
  intro hprev
  obtain ⟨hjw, ha⟩ := List.getElem?_eq_some_iff.mp hprev
  have hnode := T.prefix_closed w (T.code_subset hw) j hjw.le
  have hchild := code_child_mem T hw hjw
  rw [ha] at hchild
  have h := (Q.children (w.take j) hnode (by simp [hjw.le]) 1).mp hchild
  have hparent : w.take j = previous := by
    by_contra hne
    by_cases hl : w.take j < previous <;> simp [localChild, hne, hl] at h
  have hcpre : c.IsPrefix w := (List.prefix_append c [1]).trans hp
  have htake : c = w.take (j+1) := by
    simpa only [P.critical_length] using List.prefix_iff_eq_take.mp hcpre
  apply T.following j c kind previous P Q
  rw [htake, ← List.take_append_getElem hjw, ha, hparent]
  rfl

/-- A normalized diary retains precisely all its levels, even when
successive turns alternate between distinct branches. -/
theorem selected_source {D : GeneralizedDiary n} {height : Nat}
    (T : GeneralizedTreeAxioms D.nodes D.codes height) :
    selected D.codes = Finset.range height := by
  have hessential (j : Nat) (hj : j ∈ essential D.codes) : j < height := by
    rcases mem_essential_iff.mp hj with ⟨w, hw, rfl⟩ | ⟨w, hw, _, _, hj, _⟩
    · exact T.bounded w (T.code_subset hw)
    · exact hj.trans (T.bounded w (T.code_subset hw))
  ext j
  rw [mem_selected_iff, Finset.mem_range]
  constructor
  · intro hj
    cases hj with
    | first hf => exact hessential _ hf.1
    | next _ hn =>
      rcases hn.2.1 with he | ⟨w, hw, _, hone⟩
      · exact hessential _ he
      · exact (List.getElem?_eq_some_iff.mp hone).1.trans (T.bounded w (T.code_subset hw))
  · intro hj
    induction j with
    | zero =>
      obtain ⟨kind, c, P⟩ := T.level 0 hj
      have hn : kind ≠ .turn := by
        intro heq
        subst kind
        exact T.initial c P
      exact Reached.first ⟨nonturn_essential T P hn, fun _ _ => Nat.zero_le _⟩
    | succ j ih =>
      obtain ⟨kind, c, P⟩ := T.level (j+1) hj
      by_cases hk : kind = .turn
      · subst kind
        obtain ⟨pk, previous, Q⟩ := T.level j (by omega)
        exact Reached.next (ih (by omega)) ⟨by omega, turn_candidate T P Q,
          fun k h₁ h₂ => by omega⟩
      · exact mem_selected_iff.mp (essential_subset_selected D.codes (nonturn_essential T P hk))

theorem code_source (D : GeneralizedDiary n) {w : Word} (hw : w ∈ D.codes) :
    code D.codes w = w := by
  obtain ⟨height, T⟩ := D.axioms
  have hlen := T.bounded w (T.code_subset hw)
  unfold code
  rw [selected_source T, rank_range hlen]
  apply List.ext_getElem
  · simp only [project_length]
  · intro i hi hi'
    have hil : i < w.length := by simpa only [project_length] using hi
    rw [project_get _ _ hil, schedule_range (lt_trans hil hlen)]
    simp only [List.getElem?_eq_getElem hil, Option.getD_some]

theorem codes_source (D : GeneralizedDiary n) : codes D.codes = D.codes := by
  classical
  unfold codes
  ext w
  constructor
  · intro hw
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hw
    rw [code_source D hu] at heq
    exact heq ▸ hu
  · intro hw
    exact Finset.mem_image.mpr ⟨w, hw, code_source D hw⟩

theorem nodes_source (D : GeneralizedDiary n) : nodes D.codes = D.nodes := by
  classical
  unfold nodes
  rw [codes_source D]
  ext w
  rw [D.nodes_iff_prefix_code]
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨c, hc, j, hj, rfl⟩
    exact ⟨c, hc, List.take_prefix _ _⟩
  · rintro ⟨c, hc, hpre⟩
    exact ⟨c, hc, w.length, by have := hpre.length_le; omega,
      (List.prefix_iff_eq_take.mp hpre).symm⟩

/-- Exact labelled recovery for every ray-preserving strong image. -/
theorem labelled_image_recovery (D : GeneralizedDiary n) (f : RayStrongMap)
    {w : Word} (hw : w ∈ D.codes) :
    code (D.codes.image f.map) (f.map w) = w :=
  (code_image f D.codes hw).trans (code_source D hw)

theorem image_recovery (D : GeneralizedDiary n) (f : RayStrongMap) :
    codes (D.codes.image f.map) = D.codes :=
  (codes_image f D.codes).trans (codes_source D)

theorem image_nodes_recovery (D : GeneralizedDiary n) (f : RayStrongMap) :
    nodes (D.codes.image f.map) = D.nodes :=
  (nodes_image f D.codes).trans (nodes_source D)

end GeneralizedNormalization
end AllThoseBigRamsey.Pseudotree
