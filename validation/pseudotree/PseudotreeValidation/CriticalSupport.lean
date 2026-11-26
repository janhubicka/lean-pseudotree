import PseudotreeValidation.CriticalDepth
import PseudotreeValidation.GeneralizedCanonization

/-! Range support at a selected level of a critical copy. Every node
of a critical copy is determined by a coding descendant and a selected
level; a coding point or a genuine fork of coding descendants supplies
such a level. These are the support facts needed for relative amalgamation
and the identification with expanded self-copies. -/

namespace AllThoseBigRamsey.Pseudotree.CriticalCopies
open RayEmbeddings RayMapModel
open SparseNormalization (Tree Point critical critical_length tree_prefix point_tree)
open DiaryRecovery (FirstFork firstFork_map_iff map_take firstFork_of_split)

/-- Completion uses exactly the level schedule of the critical map. -/
@[simp] theorem total_level (X : CriticalMap) (j : Nat) :
    (total X).level j = X.level j := rfl

theorem prefix_at_level_mem (X : CriticalMap) (u : Node) {j : Nat}
    (hj : j ≤ u.val.length) :
    (X.map u).take (X.level j) ∈ copyRange X := by
  let v : Node := ⟨u.val.take j,tree_prefix u.property (List.take_prefix _ _)⟩
  refine ⟨v,?_⟩
  have h := map_take (total X) u.val j hj
  change (total X).map v.val = ((total X).map u.val).take ((total X).level j) at h
  simpa only [total_agrees X v,total_agrees X u,total_level] using h

/-- It suffices to know that a node is a prefix of a point of the range
and that its length is a retained level. -/
theorem prefix_mem_of_retained (X : CriticalMap) {p w : Word}
    (hp : p.IsPrefix w) (hw : w ∈ copyRange X)
    (hlevel : ∃ j, p.length = X.level j) : p ∈ copyRange X := by
  obtain ⟨u,hu⟩ := hw
  obtain ⟨j,hj⟩ := hlevel
  have hl := hp.length_le
  rw [← hu,hj,← level_eq_length X u] at hl
  have hj' : j ≤ u.val.length := X.level_strict.le_iff_le.mp hl
  have hmem := prefix_at_level_mem X u hj'
  rwa [hu,← hj,← List.prefix_iff_eq_take.mp hp] at hmem

theorem mem_length_retained (X : CriticalMap) {w : Word} (hw : w ∈ copyRange X) :
    ∃ j, w.length = X.level j := by
  obtain ⟨u,rfl⟩ := hw
  exact ⟨u.val.length,X.length_map u⟩

/-- A genuine first fork of two range points occurs at a retained level.
In particular every common prefix witnessed by different next digits
is in the critical-copy range. -/
theorem fork_length_retained (X : CriticalMap) {s t : Word} {k : Nat}
    (hs : s ∈ copyRange X) (ht : t ∈ copyRange X) (hf : FirstFork s t k) :
    ∃ j, k = X.level j := by
  obtain ⟨u,hu⟩ := hs
  obtain ⟨v,hv⟩ := ht
  have h : FirstFork ((total X).map u.val) ((total X).map v.val) k := by
    simpa only [total_agrees X u,total_agrees X v,hu,hv] using hf
  obtain ⟨j,_,hj⟩ := (firstFork_map_iff (total X) u.val v.val k).mp h
  exact ⟨j,by simpa only [total_level] using hj⟩

theorem fork_prefix_mem (X : CriticalMap) {p s t : Word} {a b : Fin 3}
    (hs : s ∈ copyRange X) (ht : t ∈ copyRange X)
    (hp : (p ++ [a]).IsPrefix s) (hq : (p ++ [b]).IsPrefix t) (hab : a ≠ b) :
    p ∈ copyRange X := by
  have hprefix := (List.prefix_append p [a]).trans hp
  obtain ⟨u,hu⟩ := hp
  obtain ⟨v,hv⟩ := hq
  have hf : FirstFork s t p.length := by
    rw [← hu,← hv]
    simpa only [List.append_assoc,List.singleton_append] using firstFork_of_split p u v a b hab
  exact prefix_mem_of_retained X hprefix hs
    (fork_length_retained X hs ht hf)

/-- A node of R has a coding descendant, by the actual definition of R
as the prefix closure of the sparse coding set. -/
theorem node_has_point (u : Node) :
    ∃ w : Word, Point w ∧ u.val.IsPrefix w := by
  obtain ⟨n,hn⟩ := u.property
  let w := (Sparse.code n).map toFin
  have hw : w.map toLetter = Sparse.code n := by
    simp [w,List.map_map,Function.comp_def]
  refine ⟨w,?_,?_⟩
  · change Sparse.InSparse (w.map toLetter)
    rw [hw]
    exact (Sparse.inSparse_iff_code _).mpr ⟨n,rfl⟩
  · have h := hn.map toFin
    simpa [w,List.map_map,Function.comp_def] using h

/-- Every range node is a prefix of an actual coding point of the same
range. -/
theorem range_node_has_point (X : CriticalMap) {v : Word} (hv : v ∈ copyRange X) :
    ∃ w : Word, Point w ∧ w ∈ copyRange X ∧ v.IsPrefix w := by
  obtain ⟨u,rfl⟩ := hv
  obtain ⟨w,hw,hpre⟩ := node_has_point u
  let s : Node := ⟨w,point_tree hw⟩
  refine ⟨X.map s,?_ ,⟨s,rfl⟩,?_⟩
  · rw [← total_agrees X s]
    exact maps_point X hw
  · simpa only [total_agrees X u,total_agrees X s] using
      DiaryRecovery.map_prefix (total X) hpre

/-- At a split level there are two distinct coding descendants of
the critical node. The retained height is therefore determined by
coding points alone, with no reference to arbitrary padding. -/
theorem split_has_fork {j : Nat} (hj : j % 3 ≠ 2) :
    ∃ s t : Word, Point s ∧ Point t ∧ FirstFork s t j := by
  have h0 : Tree (child (critical j) 0) := by
    rw [SparseNormalization.tree_children j _ (criticalNode j).property
      (critical_length j)]
    simp [hj]
  have h2 : Tree (child (critical j) 2) := by
    rw [SparseNormalization.tree_children j _ (criticalNode j).property
      (critical_length j)]
    simp [hj]
  obtain ⟨s,hs,hsp⟩ := node_has_point ⟨_,h0⟩
  obtain ⟨t,ht,htp⟩ := node_has_point ⟨_,h2⟩
  obtain ⟨u,hu⟩ := hsp
  obtain ⟨v,hv⟩ := htp
  refine ⟨s,t,hs,ht,?_⟩
  rw [← hu,← hv,← critical_length j]
  simpa only [child,List.append_assoc,List.singleton_append] using
    firstFork_of_split (critical j) u v 0 2 (by decide)

/-- Inclusion on the coding sets already implies inclusion of the
critical-copy ranges. This proves one direction of the identification
of the expanded-copy order without assuming its converse. -/
theorem le_of_coding_inclusion (X Y : CriticalMap)
    (h : ∀ w, Point w → w ∈ copyRange X → w ∈ copyRange Y) :
    copyRange X ⊆ copyRange Y := by
  have hlevels (j : Nat) : ∃ k, X.level j = Y.level k := by
    by_cases hj : j % 3 = 2
    · let u := criticalNode j
      have hp : Point u.val := (SparseNormalization.point_at_level (criticalNode_length j)).mpr
        ⟨hj,rfl⟩
      have hpoint : Point (X.map u) := by
        rw [← total_agrees X u]
        exact maps_point X hp
      exact mem_length_retained Y (h _ hpoint ⟨u,rfl⟩)
    · obtain ⟨s,t,hs,ht,hf⟩ := split_has_fork hj
      let u : Node := ⟨s,point_tree hs⟩
      let v : Node := ⟨t,point_tree ht⟩
      have hs' : Point (X.map u) := by rw [← total_agrees X u]; exact maps_point X hs
      have ht' : Point (X.map v) := by rw [← total_agrees X v]; exact maps_point X ht
      have hf' := DiaryRecovery.firstFork_map (total X) hf
      have hf'' : FirstFork (X.map u) (X.map v) (X.level j) := by
        simpa only [total_agrees X u,total_agrees X v,total_level] using hf'
      exact fork_length_retained Y (h _ hs' ⟨u,rfl⟩) (h _ ht' ⟨v,rfl⟩) hf''
  intro v hv
  obtain ⟨w,hw,hwX,hpre⟩ := range_node_has_point X hv
  obtain ⟨j,hj⟩ := mem_length_retained X hv
  obtain ⟨k,hk⟩ := hlevels j
  exact prefix_mem_of_retained Y hpre (h w hw hwX) ⟨k,hj.trans hk⟩

theorem le_iff_coding_inclusion (X Y : CriticalMap) :
    copyRange X ⊆ copyRange Y ↔
      ∀ w, Point w → w ∈ copyRange X → w ∈ copyRange Y :=
  ⟨fun h _ _ hw => h hw,le_of_coding_inclusion X Y⟩

end AllThoseBigRamsey.Pseudotree.CriticalCopies
