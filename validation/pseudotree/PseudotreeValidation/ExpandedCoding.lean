import PseudotreeValidation.CodingCover

/-!
# Reconstruction of critical embeddings from labelled coding maps

A coding map preserves the labelled normalized diary of every finite
coding set. This is the relation-level formulation of an embedding in
the proposed expansion (before packaging the first-order language).
Finite witness sets reconstruct critical maps coherently. There is no
assumption that a coding map already extends to a ray map.
-/
namespace AllThoseBigRamsey.Pseudotree.CriticalCopies
open RayEmbeddings
open SparseNormalization (Point critical critical_length point_tree tree_prefix point_at_level)
open DiaryRecovery (FirstFork firstFork_map firstFork_map_iff firstFork_unique map_take)
open DiaryNormalization (essential ForkAt schedule schedule_strict)
open GeneralizedNormalization (selected rayMap code codes nodes)
open CodingCover (rayMap_level)

structure PreservesCoding (f : Word → Word) : Prop where
  points : ∀ w, Point w → Point (f w)
  labelled : ∀ (C : Finset Word), (∀ w ∈ C, Point w) →
    ∀ w ∈ C, code (C.image f) (f w) = code C w

namespace PreservesCoding

variable {f : Word → Word}

theorem image_points (H : PreservesCoding f) {C : Finset Word} (hC : ∀ w ∈ C, Point w) :
    ∀ w ∈ C.image f, Point w := by
  intro w hw
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
  exact H.points _ (hC _ hv)

theorem image_codes (H : PreservesCoding f) {C : Finset Word} (hC : ∀ w ∈ C, Point w) :
    codes (C.image f) = codes C := by
  classical
  unfold codes
  rw [Finset.image_image]
  apply Finset.image_congr
  intro w hw
  exact H.labelled C hC w hw

theorem image_nodes (H : PreservesCoding f) {C : Finset Word} (hC : ∀ w ∈ C, Point w) :
    nodes (C.image f) = nodes C := by
  unfold nodes
  rw [H.image_codes hC]

/-- The finite reconstructed strong map, defined on all words by the
existing inverse-normalization completion. -/
noncomputable def localMap {C : Finset Word} (hC : C.Nonempty) : RayStrongMap :=
  rayMap (hC.image f)

theorem local_code (H : PreservesCoding f) {C : Finset Word} {h : Nat} (P : CodingCover C h)
    {w : Word} (hw : w ∈ C) :
    (localMap (f:=f) P.nonempty).map (code C w) = f w := by
  rw [← H.labelled C P.points w hw]
  exact GeneralizedNormalization.rayMap_code (P.nonempty.image f) (Finset.mem_image.mpr ⟨w,hw,rfl⟩)

theorem local_prefix (H : PreservesCoding f) {C : Finset Word} {h : Nat} (P : CodingCover C h)
    (u : Node) (hu : u.val.length < h) {w : Word} (hw : w ∈ C)
    (hp : u.val.IsPrefix w) :
    (localMap (f:=f) P.nonempty).map u.val =
      (f w).take ((localMap (f:=f) P.nonempty).level u.val.length) := by
  let g := rayMap P.nonempty
  let v := code C w
  have hlen : u.val.length ≤ v.length := by
    have hs : g.level u.val.length = u.val.length := P.schedule_eq hu
    have hw' : g.map v = w := GeneralizedNormalization.rayMap_code P.nonempty hw
    have he : g.level v.length = w.length := by
      simpa only [g.length_map] using congrArg List.length hw'
    have hg : StrictMono g.level := fun _ _ h => g.level_strict h
    apply hg.le_iff_le.mp
    rw [hs,he]
    exact hp.length_le
  have he : v.take u.val.length = u.val :=
    (P.code_take hw hu hp.length_le).trans (List.prefix_iff_eq_take.mp hp).symm
  have ht := map_take (localMap (f:=f) P.nonempty) v u.val.length hlen
  rw [he,show (localMap (f:=f) P.nonempty).map v = f w from H.local_code P hw] at ht
  exact ht

theorem local_tree (H : PreservesCoding f) {C : Finset Word} {h : Nat} (P : CodingCover C h)
    (u : Node) (hu : u.val.length < h) :
    SparseNormalization.Tree ((localMap (f:=f) P.nonempty).map u.val) := by
  obtain ⟨w,hw,hpre⟩ := P.descendant u hu
  rw [H.local_prefix P u hu hw hpre]
  exact tree_prefix (point_tree (H.points w (P.points w hw))) (List.take_prefix _ _)

theorem local_coding (H : PreservesCoding f) {C : Finset Word} {h : Nat} (P : CodingCover C h)
    {w : Word} (hw : Point w) (hl : w.length < h) :
    (localMap (f:=f) P.nonempty).map w = f w := by
  obtain ⟨hm,he⟩ := (point_at_level rfl).mp hw
  have hmem : w ∈ C := he ▸ P.coding w.length hl hm
  have hc := H.local_code P hmem
  rwa [P.code_eq hmem hl] at hc

theorem source_fork {C : Finset Word} {h : Nat} (P : CodingCover C h)
    {s t : Word} (hs : s ∈ C) (ht : t ∈ C) {j : Nat}
    (hj : j < h) (hf : FirstFork s t j) :
    FirstFork (code C s) (code C t) j := by
  let g := rayMap P.nonempty
  have h : FirstFork (g.map (code C s)) (g.map (code C t)) j := by
    rw [show g.map (code C s) = s from GeneralizedNormalization.rayMap_code P.nonempty hs,
      show g.map (code C t) = t from GeneralizedNormalization.rayMap_code P.nonempty ht]
    exact hf
  obtain ⟨i,hi,he⟩ := (firstFork_map_iff g _ _ _).mp h
  have hg : StrictMono g.level := fun _ _ h => g.level_strict h
  have hlevel : g.level j = j := P.schedule_eq hj
  have hij : i = j := hg.injective (he.symm.trans hlevel.symm)
  exact hij ▸ hi

theorem local_fork (H : PreservesCoding f) {C : Finset Word} {h : Nat} (P : CodingCover C h)
    {s t : Word} (hs : s ∈ C) (ht : t ∈ C) {j : Nat}
    (hj : j < h) (hf : FirstFork s t j) :
    FirstFork (f s) (f t) ((localMap (f:=f) P.nonempty).level j) := by
  have hf' := firstFork_map (localMap (f:=f) P.nonempty)
    (source_fork P hs ht hj hf)
  rwa [H.local_code P hs,H.local_code P ht] at hf'

/-- Critical vertices in both finite normalizations are literally the
same, by uniqueness of the generalized local grammar. -/
theorem local_critical (H : PreservesCoding f) {C : Finset Word} {h : Nat} (P : CodingCover C h)
    {j : Nat} (hj : j < h) :
    (localMap (f:=f) P.nonempty).map (critical j) =
      critical ((localMap (f:=f) P.nonempty).level j) := by
  classical
  let D := C.image f
  have hD : D.Nonempty := P.nonempty.image f
  have hpD : ∀ w ∈ D, Point w := H.image_points P.points
  have hc := H.image_codes P.points
  have hn := H.image_nodes P.points
  have hjC := P.index_lt_card hj
  have hnormC : GeneralizedNormalization.normalizedCritical C j = critical j := by
    unfold GeneralizedNormalization.normalizedCritical
    rw [P.schedule_eq hj,P.project_initial (w := critical j) hj (by simp)]
    exact List.take_of_length_le (critical_length j).le
  have hnode := (GeneralizedNormalization.normalized_critical P.points P.nonempty hjC).1
  have hnodeD : GeneralizedNormalization.normalizedCritical C j ∈ nodes D := by
    rw [show nodes D = nodes C from hn]
    exact hnode
  have hjD : j < (selected D).card := by
    simpa only [GeneralizedNormalization.normalizedCritical_length] using
      GeneralizedNormalization.nodes_bounded hnodeD
  have L := GeneralizedNormalization.normalized_level P.points P.nonempty hjC
  have M := GeneralizedNormalization.normalized_level hpD hD hjD
  rw [show nodes D = nodes C from hn,show codes D = codes C from hc] at M
  have he := (GeneralizedLevel.unique L M).1
  have hcritD : critical j = GeneralizedNormalization.normalizedCritical D j :=
    hnormC.symm.trans he
  have hmem : critical j ∈ nodes D := by
    rw [← hnormC]
    exact hnodeD
  have hDom := (GeneralizedNormalization.mem_nodes_iff_domain hD).mp hmem
  change (rayMap hD).map (critical j) = critical (schedule (selected D) j)
  unfold GeneralizedNormalization.rayMap
  rw [PrefixRayMap.completion_agrees _ _ hDom]
  change LevelProjection.inverse (D : Set Word) (schedule (selected D)) (critical j) = _
  rw [hcritD]
  exact (GeneralizedNormalization.normalized_critical hpD hD hjD).2

theorem local_phase (H : PreservesCoding f) {C : Finset Word} {h : Nat} (P : CodingCover C h)
    {j : Nat} (hj : j < h) :
    (localMap (f:=f) P.nonempty).level j % 3 = 2 ↔ j % 3 = 2 := by
  by_cases hm : j % 3 = 2
  · have hp : Point (critical j) := (point_at_level (critical_length j)).mpr ⟨hm,rfl⟩
    have he := H.local_coding P hp (by simpa only [critical_length] using hj)
    have hpoint : Point ((localMap (f:=f) P.nonempty).map (critical j)) :=
      he.symm ▸ H.points _ hp
    have hl : ((localMap (f:=f) P.nonempty).map (critical j)).length =
        (localMap (f:=f) P.nonempty).level j := by rw [(localMap _).length_map,critical_length]
    have hphase := ((point_at_level hl).mp hpoint).1
    simp [hphase,hm]
  · obtain ⟨s,hs,t,ht,hf⟩ := P.fork j hj hm
    have hf' := H.local_fork P hs ht hj hf
    have hfork : ForkAt (C.image f) ((localMap (f:=f) P.nonempty).level j) :=
      ⟨f s,Finset.mem_image.mpr ⟨s,hs,rfl⟩,f t,Finset.mem_image.mpr ⟨t,ht,rfl⟩,hf'⟩
    have hphase := (SparseNormalization.fork_critical (H.image_points P.points) hfork).1
    simp [hphase,hm]

/-- On overlapping covered levels, reconstruction is independent of the
finite witness set. Coding heights are fixed by one point and split
heights by a witnessed first fork. -/
theorem local_levels_of_subset (H : PreservesCoding f) {C D : Finset Word} {h : Nat}
    (P : CodingCover C h) (Q : CodingCover D h) (hCD : C ⊆ D)
    {j : Nat} (hj : j < h) :
    (localMap (f:=f) P.nonempty).level j = (localMap (f:=f) Q.nonempty).level j := by
  by_cases hm : j % 3 = 2
  · have hp : Point (critical j) := (point_at_level (critical_length j)).mpr ⟨hm,rfl⟩
    have h1 := H.local_coding P hp (by simpa only [critical_length] using hj)
    have h2 := H.local_coding Q hp (by simpa only [critical_length] using hj)
    have he := congrArg List.length (h1.trans h2.symm)
    simpa only [RayStrongMap.length_map,critical_length] using he
  · obtain ⟨s,hs,t,ht,hf⟩ := P.fork j hj hm
    exact firstFork_unique (H.local_fork P hs ht hj hf)
      (H.local_fork Q (hCD hs) (hCD ht) hj hf)

theorem local_agrees_of_subset (H : PreservesCoding f) {C D : Finset Word} {h : Nat}
    (P : CodingCover C h) (Q : CodingCover D h) (hCD : C ⊆ D)
    (u : Node) (hu : u.val.length < h) :
    (localMap (f:=f) P.nonempty).map u.val = (localMap (f:=f) Q.nonempty).map u.val := by
  obtain ⟨w,hw,hpre⟩ := P.descendant u hu
  rw [H.local_prefix P u hu hw hpre,H.local_prefix Q u hu (hCD hw) hpre,
    H.local_levels_of_subset P Q hCD hu]

/-- No nested choice of witness sets is required: their union is a
common refinement, so the reconstructed maps agree wherever both
covers are defined. -/
theorem local_agrees (H : PreservesCoding f) {C D : Finset Word} {h k : Nat}
    (P : CodingCover C h) (Q : CodingCover D k)
    (u : Node) (hu : u.val.length < h) (hv : u.val.length < k) :
    (localMap (f:=f) P.nonempty).map u.val = (localMap (f:=f) Q.nonempty).map u.val := by
  classical
  let m := min h k
  have hm : u.val.length < m := by dsimp [m]; omega
  have hp := P.lower (min_le_left h k)
  have hq := Q.lower (min_le_right h k)
  have hU : ∀ w ∈ C ∪ D, Point w := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact P.points _ hw
    · exact Q.points _ hw
  have R : CodingCover (C ∪ D) m := hp.mono Finset.subset_union_left hU
  exact (H.local_agrees_of_subset hp R Finset.subset_union_left u hm).trans
    (H.local_agrees_of_subset hq R Finset.subset_union_right u hm).symm

/-- The main reconstruction theorem for the actual sparse coding set.
It requires only the explicit finite labelled relations, not
recurrence, A.3, A.4, or an assumed infinite extension. -/
theorem extends_critical (H : PreservesCoding f) : ∃ X : CriticalMap, ∀ w (hw : Point w),
    X.map ⟨w,point_tree hw⟩ = f w := by
  classical
  let C (j : Nat) := (CodingCover.exists_cover (j+1)).choose
  let P (j : Nat) : CodingCover (C j) (j+1) :=
    (CodingCover.exists_cover (j+1)).choose_spec
  let F (j : Nat) : RayStrongMap := localMap (f:=f) (P j).nonempty
  let M (u : Node) : Word := (F u.val.length).map u.val
  have agrees (j : Nat) (u : Node) (hu : u.val.length ≤ j) :
      M u = (F j).map u.val :=
    H.local_agrees (P u.val.length) (P j) u (by omega) (by omega)
  have hlength (u : Node) (j : Nat) (hu : u.val.length ≤ j) :
      (M u).length = (F j).level u.val.length := by
    rw [agrees j u hu,(F j).length_map]
  let X : CriticalMap := {
    map := M
    level_strict := by
      intro i j hij
      change (M (criticalNode i)).length < (M (criticalNode j)).length
      rw [hlength _ j (by simp; omega),hlength _ j (by simp),
        criticalNode_length,criticalNode_length]
      exact (F j).level_strict hij
    length_map := by
      intro u
      rw [hlength u u.val.length le_rfl,
        hlength (criticalNode u.val.length) u.val.length (by simp),criticalNode_length]
    step := by
      intro s a hs
      let u : Node := parentNode s a hs
      let v : Node := ⟨s++[a],hs⟩
      change ∃ p : Word, M v = M u ++ a :: p ∧ (a ≠ 1 → Binary p)
      rw [agrees v.val.length v le_rfl,agrees v.val.length u
        (by change s.length ≤ (s++[a]).length; simp)]
      exact (F v.val.length).step s a
    maps_tree := fun u => H.local_tree (P u.val.length) u (by omega)
    critical_image := by
      intro j
      rw [hlength _ j (by simp),criticalNode_length,agrees j _ (by simp)]
      exact H.local_critical (P j) (by omega)
    phase := by
      intro j
      rw [hlength _ j (by simp),criticalNode_length]
      exact H.local_phase (P j) (by omega) }
  refine ⟨X,?_⟩
  intro w hw
  change (F w.length).map w = f w
  exact H.local_coding (P w.length) hw (Nat.lt_succ_self _)

end PreservesCoding

/-- The converse direction follows from the already checked labelled
naturality and coding-point preservation. -/
theorem critical_preservesCoding (X : CriticalMap) :
    PreservesCoding (total X).map :=
  ⟨fun _ hw => maps_point X hw,fun C _ _ hw => preserves_labelled_diary X C hw⟩

/-- Every coding map preserving the labelled finite relations is the
restriction of a critical map, and every critical map has that property. -/
theorem preservesCoding_iff_extension (f : Word → Word) :
    PreservesCoding f ↔ ∃ X : CriticalMap, ∀ w (hw : Point w),
      (total X).map w = f w := by
  constructor
  · intro H
    obtain ⟨X,hX⟩ := H.extends_critical
    exact ⟨X,fun w hw => (total_agrees X ⟨w,point_tree hw⟩).trans (hX w hw)⟩
  · rintro ⟨X,hX⟩
    have H := critical_preservesCoding X
    constructor
    · intro w hw
      rw [← hX w hw]
      exact H.points w hw
    · intro C hC w hw
      have he : C.image f = C.image (total X).map := by
        apply Finset.image_congr
        intro v hv
        exact (hX v (hC v hv)).symm
      rw [he,← hX w (hC w hw)]
      exact H.labelled C hC w hw

end AllThoseBigRamsey.Pseudotree.CriticalCopies
