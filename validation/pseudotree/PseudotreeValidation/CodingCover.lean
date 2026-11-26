import PseudotreeValidation.CriticalSupport
import PseudotreeValidation.GeneralizedRecovery

/-! Finite witnesses for reconstructing the actual sparse tree from
labelled normalized coding sets. All levels of a prescribed initial
segment are witnessed by coding points or actual forks. -/
namespace AllThoseBigRamsey.Pseudotree.CriticalCopies
open RayEmbeddings
open SparseNormalization (Point critical critical_length point_tree tree_prefix point_at_level)
open DiaryRecovery (FirstFork firstFork_map firstFork_map_iff firstFork_unique map_take)
open DiaryNormalization (essential length_mem_essential fork_mem_essential ForkAt schedule rank schedule_rank schedule_strict)
open GeneralizedNormalization (selected essential_subset_selected rayMap code codes nodes)

structure CodingCover (C : Finset Word) (h : Nat) : Prop where
  points : ∀ w ∈ C, Point w
  nonempty : C.Nonempty
  descendant : ∀ u : Node, u.val.length < h → ∃ w ∈ C, u.val.IsPrefix w
  coding : ∀ j < h, j % 3 = 2 → critical j ∈ C
  fork : ∀ j < h, j % 3 ≠ 2 → ForkAt C j

namespace CodingCover

theorem mono {C D : Finset Word} {h : Nat} (P : CodingCover C h)
    (hCD : C ⊆ D) (hD : ∀ w ∈ D, Point w) : CodingCover D h where
  points := hD
  nonempty := P.nonempty.mono hCD
  descendant := by
    intro u hu
    obtain ⟨w,hw,hpre⟩ := P.descendant u hu
    exact ⟨w,hCD hw,hpre⟩
  coding := fun j hj hm => hCD (P.coding j hj hm)
  fork := by
    intro j hj hm
    obtain ⟨s,hs,t,ht,hf⟩ := P.fork j hj hm
    exact ⟨s,hCD hs,t,hCD ht,hf⟩

theorem lower {C : Finset Word} {h k : Nat} (P : CodingCover C h) (hk : k ≤ h) :
    CodingCover C k where
  points := P.points
  nonempty := P.nonempty
  descendant := fun u hu => P.descendant u (hu.trans_le hk)
  coding := fun j hj => P.coding j (hj.trans_le hk)
  fork := fun j hj => P.fork j (hj.trans_le hk)

/-- Witness every level using finitely many actual coding descendants.
Coding nodes already in the prescribed block are included themselves. -/
theorem exists_cover (h : Nat) : ∃ C : Finset Word, CodingCover C h := by
  classical
  letI : Fintype (Prefix (h+1)) := Fintype.ofFinite _
  have hex (u : Prefix (h+1)) :
      ∃ w : Word, Point w ∧ u.val.val.IsPrefix w ∧ (Point u.val.val → w = u.val.val) := by
    by_cases hp : Point u.val.val
    · exact ⟨u.val.val,hp,List.prefix_rfl,fun _ => rfl⟩
    · obtain ⟨w,hw,hpre⟩ := node_has_point u.val
      exact ⟨w,hw,hpre,fun hh => False.elim (hp hh)⟩
  choose W hW hp hself using hex
  let C : Finset Word := Finset.univ.image W
  have hmem (u : Prefix (h+1)) : W u ∈ C :=
    Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩
  have desc (u : Node) (hu : u.val.length < 3*(h+1)) :
      ∃ w ∈ C, u.val.IsPrefix w := ⟨W ⟨u,hu⟩,hmem _,hp _⟩
  refine ⟨C,?_,?_,?_,?_,?_⟩
  · intro w hw
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hw
    exact hW u
  · exact ⟨_,hmem ⟨criticalNode 0,by simp⟩⟩
  · intro u hu
    exact desc u (by omega)
  · intro j hj hm
    let u : Prefix (h+1) := ⟨criticalNode j,by simp; omega⟩
    have hpoint : Point u.val.val := (point_at_level (criticalNode_length j)).mpr ⟨hm,rfl⟩
    have he := hself u hpoint
    exact he ▸ hmem u
  · intro j hj hm
    have hc : SparseNormalization.Tree (critical j) := (criticalNode j).property
    have h0 : SparseNormalization.Tree (critical j ++ [0]) := by
      change SparseNormalization.Tree (child (critical j) 0)
      rw [SparseNormalization.tree_children j (critical j) hc (critical_length j)]
      simp [hm]
    have h2 : SparseNormalization.Tree (critical j ++ [2]) := by
      change SparseNormalization.Tree (child (critical j) 2)
      rw [SparseNormalization.tree_children j (critical j) hc (critical_length j)]
      simp [hm]
    obtain ⟨s,hs,hsp⟩ := desc ⟨_,h0⟩ (by simp; omega)
    obtain ⟨t,ht,htp⟩ := desc ⟨_,h2⟩ (by simp; omega)
    obtain ⟨u,hu⟩ := hsp
    obtain ⟨v,hv⟩ := htp
    change (critical j ++ [0]) ++ u = s at hu
    change (critical j ++ [2]) ++ v = t at hv
    have hf : FirstFork s t j := by
      rw [← hu,← hv]
      simpa only [List.append_assoc,List.singleton_append,critical_length] using
        DiaryRecovery.firstFork_of_split (critical j) u v 0 2 (by decide)
    exact ⟨s,hs,t,ht,hf⟩

theorem essential_mem {C : Finset Word} {h : Nat} (P : CodingCover C h)
    {j : Nat} (hj : j < h) : j ∈ essential C := by
  by_cases hm : j % 3 = 2
  · simpa only [critical_length] using length_mem_essential (P.coding j hj hm)
  · exact fork_mem_essential (P.fork j hj hm)

theorem selected_mem {C : Finset Word} {h : Nat} (P : CodingCover C h)
    {j : Nat} (hj : j < h) : j ∈ selected C :=
  essential_subset_selected C (P.essential_mem hj)

/-- A strictly increasing enumeration of a finite set containing an
initial segment cannot skip any of those initial indices. -/
theorem schedule_initial {L : Finset Nat} (hne : L.Nonempty) {h : Nat}
    (hmem : ∀ j < h, j ∈ L) {j : Nat} (hj : j < h) : schedule L j = j := by
  have hstrict := schedule_strict hne
  have hge (i : Nat) : i ≤ schedule L i := by
    induction i with
    | zero => omega
    | succ i ih =>
      have ht := hstrict (Nat.lt_succ_self i)
      omega
  have hr (i : Nat) (hi : i < h) : rank L i ≤ i := by
    have hh := hge (rank L i)
    rw [schedule_rank (hmem i hi)] at hh
    exact hh
  induction j with
  | zero =>
    have he : rank L 0 = 0 := by have := hr 0 hj; omega
    have hk := schedule_rank (hmem 0 hj)
    rwa [he] at hk
  | succ j ih =>
    have hprev := ih (by omega)
    have ht : j < rank L (j+1) := by
      apply hstrict.lt_iff_lt.mp
      rw [hprev,schedule_rank (hmem (j+1) hj)]
      omega
    have he : rank L (j+1) = j+1 := by have := hr (j+1) hj; omega
    have hh := schedule_rank (hmem (j+1) hj)
    rwa [he] at hh

theorem schedule_eq {C : Finset Word} {h : Nat} (P : CodingCover C h)
    {j : Nat} (hj : j < h) : schedule (selected C) j = j :=
  schedule_initial (GeneralizedNormalization.selected_nonempty P.nonempty)
    (fun _ hi => P.selected_mem hi) hj

theorem index_lt_card {C : Finset Word} {h : Nat} (P : CodingCover C h)
    {j : Nat} (hj : j < h) : j < (selected C).card := by
  have hr := schedule_rank (P.selected_mem hj)
  have he : rank (selected C) j = j :=
    (schedule_strict (GeneralizedNormalization.selected_nonempty P.nonempty)).injective
      (hr.trans (P.schedule_eq hj).symm)
  simpa only [he] using DiaryNormalization.rank_lt (P.selected_mem hj)

theorem rayMap_level {C : Finset Word} (hne : C.Nonempty) (j : Nat) :
    (rayMap hne).level j = schedule (selected C) j := rfl

theorem project_initial {C : Finset Word} {h : Nat} (P : CodingCover C h)
    {w : Word} {j : Nat} (hj : j < h) (hw : j ≤ w.length) :
    LevelProjection.project (schedule (selected C)) w j = w.take j := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hw]
  · intro i hi hi'
    have hij : i < j := by simpa only [LevelProjection.project_length] using hi
    have hiw : i < w.length := hij.trans_le hw
    rw [LevelProjection.project_get _ _ hij,P.schedule_eq (hij.trans hj)]
    simp only [List.getElem?_eq_getElem hiw,Option.getD_some,List.getElem_take]

/-- The code of any witnessed descendant has exactly the original
prefix up to every covered level. -/
theorem code_take {C : Finset Word} {h : Nat} (P : CodingCover C h)
    {w : Word} (hw : w ∈ C) {j : Nat} (hj : j < h) (hwl : j ≤ w.length) :
    (code C w).take j = w.take j := by
  have hl := congrArg List.length (GeneralizedNormalization.rayMap_code P.nonempty hw)
  rw [(rayMap P.nonempty).length_map,rayMap_level] at hl
  have hle : j ≤ (code C w).length := by
    apply (schedule_strict (GeneralizedNormalization.selected_nonempty P.nonempty)).le_iff_le.mp
    rw [P.schedule_eq hj,hl]
    exact hwl
  have hle' : j ≤ rank (selected C) w.length := by
    simpa only [code,LevelProjection.project_length] using hle
  rw [code,LevelProjection.project_take _ _ hle',P.project_initial hj hwl]

theorem code_eq {C : Finset Word} {h : Nat} (P : CodingCover C h)
    {w : Word} (hw : w ∈ C) (hl : w.length < h) : code C w = w := by
  have hr := schedule_rank (P.selected_mem hl)
  have he : rank (selected C) w.length = w.length :=
    (schedule_strict (GeneralizedNormalization.selected_nonempty P.nonempty)).injective
      (hr.trans (P.schedule_eq hl).symm)
  unfold code
  rw [he,P.project_initial hl le_rfl,List.take_length]

end CodingCover
end AllThoseBigRamsey.Pseudotree.CriticalCopies
