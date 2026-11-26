import PseudotreeValidation.ExpandedCoding

/-! Uniqueness, order identification, and the finite-coordinate
continuity estimates for the actual coding-range representation.
The topology statements are presented here as their explicit finite
cylinder conditions, independently of a topology API. -/
namespace AllThoseBigRamsey.Pseudotree.CriticalCopies
open RayEmbeddings
open SparseNormalization (Point critical critical_length point_tree point_at_level)
open DiaryRecovery (firstFork_map firstFork_unique map_take)

theorem level_ge (X : CriticalMap) (j : Nat) : j ≤ X.level j := by
  induction j with
  | zero => omega
  | succ j ih =>
    have h : X.level j < X.level (j+1) := X.level_strict (Nat.lt_succ_self j)
    omega

theorem point_reflect (X : CriticalMap) (u : Node) (hp : Point (X.map u)) :
    Point u.val := by
  obtain ⟨hm,hc⟩ := (point_at_level rfl).mp hp
  have hlen := X.length_map u
  have hu : u = criticalNode u.val.length := by
    apply map_injective X
    rw [hc,hlen]
    exact (X.critical_image _).symm
  have hm' := (X.phase u.val.length).mp (hlen ▸ hm)
  exact (point_at_level rfl).mpr ⟨hm',congrArg Subtype.val hu⟩

/-- Values on the coding points determine every critical-map value:
a code or a witnessed fork fixes the level, and a coding descendant
fixes the prefix at that level. -/
theorem eq_of_agrees_points (X Y : CriticalMap)
    (he : ∀ w (hw : Point w), X.map ⟨w,point_tree hw⟩ = Y.map ⟨w,point_tree hw⟩) :
    X = Y := by
  have hl (j : Nat) : X.level j = Y.level j := by
    by_cases hm : j % 3 = 2
    · have hp : Point (critical j) := (point_at_level (critical_length j)).mpr ⟨hm,rfl⟩
      exact congrArg List.length (he _ hp)
    · obtain ⟨s,t,hs,ht,hf⟩ := split_has_fork hm
      let u : Node := ⟨s,point_tree hs⟩
      let v : Node := ⟨t,point_tree ht⟩
      have hx := firstFork_map (total X) hf
      have hy := firstFork_map (total Y) hf
      change DiaryRecovery.FirstFork ((total X).map u.val) ((total X).map v.val) (X.level j) at hx
      change DiaryRecovery.FirstFork ((total Y).map u.val) ((total Y).map v.val) (Y.level j) at hy
      rw [total_agrees X u,total_agrees X v,he s hs,he t ht] at hx
      rw [total_agrees Y u,total_agrees Y v] at hy
      exact firstFork_unique hx hy
  apply CriticalMap.ext
  funext u
  obtain ⟨w,hw,hpre⟩ := node_has_point u
  let v : Node := ⟨w,point_tree hw⟩
  have hp : u.val = v.val.take u.val.length := List.prefix_iff_eq_take.mp hpre
  have hX := map_take (total X) v.val u.val.length hpre.length_le
  have hY := map_take (total Y) v.val u.val.length hpre.length_le
  rw [← hp,total_agrees X u,total_agrees X v,total_level] at hX
  rw [← hp,total_agrees Y u,total_agrees Y v,total_level] at hY
  exact hX.trans ((congrArg₂ List.take (hl u.val.length) (he w hw)).trans hY.symm)

/-- A labelled coding-map embedding extends uniquely. -/
theorem PreservesCoding.unique_extension {f : Word → Word} (H : PreservesCoding f) :
    ∃! X : CriticalMap, ∀ w (hw : Point w), X.map ⟨w,point_tree hw⟩ = f w := by
  obtain ⟨X,hX⟩ := H.extends_critical
  exact ⟨X,hX,fun Y hY => eq_of_agrees_points Y X (fun w hw => (hY w hw).trans (hX w hw).symm)⟩

def codingRange (X : CriticalMap) : Set Word := {w | Point w ∧ w ∈ copyRange X}

theorem mem_codingRange_iff (X : CriticalMap) (w : Word) :
    w ∈ codingRange X ↔ ∃ v (hv : Point v), X.map ⟨v,point_tree hv⟩ = w := by
  constructor
  · rintro ⟨hp,⟨u,rfl⟩⟩
    exact ⟨u.val,point_reflect X u hp,rfl⟩
  · rintro ⟨v,hv,rfl⟩
    refine ⟨?_,⟨⟨v,point_tree hv⟩,rfl⟩⟩
    rw [← total_agrees X (⟨v,point_tree hv⟩ : Node)]
    exact maps_point X hv

theorem codingRange_le_iff (X Y : CriticalMap) :
    codingRange X ⊆ codingRange Y ↔ copyRange X ⊆ copyRange Y := by
  constructor
  · intro h
    exact le_of_coding_inclusion X Y (fun w hp hw => (h ⟨hp,hw⟩).2)
  · intro h w hw
    exact ⟨hw.1,h hw.2⟩

/-- Coding-map images and critical-copy coding ranges coincide. -/
theorem codingRange_characterization (A : Set Word) :
    (∃ X : CriticalMap, codingRange X = A) ↔
      ∃ f : Word → Word, PreservesCoding f ∧ A = f '' {w | Point w} := by
  constructor
  · rintro ⟨X,rfl⟩
    refine ⟨(total X).map,critical_preservesCoding X,?_⟩
    ext w
    rw [mem_codingRange_iff]
    constructor
    · rintro ⟨v,hv,h⟩
      exact ⟨v,hv,(total_agrees X ⟨v,point_tree hv⟩).trans h⟩
    · rintro ⟨v,hv,h⟩
      exact ⟨v,hv,(total_agrees X ⟨v,point_tree hv⟩).symm.trans h⟩
  · rintro ⟨f,H,rfl⟩
    obtain ⟨X,hX⟩ := H.extends_critical
    refine ⟨X,?_⟩
    ext w
    rw [mem_codingRange_iff]
    constructor
    · rintro ⟨v,hv,h⟩
      exact ⟨v,hv,(hX v hv).symm.trans h⟩
    · rintro ⟨v,hv,h⟩
      exact ⟨v,hv,(hX v hv).trans h⟩

/-- Forward continuity: an actual whole-block approximation beyond
the length of a given word decides its membership in the code range. -/
theorem codingRange_agrees_short {X Y : CriticalMap} {n : Nat}
    (ha : approx n X = approx n Y) {w : Word} (hw : w.length < 3*n) :
    w ∈ codingRange X ↔ w ∈ codingRange Y := by
  have aux (U V : CriticalMap) (hUV : approx n U = approx n V) :
      w ∈ codingRange U → w ∈ codingRange V := by
    rintro ⟨hp,⟨u,hu⟩⟩
    have hlen : u.val.length ≤ w.length := by
      have h := level_ge U u.val.length
      rw [level_eq_length U u,hu] at h
      exact h
    have he := approx_eq_iff.mp hUV ⟨u,hlen.trans_lt hw⟩
    exact ⟨hp,⟨u,he.symm.trans hu⟩⟩
  exact ⟨aux X Y ha,aux Y X ha.symm⟩

end AllThoseBigRamsey.Pseudotree.CriticalCopies
