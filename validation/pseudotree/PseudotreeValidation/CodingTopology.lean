import PseudotreeValidation.CodingIdentification

/-! Reverse finite-coordinate control for the coding-range topology.
The coding points are indexed by their actual increasing lengths.
A finite initial segment of the range recovers each of the finitely
many coding witnesses needed for a whole-block approximation. -/
namespace AllThoseBigRamsey.Pseudotree.CriticalCopies
open RayEmbeddings
open SparseNormalization (Point critical critical_length point_tree point_at_level point_unique_length)
open DiaryRecovery (firstFork_map firstFork_unique map_take)

def pointIndex (i : Nat) : Word := critical (3*i+2)

theorem pointIndex_point (i : Nat) : Point (pointIndex i) :=
  (point_at_level (critical_length (3*i+2))).mpr ⟨by omega,rfl⟩

theorem pointIndex_surj {w : Word} (hw : Point w) : ∃ i, pointIndex i = w := by
  obtain ⟨hm,he⟩ := (point_at_level rfl).mp hw
  refine ⟨w.length/3,?_⟩
  unfold pointIndex
  rw [show 3*(w.length/3)+2 = w.length by omega]
  exact he.symm

def pointImage (X : CriticalMap) (i : Nat) : Word :=
  X.map (criticalNode (3*i+2))

theorem pointImage_point (X : CriticalMap) (i : Nat) : Point (pointImage X i) := by
  change Point (X.map (criticalNode (3*i+2)))
  rw [← total_agrees X (criticalNode (3*i+2))]
  exact maps_point X (pointIndex_point i)

def imageHeight (X : CriticalMap) (i : Nat) : Nat := (pointImage X i).length

theorem imageHeight_strict (X : CriticalMap) : StrictMono (imageHeight X) := by
  intro i j hij
  exact X.level_strict (show 3*i+2 < 3*j+2 by omega)

theorem pointImage_mem (X : CriticalMap) (i : Nat) : pointImage X i ∈ codingRange X :=
  ⟨pointImage_point X i,⟨criticalNode (3*i+2),rfl⟩⟩

theorem mem_codingRange_index (X : CriticalMap) {w : Word} (hw : w ∈ codingRange X) :
    ∃ i, pointImage X i = w := by
  obtain ⟨v,hv,he⟩ := (mem_codingRange_iff X w).mp hw
  obtain ⟨i,hi⟩ := pointIndex_surj hv
  have hnode : criticalNode (3*i+2) = (⟨v,point_tree hv⟩ : Node) := Subtype.ext hi
  exact ⟨i,(congrArg X.map hnode).trans he⟩

/-- Strictly increasing natural sequences with the same range below
f(K) agree at every index at most K. No arbitrary enumeration of a
countable set is used. -/
theorem increasing_initial_eq (f g : Nat → Nat) (hf : StrictMono f) (hg : StrictMono g)
    (K : Nat)
    (h : ∀ l ≤ f K, (∃ i, f i = l) ↔ ∃ i, g i = l) :
    ∀ j ≤ K, f j = g j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    obtain ⟨i,hi⟩ := (h (f j) (hf.monotone hj)).mp ⟨j,rfl⟩
    have hji : j ≤ i := by
      by_contra hn
      have hlt : i < j := by omega
      have he := ih i hlt (hlt.le.trans hj)
      exact (ne_of_lt (hf hlt)) (he.trans hi)
    have hg_le : g j ≤ f j := (hg.monotone hji).trans_eq hi
    obtain ⟨i',hi'⟩ := (h (g j) (hg_le.trans (hf.monotone hj))).mpr ⟨j,rfl⟩
    have hji' : j ≤ i' := by
      by_contra hn
      have hlt : i' < j := by omega
      have he := ih i' hlt (hlt.le.trans hj)
      exact (ne_of_lt (hg hlt)) (he.symm.trans hi')
    exact le_antisymm ((hf.monotone hji').trans_eq hi') hg_le

theorem pointImages_agree {X Y : CriticalMap} (K : Nat)
    (h : ∀ w : Word, w.length ≤ imageHeight X K →
      (w ∈ codingRange X ↔ w ∈ codingRange Y)) :
    ∀ i ≤ K, pointImage X i = pointImage Y i := by
  have hh (l : Nat) (hl : l ≤ imageHeight X K) :
      (∃ i, imageHeight X i = l) ↔ ∃ i, imageHeight Y i = l := by
    constructor
    · rintro ⟨i,hi⟩
      have hm := (h (pointImage X i) (by change imageHeight X i ≤ _; omega)).mp
        (pointImage_mem X i)
      obtain ⟨j,hj⟩ := mem_codingRange_index Y hm
      exact ⟨j,(congrArg List.length hj).trans hi⟩
    · rintro ⟨i,hi⟩
      have hm := (h (pointImage Y i) (by change imageHeight Y i ≤ _; omega)).mpr
        (pointImage_mem Y i)
      obtain ⟨j,hj⟩ := mem_codingRange_index X hm
      exact ⟨j,(congrArg List.length hj).trans hi⟩
  have hlen := increasing_initial_eq (imageHeight X) (imageHeight Y)
    (imageHeight_strict X) (imageHeight_strict Y) K hh
  intro i hi
  exact point_unique_length (pointImage_point X i) (pointImage_point Y i) (hlen i hi)

/-- The finite witnesses determine the values on their entire covered
prefix, also for critical maps not obtained by our reconstruction. -/
theorem agrees_cover {X Y : CriticalMap} {C : Finset Word} {h : Nat}
    (P : CodingCover C h)
    (he : ∀ w ∈ C, (total X).map w = (total Y).map w) (u : Node) (hu : u.val.length < h) :
    X.map u = Y.map u := by
  have hl (j : Nat) (hj : j < h) : X.level j = Y.level j := by
    by_cases hm : j % 3 = 2
    · have h := congrArg List.length (he (critical j) (P.coding j hj hm))
      simpa only [RayStrongMap.length_map,total_level,critical_length] using h
    · obtain ⟨s,hs,t,ht,hf⟩ := P.fork j hj hm
      have hx := firstFork_map (total X) hf
      rw [he s hs,he t ht] at hx
      exact firstFork_unique hx (firstFork_map (total Y) hf)
  obtain ⟨w,hw,hp⟩ := P.descendant u hu
  have hX := map_take (total X) w u.val.length hp.length_le
  have hY := map_take (total Y) w u.val.length hp.length_le
  have hpre := List.prefix_iff_eq_take.mp hp
  rw [← hpre,total_agrees X u,total_level,he w hw,hl _ hu] at hX
  rw [← hpre,total_agrees Y u,total_level] at hY
  exact hX.trans hY.symm

theorem codingRange_injective : Function.Injective codingRange := by
  intro X Y h
  apply eq_of_agrees_points X Y
  intro w hw
  obtain ⟨i,hi⟩ := pointIndex_surj hw
  have he := pointImages_agree (X:=X) (Y:=Y) i (fun v _ => by rw [h]) i le_rfl
  have hnode : criticalNode (3*i+2) = (⟨w,point_tree hw⟩ : Node) := Subtype.ext hi
  change X.map (criticalNode (3*i+2)) = Y.map (criticalNode (3*i+2)) at he
  rwa [hnode] at he

/-- Reverse continuity at a fixed critical copy: agreement of its
coding range with another copy on one finite length-bounded cylinder
forces agreement of their entire n-th approximations. -/
theorem finite_cylinder_recovers_approx (X : CriticalMap) (n : Nat) :
    ∃ L : Nat, ∀ Y : CriticalMap,
      (∀ w : Word, w.length ≤ L → (w ∈ codingRange X ↔ w ∈ codingRange Y)) →
      approx n X = approx n Y := by
  obtain ⟨C,P⟩ := CodingCover.exists_cover (3*n)
  let K := C.sup List.length
  refine ⟨imageHeight X K,?_⟩
  intro Y hY
  have he := pointImages_agree K hY
  apply approx_eq_iff.mpr
  intro u
  apply agrees_cover P _ u.val u.property
  intro w hw
  have hp := P.points w hw
  obtain ⟨i,hi⟩ := pointIndex_surj hp
  have hl : w.length ≤ K := Finset.le_sup hw
  have hl' := congrArg List.length hi
  change (critical (3*i+2)).length = w.length at hl'
  rw [critical_length] at hl'
  have hiK : i ≤ K := by omega
  have hnode : criticalNode (3*i+2) = (⟨w,point_tree hp⟩ : Node) := Subtype.ext hi
  have heq := he i hiK
  change X.map (criticalNode (3*i+2)) = Y.map (criticalNode (3*i+2)) at heq
  rw [hnode] at heq
  rw [total_agrees X (⟨w,point_tree hp⟩ : Node),total_agrees Y (⟨w,point_tree hp⟩ : Node)]
  exact heq

end AllThoseBigRamsey.Pseudotree.CriticalCopies
