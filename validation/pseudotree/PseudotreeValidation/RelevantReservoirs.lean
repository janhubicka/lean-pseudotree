import PseudotreeValidation.RelativeReservoirRun
import PseudotreeValidation.CriticalAmalgamation

/-!
# Relative amalgamation in the critical-copy space

Assign the given critical reduct copy to the relevant boundary slots
and the ambient sparse copy to all other slots. The relative reservoir
construction preserves these assignments. Its prefix and fork witnesses
supply exactly RelativeSupport; the previously separated range argument
then gives the actual A.3(2) axiom.
-/

namespace AllThoseBigRamsey.Pseudotree.CriticalCopies
open RayEmbeddings RayMapModel LowerGeometry
open SparseNormalization (Point critical critical_length point_tree)
open Reservoir (Target BoundarySeeds StableAfter sparseSource)
open scoped FirstOrder

/-- The functional self-copy carried by a critical map. Its domain is
the full ternary model and its range is the image of the sparse code set. -/
noncomputable def targetCopy (X : CriticalMap) : Target :=
  (RayMapModel.embedding (total X)).comp SparseModel.selfEmbedding

def wordOf (z : TernaryModel) : Word := (fromBlocks z).map toFin

@[simp] theorem wordOf_model (w : Word) : wordOf (DiaryChains.model w) = w := by
  simp [wordOf,DiaryChains.model,List.map_map,Function.comp_def]

@[simp] theorem model_wordOf (z : TernaryModel) : DiaryChains.model (wordOf z) = z := by
  simp [wordOf,DiaryChains.model,List.map_map,Function.comp_def]

@[simp] theorem wordOf_letters (z : TernaryModel) :
    (wordOf z).map toLetter = fromBlocks z := by
  simp [wordOf,List.map_map,Function.comp_def]

theorem wordOf_point {z : TernaryModel} (hz : Sparse.InSparse (fromBlocks z)) :
    Point (wordOf z) := by
  change Sparse.InSparse ((wordOf z).map toLetter)
  rwa [wordOf_letters]

theorem targetCopy_mem (X : CriticalMap) {z : TernaryModel}
    (hz : z ∈ Set.range (targetCopy X)) :
    Point (wordOf z) ∧ wordOf z ∈ copyRange X := by
  obtain ⟨t,rfl⟩ := hz
  let y := SparseModel.selfEmbedding t
  have hy : Sparse.InSparse (fromBlocks y) := by
    have h : y ∈ Set.range SparseModel.selfEmbedding := ⟨t,rfl⟩
    rw [SparseModel.selfEmbedding_range] at h
    exact h
  let w := wordOf y
  have hp : Point w := wordOf_point hy
  have hmodel : RayMapModel.embedding (total X) y =
      DiaryChains.model ((total X).map w) := by
    rw [← model_wordOf y]
    change RayMapModel.embedding (total X) (toBlocks ((wordOf y).map toLetter)) =
      DiaryChains.model ((total X).map w)
    rw [RayMapModel.embedding_apply_word]
    simp [RayMapModel.act,DiaryChains.model,w,List.map_map,Function.comp_def]
  change Point (wordOf (RayMapModel.embedding (total X) y)) ∧
    wordOf (RayMapModel.embedding (total X) y) ∈ copyRange X
  rw [hmodel,wordOf_model]
  exact ⟨maps_point X hp,⟨⟨w,point_tree hp⟩,(total_agrees X ⟨w,point_tree hp⟩).symm⟩⟩

theorem targetCopy_sparse (X : CriticalMap) {z : TernaryModel}
    (hz : z ∈ Set.range (targetCopy X)) : Sparse.InSparse (fromBlocks z) := by
  have hp := (targetCopy_mem X hz).1
  change Sparse.InSparse ((wordOf z).map toLetter) at hp
  simpa only [wordOf_letters] using hp

noncomputable def assigned (X : CriticalMap) (n : Nat) (w : Word) : Target := by
  classical
  exact if Relevant X n w then targetCopy X else SparseModel.selfEmbedding

theorem assigned_sparse (X : CriticalMap) (n : Nat) :
    Reservoir.SparseTargets (assigned X n) := by
  classical
  intro w z hz
  by_cases hw : Relevant X n w
  · rw [assigned,if_pos hw] at hz
    exact targetCopy_sparse X hz
  · rw [assigned,if_neg hw,SparseModel.selfEmbedding_range] at hz
    exact hz

theorem assigned_stable (X : CriticalMap) {n d : Nat} (hd : 0 < d)
    (htop : X.level (3*n-1) = 3*d-1) :
    StableAfter (assigned X n) (3*d) := by
  classical
  intro j hj u a _
  have hu : 3*d ≤ u.val.length := u.property.2.symm ▸ hj
  have he := relevant_append_iff hd htop hu a
  by_cases hr : Relevant X n u.val
  · have hr' : Relevant X n (u.val ++ [a]) := he.mpr hr
    simp only [assigned,child,if_pos hr,if_pos hr']
  · have hr' : ¬Relevant X n (u.val ++ [a]) := fun h => hr (he.mp h)
    simp only [assigned,child,if_neg hr,if_neg hr']

theorem slot_identity {j : Nat} (w : Boundary j) :
    slot (restrictCritical identity (j+1)) w = w.val :=
  Reservoir.child_parent w

/-- The rational slot lemma in the Fin 3 alphabet. -/
theorem live_ray (d : Nat) (w : Word) (hw : SparseNormalization.Tree w)
    (hlen : w.length = 3*d) :
    ∃ Q : RayCopy, (∀ q, Sparse.InSparse (fromBlocks (Q q))) ∧
      ∀ q, ∃ b : Word, Binary b ∧ fromBlocks (Q q) = (w ++ b).map toLetter := by
  obtain ⟨Q,hQ,htail⟩ := Sparse.FIFO.slot_rayCopy d (w.map toLetter) hw
    (by simpa using hlen)
  refine ⟨Q,hQ,?_⟩
  intro q
  obtain ⟨b,hb,he⟩ := htail q
  refine ⟨b.map toFin,(binary_map b).mpr (fun a ha h => hb (h ▸ ha)),?_⟩
  simpa [List.map_append,List.map_map,Function.comp_def] using he

/-- Build the relative reservoir seed in a relevant slot from the
corresponding source slot of X. A binary entering edge remains binary
even through the gap to X's next selected level. -/
theorem relevant_seed (X : CriticalMap) {n d j : Nat} (hn : 0 < n)
    (hd : 0 < d) (hj : j+1 = 3*d)
    (htop : X.level (3*n-1) = 3*d-1)
    (w : Boundary j) (hw : Relevant X n w.val) :
    ∃ Q : RayCopy, Set.range Q.embedding ⊆ Set.range (targetCopy X) ∧
      ∀ q, ∃ b : Sparse.Word, fromBlocks (Q q) = w.val.map toLetter ++ b ∧
        (Reservoir.last w ≠ 1 → .one ∉ b) := by
  obtain ⟨u,hu,a,ha,hpre⟩ := hw
  have hlen : (X.map u).length = j := by
    rw [← level_eq_length X u,hu,htop]
    omega
  have heq : X.map u ++ [a] = w.val :=
    hpre.eq_of_length (by rw [List.length_append,List.length_singleton,hlen,w.property.2])
  have hlast : Reservoir.last w = a := by
    have hword := Reservoir.child_parent w
    have hh := congrArg List.getLast? (hword.trans heq.symm)
    simpa only [child,List.getLast?_concat,Option.some.injEq] using hh
  obtain ⟨Q,hQ,hQtail⟩ := live_ray n (u.val ++ [a]) ha
    (by rw [List.length_append,List.length_singleton,hu]; omega)
  obtain ⟨R,hR,hRtail⟩ := Q.mapped_slot (total X) (u.val ++ [a]) hQtail
  obtain ⟨pad,hpad,hpbin⟩ := X.step u.val a ha
  have hpar : parentNode u.val a ha = u := Subtype.ext rfl
  rw [hpar] at hpad
  have hstep : (total X).map (u.val ++ [a]) = w.val ++ pad := by
    rw [show (total X).map (u.val ++ [a]) = X.map ⟨u.val ++ [a],ha⟩
      from total_agrees X ⟨u.val ++ [a],ha⟩,hpad]
    change X.map u ++ a :: pad = w.val ++ pad
    rw [← heq]
    simp only [List.append_assoc,List.singleton_append]
  refine ⟨R,?_,?_⟩
  · rintro z ⟨q,rfl⟩
    have hmem : Q q ∈ Set.range SparseModel.selfEmbedding := by
      rw [SparseModel.selfEmbedding_range]
      exact hQ q
    obtain ⟨t,ht⟩ := hmem
    refine ⟨t,?_⟩
    change RayMapModel.embedding (total X) (SparseModel.selfEmbedding t) = R q
    rw [ht,hR]
  · intro q
    obtain ⟨b,hb,he⟩ := hRtail q
    refine ⟨(pad++b).map toLetter,?_,?_⟩
    · rw [he,hstep,List.append_assoc,List.map_append]
    · intro hn
      have hb' : Binary (pad++b) :=
        (binary_append _ _).mpr ⟨hpbin (hlast ▸ hn),hb⟩
      exact fun hm => ((noOne_map _).mpr hb') _ hm rfl

/-- All live boundary slots have the required seeds. No selection of a
single common reduct copy is needed. -/
theorem assigned_seeds (X : CriticalMap) {n d j : Nat} (hn : 0 < n)
    (hd : 0 < d) (hj : j+1 = 3*d)
    (htop : X.level (3*n-1) = 3*d-1) :
    Nonempty (BoundarySeeds (restrictCritical identity (j+1)) (assigned X n)) := by
  classical
  have hchoice (w : Boundary j) :
      ∃ Q : RayCopy, Set.range Q.embedding ⊆ Set.range (assigned X n w.val) ∧
        ∀ q, ∃ b : Sparse.Word, fromBlocks (Q q) =
          (slot (restrictCritical identity (j+1)) w).map toLetter ++ b ∧
          (Reservoir.last w ≠ 1 → .one ∉ b) := by
    by_cases hw : Relevant X n w.val
    · rw [assigned,if_pos hw,slot_identity]
      exact relevant_seed X hn hd hj htop w hw
    · rw [assigned,if_neg hw,slot_identity]
      obtain ⟨Q,hQ,hQtail⟩ := Sparse.FIFO.slot_rayCopy d (w.val.map toLetter)
        w.property.1 (by rw [List.length_map,w.property.2,hj])
      refine ⟨Q,?_,?_⟩
      · rintro z ⟨q,rfl⟩
        rw [SparseModel.selfEmbedding_range]
        exact hQ q
      · intro q
        obtain ⟨b,hb,he⟩ := hQtail q
        exact ⟨b,he,fun _ => hb⟩
  choose Q hQ htail using hchoice
  exact ⟨⟨Q,hQ,htail⟩⟩

/-- The actual relative support construction. The critical vertex
supplies a selected target height (a coding height or a genuine fork).
Every relevant node at that height has a prefix witness in the target. -/
theorem relative_support_construction : RelativeSupportConstruction := by
  classical
  intro X n d hn hd htop
  let j := 3*d-1
  have hj : j+1 = 3*d := by dsimp [j]; omega
  let e := restrictCritical identity (j+1)
  have hstable : StableAfter (assigned X n) (j+1) := by
    rw [hj]
    exact assigned_stable X hd htop
  obtain ⟨Q⟩ := assigned_seeds X hn hd hj htop
  obtain ⟨Z,hZ,hprefix,hcode,hfork⟩ :=
    Reservoir.relative_reservoir e (assigned X n) (assigned_sparse X n) hstable Q
  refine ⟨Z,?_,?_⟩
  · intro u hu
    exact hZ u (by omega)
  · intro u hu hr hc
    have hu' : j+1 ≤ u.val.length := by omega
    obtain ⟨z,hz,hpre⟩ := hprefix u hu'
    rw [assigned,if_pos hr] at hz
    have hzmem := (targetCopy_mem X hz).2
    have hpre' : (Z.map u).IsPrefix (wordOf z) := by
      have hh := hpre.map toFin
      simpa [wordOf,List.map_map,Function.comp_def] using hh
    let i := u.val.length
    let v := criticalNode i
    have hv : j+1 ≤ v.val.length := by simpa [v,i] using hu'
    have hcritical_mem : Z.map v ∈ copyRange X := by
      by_cases hm : i % 3 = 2
      · have hp : Point v.val :=
          (SparseNormalization.point_at_level (criticalNode_length i)).mpr ⟨hm,rfl⟩
        have h := hcode v hv hp
        change DiaryChains.model (Z.map v) ∈ Set.range (assigned X n (critical i)) at h
        rw [assigned,if_pos hc] at h
        simpa only [wordOf_model] using (targetCopy_mem X h).2
      · obtain ⟨y,hy,z',hz',h0,h2⟩ := hfork i (by simpa [i] using hu') hm
        rw [assigned,if_pos hc] at hy hz'
        have h0' : (Z.map v ++ [0]).IsPrefix (wordOf y) := by
          simpa [v,wordOf,List.map_append,List.map_map,Function.comp_def] using h0.map toFin
        have h2' : (Z.map v ++ [2]).IsPrefix (wordOf z') := by
          simpa [v,wordOf,List.map_append,List.map_map,Function.comp_def] using h2.map toFin
        exact fork_prefix_mem X (targetCopy_mem X hy).2 (targetCopy_mem X hz').2
          h0' h2' (by decide)
    obtain ⟨k,hk⟩ := mem_length_retained X hcritical_mem
    apply prefix_mem_of_retained X hpre' hzmem
    exact ⟨k,(Z.length_map u).trans hk⟩

/-- A.3(2) in the exported abstract Ramsey-space interface. -/
theorem amalgamation_refine {n d : Nat} (a : system.Approx n) (Y : CriticalMap)
    (hd : finitization.HasDepth a Y d)
    {A : CriticalMap} (hAY : system.le A Y)
    (hne : (system.neighborhood a A).Nonempty) :
    ∃ A', A' ∈ system.levelNeighborhood d Y ∧
      system.neighborhood a A' ⊆ system.neighborhood a A :=
  amalgamation_refine_of_support relative_support_construction a Y hd hAY hne

end AllThoseBigRamsey.Pseudotree.CriticalCopies
