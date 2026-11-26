import PseudotreeValidation.RelativeReservoirInit
import PseudotreeValidation.RelativeTail

/-! Infinite continuation of the relative reservoir construction.
The same synchronized transitions used for absolute recurrence run
from an arbitrary prescribed boundary layer. The output records
prefix witnesses, actual coding points, and fork witnesses in the
target assigned to each slot. -/
namespace AllThoseBigRamsey.Pseudotree.Reservoir
open RayEmbeddings RayMapModel
open SparseNormalization (critical critical_length Point)
open CriticalCopies (Node Boundary FiniteCritical RelativeTail CriticalMap)
open scoped FirstOrder

abbrev StableAfter (targets : Word → Target) (h : Nat) : Prop :=
  ∀ j, h ≤ j → ∀ (u : Level sparseSource j) a, child u.val a ∈ sparseSource.nodes →
    targets (child u.val a) = targets u.val

structure TailRun (targets : Word → Target) (h : Nat) where
  layer : ∀ k, Layer sparseSource targets (h+k)
  step : ∀ k, Step (layer k)
  next_eq : ∀ k, (step k).next = layer (k+1)

noncomputable def tailSequence {targets : Word → Target} {h : Nat}
    (P0 : Layer sparseSource targets h)
    (pick : ∀ k, (P : Layer sparseSource targets (h+k)) → Step P) :
    (k : Nat) → Layer sparseSource targets (h+k)
  | 0 => P0
  | k+1 => (pick k (tailSequence P0 pick k)).next

noncomputable def TailRun.ofInitial {targets : Word → Target} {h : Nat}
    (P0 : Layer sparseSource targets h) (hsparse : SparseTargets targets)
    (stable : StableAfter targets h) : TailRun targets h := by
  let pick (k : Nat) (P : Layer sparseSource targets (h+k)) : Step P :=
    Classical.choice (exists_step P hsparse (stable (h+k) (by omega)))
  exact ⟨tailSequence P0 pick,fun k => pick k (tailSequence P0 pick k),fun _ => rfl⟩

namespace TailRun

variable {targets : Word → Target} {h : Nat}

def levels (R : TailRun targets h) (i : Nat) : Nat := (R.step (i-h)).level

theorem strict (R : TailRun targets h) {i j : Nat} (hi : h ≤ i) (hij : i < j) :
    R.levels i < R.levels j := by
  have hs : StrictMono (fun k => (R.step k).level) := by
    apply strictMono_nat_of_lt_succ
    intro k
    have hu := (R.step k).upper
    rw [R.next_eq k] at hu
    exact hu.trans_le (R.step (k+1)).lower
  exact hs (show i-h < j-h by omega)

def value (R : TailRun targets h) (u : Node) : Word :=
  if hu : h ≤ u.val.length then
    ((R.step (u.val.length-h)).roots
      ⟨u.val,u.property,by omega⟩).map toFin
  else []

theorem value_at (R : TailRun targets h) (k : Nat) (u : Level sparseSource (h+k)) :
    R.value ⟨u.val,u.property.1⟩ = ((R.step k).roots u).map toFin := by
  rcases u with ⟨u,hu,hlen⟩
  have hh : h ≤ u.length := by omega
  have hk : u.length-h = k := by omega
  unfold value
  rw [dif_pos hh]
  -- Transport only the index of the step and its level-subtype input.
  simp only [hk]

theorem value_length (R : TailRun targets h) (u : Node) (hu : h ≤ u.val.length) :
    (R.value u).length = R.levels u.val.length := by
  unfold value levels
  rw [dif_pos hu,List.length_map]
  exact (R.step _).root_length _

theorem value_tree (R : TailRun targets h) (u : Node) (hu : h ≤ u.val.length) :
    SparseNormalization.Tree (R.value u) := by
  unfold value
  rw [dif_pos hu]
  change Sparse.InTree ((((R.step _).roots _).map toFin).map toLetter)
  simpa only [List.map_map,Function.comp_def,toLetter_toFin,List.map_id_fun',id_eq]
    using (R.step (u.val.length-h)).root_tree
      (⟨u.val,u.property,by omega⟩ : Level sparseSource (h+(u.val.length-h)))

theorem critical_value (R : TailRun targets h) (i : Nat) (hi : h ≤ i) :
    R.value (CriticalCopies.criticalNode i) = critical (R.levels i) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hi
  have hc := R.value_at k (criticalAt sparseSource (h+k))
  change R.value (CriticalCopies.criticalNode (h+k)) =
    ((R.step k).roots (criticalAt sparseSource (h+k))).map toFin at hc
  rw [hc,(R.step k).critical]
  have he : h+k-h = k := by omega
  simp only [levels,he,critical]

theorem phase (R : TailRun targets h) (i : Nat) (_hi : h ≤ i) :
    R.levels i % 3 = 2 ↔ i % 3 = 2 := by
  have hi := _hi
  have hp := (R.step (i-h)).phase
  change R.levels i % 3 = 2 ↔
    (if (h+(i-h)) % 3 = 2 then PaperKind.code else PaperKind.split) ≠ .split at hp
  rw [Nat.add_sub_of_le hi] at hp
  by_cases hm : i % 3 = 2 <;> simpa [hm] using hp

theorem step_value (R : TailRun targets h) (s : Word) (a : Fin 3)
    (hs : SparseNormalization.Tree (s ++ [a])) (hstart : h ≤ s.length) :
    ∃ b : Word, R.value ⟨s ++ [a],hs⟩ =
      R.value (CriticalCopies.parentNode s a hs) ++ a :: b ∧
        (a ≠ 1 → Binary b) := by
  let k := s.length-h
  let u : Level sparseSource (h+k) :=
    ⟨s,SparseNormalization.tree_prefix hs (List.prefix_append s [a]),by dsimp [k]; omega⟩
  let v : Level sparseSource (h+(k+1)) := childNode u a hs
  obtain ⟨b,hb,hbbin⟩ := (R.step k).edge u a hs
  obtain ⟨c,hcbin,hc⟩ := (R.step (k+1)).root_binary v
  have hroots : (R.step (k+1)).roots v =
      (R.step k).roots u ++ toLetter a :: (b ++ c) := by
    rw [hc,← R.next_eq k]
    change (R.step k).next.prefixes (childNode u a hs) ++ c = _
    rw [hb]
    simp only [List.append_assoc,List.cons_append]
  refine ⟨(b++c).map toFin,?_,?_⟩
  · change R.value ⟨v.val,v.property.1⟩ =
      R.value ⟨u.val,u.property.1⟩ ++ a :: (b++c).map toFin
    rw [R.value_at (k+1) v,R.value_at k u,hroots]
    simp only [List.map_append,List.map_cons,toFin_toLetter]
  · intro ha
    apply (binary_map _).mpr
    intro x hx hx1
    have hnot : TernaryLetter.one ∉ b++c := by
      simp only [List.mem_append,not_or]
      exact ⟨hbbin ha,hcbin⟩
    exact hnot (hx1 ▸ hx)

/-- Prefix witnesses at all tail nodes, in their own assigned target. -/
theorem prefix_supported (R : TailRun targets h) (stable : StableAfter targets h)
    (u : Node) (hu : h ≤ u.val.length) :
    ∃ z ∈ Set.range (targets u.val),
      ((R.value u).map toLetter).IsPrefix (fromBlocks z) := by
  let k := u.val.length-h
  let v : Level sparseSource (h+k) := ⟨u.val,u.property,by dsimp [k]; omega⟩
  obtain ⟨z,hz,hpre⟩ := (R.step k).root_supported
    (stable (h+k) (by omega)) v
  refine ⟨z,hz,?_⟩
  change ((R.value ⟨v.val,v.property.1⟩).map toLetter).IsPrefix (fromBlocks z)
  rw [R.value_at k v]
  simpa only [List.map_map,Function.comp_def,toLetter_toFin,List.map_id_fun',id_eq] using hpre

theorem coding_supported (R : TailRun targets h) (u : Node) (hu : h ≤ u.val.length)
    (hp : Point u.val) : DiaryChains.model (R.value u) ∈ Set.range (targets u.val) := by
  let k := u.val.length-h
  let v : Level sparseSource (h+k) := ⟨u.val,u.property,by dsimp [k]; omega⟩
  change DiaryChains.model (R.value ⟨v.val,v.property.1⟩) ∈ Set.range (targets v.val)
  rw [R.value_at k v]
  change toBlocks ((((R.step k).roots v).map toFin).map toLetter) ∈ Set.range (targets v.val)
  simpa only [List.map_map,Function.comp_def,toLetter_toFin,List.map_id_fun',id_eq] using
    (R.step k).coding v hp

theorem fork_supported (R : TailRun targets h) (stable : StableAfter targets h)
    (i : Nat) (hi : h ≤ i) (hsplit : i % 3 ≠ 2) :
    ∃ y ∈ Set.range (targets (critical i)), ∃ z ∈ Set.range (targets (critical i)),
      ((R.value (CriticalCopies.criticalNode i)).map toLetter ++ [.zero]).IsPrefix (fromBlocks y) ∧
      ((R.value (CriticalCopies.criticalNode i)).map toLetter ++ [.two]).IsPrefix (fromBlocks z) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hi
  obtain ⟨y,hy,z,hz,h0,h2⟩ := (R.step k).split_supported
    (stable (h+k) (by omega)) hsplit
  have hc := R.value_at k (criticalAt sparseSource (h+k))
  change R.value (CriticalCopies.criticalNode (h+k)) =
    ((R.step k).roots (criticalAt sparseSource (h+k))).map toFin at hc
  refine ⟨y,hy,z,hz,?_,?_⟩
  · rw [hc]
    simpa only [List.map_map,Function.comp_def,toLetter_toFin,List.map_id_fun',id_eq] using h0
  · rw [hc]
    simpa only [List.map_map,Function.comp_def,toLetter_toFin,List.map_id_fun',id_eq] using h2

end TailRun

/-- The infinite relative reservoir endpoint. It extends the given
finite prefix and retains the assigned target support at every tail
node and at every critical event. No global target homogeneity is used. -/
theorem relative_reservoir {j : Nat} (e : FiniteCritical (j+1))
    (targets : Word → Target) (hsparse : SparseTargets targets)
    (stable : StableAfter targets (j+1)) (Q : BoundarySeeds e targets) :
    ∃ X : CriticalMap, CriticalCopies.Extends X e ∧
      (∀ u : Node, j+1 ≤ u.val.length →
        ∃ z ∈ Set.range (targets u.val), ((X.map u).map toLetter).IsPrefix (fromBlocks z)) ∧
      (∀ u : Node, j+1 ≤ u.val.length → Point u.val →
        DiaryChains.model (X.map u) ∈ Set.range (targets u.val)) ∧
      ∀ i, j+1 ≤ i → i % 3 ≠ 2 →
        ∃ y ∈ Set.range (targets (critical i)), ∃ z ∈ Set.range (targets (critical i)),
          ((X.map (CriticalCopies.criticalNode i)).map toLetter ++ [.zero]).IsPrefix (fromBlocks y) ∧
          ((X.map (CriticalCopies.criticalNode i)).map toLetter ++ [.two]).IsPrefix (fromBlocks z) := by
  obtain ⟨P,hP,hslot⟩ := relativeInitial Q
  let R := TailRun.ofInitial P hsparse stable
  let T : RelativeTail e := {
    map := R.value
    level := R.levels
    after := by
      have hlo : P.bound ≤ R.levels (j+1) := by
        change P.bound ≤ (R.step ((j+1)-(j+1))).level
        rw [Nat.sub_self]
        exact (R.step 0).lower
      simpa only [Nat.add_sub_cancel] using hP.trans_le hlo
    strict := R.strict
    length_map := R.value_length
    tree := R.value_tree
    critical_image := R.critical_value
    phase := R.phase
    step := R.step_value
    boundary := by
      intro s a hs hlen
      have hsj : s.length = j := by simp at hlen; omega
      let u : Level sparseSource j :=
        ⟨s,SparseNormalization.tree_prefix hs (List.prefix_append s [a]),hsj⟩
      let w : Boundary j := childNode u a hs
      obtain ⟨b,hb,hbbin⟩ := hslot w
      have hb' : (R.layer 0).prefixes w =
          (CriticalCopies.slot e w).map toLetter ++ b := hb
      obtain ⟨c,hcbin,hc⟩ := (R.step 0).root_binary w
      rw [hb'] at hc
      have hslot' : CriticalCopies.slot e w =
          e.map (CriticalCopies.parentNode s a hs) ++ [a] := by
        exact CriticalCopies.slot_childNode e u a hs
      refine ⟨(b++c).map toFin,?_,?_⟩
      · change R.value ⟨w.val,w.property.1⟩ =
          e.map (CriticalCopies.parentNode s a hs) ++ a :: (b++c).map toFin
        rw [R.value_at 0 w,hc,hslot']
        simp [List.map_append,List.map_map,Function.comp_def,List.append_assoc]
      · intro ha
        apply (binary_map _).mpr
        intro x hx hx1
        have hbno : TernaryLetter.one ∉ b :=
          hbbin (by simpa only [w,last_childNode] using ha)
        have hnot : TernaryLetter.one ∉ b++c := by simp [hbno,hcbin]
        exact hnot (hx1 ▸ hx) }
  let X := T.assemble (by omega : 0 < j+1)
  refine ⟨X,T.assemble_extends (by omega),?_,?_,?_⟩
  · intro u hu
    rw [T.assemble_tail (by omega) u hu]
    exact R.prefix_supported stable u hu
  · intro u hu hp
    rw [T.assemble_tail (by omega) u hu]
    exact R.coding_supported u hu hp
  · intro i hi hsplit
    rw [T.assemble_tail (by omega) (CriticalCopies.criticalNode i) (by simpa using hi)]
    exact R.fork_supported stable i hi hsplit

end AllThoseBigRamsey.Pseudotree.Reservoir
