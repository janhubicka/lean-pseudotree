import PseudotreeValidation.SparseNormalization
import RamseySpace.AbstractEllentuck

/-! Concrete critical copies of the sparse prefix tree. The local map
conditions are the manuscript's edge and level conditions; the upstream
approximation-system and closedness interfaces are used directly. -/

namespace AllThoseBigRamsey.Pseudotree.CriticalCopies
open RayEmbeddings RayMapModel
open SparseNormalization (Tree critical critical_map critical_length tree_prefix)

abbrev Node := {w : Word // Tree w}

def criticalNode (j : Nat) : Node :=
  ⟨critical j, by
    change Sparse.InTree ((critical j).map toLetter)
    rw [critical_map]
    exact Sparse.critical_inTree j⟩

@[simp] theorem criticalNode_length (j : Nat) : (criticalNode j).val.length = j :=
  critical_length j

def parentNode (s : Word) (a : Fin 3) (hs : Tree (s ++ [a])) : Node :=
  ⟨s, tree_prefix hs (List.prefix_append s [a])⟩

/-- No Ramsey or infinite extension assumption is part of this definition. -/
@[ext] structure CriticalMap where
  map : Node → Word
  level_strict : StrictMono (fun j => (map (criticalNode j)).length)
  length_map : ∀ u : Node,
    (map u).length = (map (criticalNode u.val.length)).length
  step : ∀ s a (hs : Tree (s ++ [a])), ∃ p : Word,
    map ⟨s ++ [a], hs⟩ = map (parentNode s a hs) ++ a :: p ∧
      (a ≠ 1 → Binary p)
  maps_tree : ∀ u, Tree (map u)
  critical_image : ∀ j, map (criticalNode j) =
    critical ((map (criticalNode j)).length)
  phase : ∀ j, (map (criticalNode j)).length % 3 = 2 ↔ j % 3 = 2

def CriticalMap.level (X : CriticalMap) (j : Nat) : Nat :=
  (X.map (criticalNode j)).length

def identity : CriticalMap where
  map := Subtype.val
  level_strict := by intro i j h; simpa using h
  length_map := by intro u; simp
  step := by intro s a hs; exact ⟨[], rfl, fun _ => binary_nil⟩
  maps_tree := Subtype.property
  critical_image := by intro j; simp [criticalNode, critical_length]
  phase := by intro j; simp

noncomputable def onWord (X : CriticalMap) (w : Word) : Word := by
  classical
  exact if hw : Tree w then X.map ⟨w, hw⟩ else []

@[simp] theorem onWord_agrees (X : CriticalMap) (u : Node) :
    onWord X u.val = X.map u := by
  classical
  simp [onWord, u.property]

noncomputable def partial (X : CriticalMap) : PrefixRayMap Tree where
  root_mem := by
    have h := (criticalNode 0).property
    have hz : critical 0 = [] := List.length_eq_zero_iff.mp (critical_length 0)
    simpa [criticalNode, hz] using h
  prefix_closed := fun s t h => tree_prefix h (List.prefix_append s t)
  map := onWord X
  level := X.level
  level_strict := X.level_strict
  length_map := by
    intro s hs
    rw [onWord_agrees X (⟨s, hs⟩ : Node)]
    exact X.length_map ⟨s, hs⟩
  step := by
    intro s a hs
    obtain ⟨p, hp, hb⟩ := X.step s a hs
    refine ⟨p, ?_, hb⟩
    change onWord X (s ++ [a]) = onWord X s ++ a :: p
    rw [onWord_agrees X (⟨s ++ [a], hs⟩ : Node),
      onWord_agrees X (parentNode s a hs)]
    exact hp

noncomputable def total (X : CriticalMap) : RayStrongMap := (partial X).completion

theorem total_agrees (X : CriticalMap) (u : Node) : (total X).map u.val = X.map u := by
  rw [total, PrefixRayMap.completion_agrees _ _ u.property]
  exact onWord_agrees X u

theorem map_injective (X : CriticalMap) : Function.Injective X.map := by
  intro s t h
  apply Subtype.ext
  apply (total X).injective
  simpa only [total_agrees] using h

theorem map_strictMono (X : CriticalMap) : StrictMono X.map := by
  intro s t h
  have hh := DiaryNormalization.rayMap_strictMono (total X) h
  simpa only [total_agrees] using hh

/-- Finite source prefixes stop at the manuscript's whole-stage boundaries. -/
abbrev Prefix (n : Nat) := {u : Node // u.val.val.length < 3 * n}

def restriction (n : Nat) (X : CriticalMap) : Prefix n → Word := fun u => X.map u.val

def Approx (n : Nat) := {a : Prefix n → Word // ∃ X : CriticalMap, restriction n X = a}

def approx (n : Nat) (X : CriticalMap) : Approx n := ⟨restriction n X, X, rfl⟩

theorem approx_eq_iff {n : Nat} {X Y : CriticalMap} :
    approx n X = approx n Y ↔ ∀ u : Prefix n, X.map u.val = Y.map u.val := by
  constructor
  · intro h u
    exact congrFun (congrArg Subtype.val h) u
  · intro h
    exact Subtype.ext (funext h)

def copyRange (X : CriticalMap) : Set Word := Set.range X.map

def system : RamseySpace.ApproximationSystem where
  Point := CriticalMap
  Approx := Approx
  le X Y := copyRange X ⊆ copyRange Y
  le_refl _ := fun _ h => h
  le_trans h₁ h₂ := fun _ h => h₂ (h₁ h)
  approx := approx
  approx_surjective := by
    intro n a
    obtain ⟨X, hX⟩ := a.property
    exact ⟨X, Subtype.ext hX⟩
  empty := approx 0 identity
  approx_zero := by
    intro X
    apply approx_eq_iff.mpr
    intro u
    have h := u.property
    omega
  separated := by
    intro X Y h
    apply CriticalMap.ext
    funext u
    exact (approx_eq_iff.mp (h (u.val.length+1))) ⟨u, by omega⟩
  coherent := by
    intro X Y n h m hmn
    apply approx_eq_iff.mpr
    intro u
    exact (approx_eq_iff.mp h) ⟨u.val, by have := u.property; omega⟩

/-- A finite prefix has no extra hidden coordinates. -/
private def wordsThrough : Nat → Finset Word
  | 0 => {[]}
  | n+1 => {[]} ∪ (Finset.univ : Finset (Fin 3)).biUnion
      (fun a => (wordsThrough n).image (List.cons a))

private theorem mem_wordsThrough (n : Nat) (w : Word) :
    w ∈ wordsThrough n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero => simp [wordsThrough]
  | succ n ih => cases w <;> simp [wordsThrough, ih]

instance prefix_finite (n : Nat) : Finite (Prefix n) := by
  let encode (u : Prefix n) : {w : Word // w ∈ wordsThrough (3*n)} :=
    ⟨u.val.val, (mem_wordsThrough _ _).mpr u.property.le⟩
  apply Finite.of_injective encode
  intro u v h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg Subtype.val h

/-- The literal finite range, as in the manuscript (not a map outside its
source prefix). -/
def finiteRange (a : system.FiniteApprox) : Set Word := Set.range a.2.val

theorem finiteRange_finite (a : system.FiniteApprox) : (finiteRange a).Finite := by
  rcases a with ⟨n, a⟩
  exact Set.finite_range a.val

def leFin (a b : system.FiniteApprox) : Prop := finiteRange a ⊆ finiteRange b

theorem prefixRange_mono (X : CriticalMap) {n m : Nat} (hnm : n ≤ m) :
    finiteRange (system.finiteApprox n X) ⊆ finiteRange (system.finiteApprox m X) := by
  rintro _ ⟨u, rfl⟩
  exact ⟨⟨u.val, by have := u.property; omega⟩, rfl⟩

theorem value_mem_prefix (X : CriticalMap) (u : Node) :
    X.map u ∈ finiteRange (system.finiteApprox (u.val.length+1) X) :=
  ⟨⟨u, by omega⟩, rfl⟩

theorem finite_subset_prefix (X : CriticalMap) {t : Set Word}
    (ht : t.Finite) (hsub : t ⊆ copyRange X) :
    ∃ n, t ⊆ finiteRange (system.finiteApprox n X) := by
  induction t, ht using Set.Finite.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x t hxt ht ih =>
    obtain ⟨n, hn⟩ := ih (fun y hy => hsub (Set.mem_insert_of_mem x hy))
    obtain ⟨u, hu⟩ := hsub (Set.mem_insert x t)
    refine ⟨max n (u.val.length+1), ?_⟩
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · apply prefixRange_mono X (Nat.le_max_right _ _)
      rw [← hu]
      exact value_mem_prefix X u
    · exact prefixRange_mono X (Nat.le_max_left _ _) (hn hy)

theorem realizesOrder (X Y : CriticalMap) :
    system.le X Y ↔ ∀ n, ∃ m,
      leFin (system.finiteApprox n X) (system.finiteApprox m Y) := by
  constructor
  · intro h n
    apply finite_subset_prefix Y (finiteRange_finite _)
    rintro _ ⟨u, rfl⟩
    exact h ⟨u.val, rfl⟩
  · intro h _ hx
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨m, hm⟩ := h (u.val.length+1)
    obtain ⟨v, hv⟩ := hm (value_mem_prefix X u)
    exact ⟨v.val, hv⟩

/-- The labelled finite approximation image has exactly the expected size.
This is used to forget the labels without identifying different stages. -/
theorem finiteRange_ncard (a : system.FiniteApprox) :
    (finiteRange a).ncard = Nat.card (Prefix a.1) := by
  rcases a with ⟨n, a⟩
  obtain ⟨X, hX⟩ := a.property
  change (Set.range a.val).ncard = Nat.card (Prefix n)
  rw [← hX, Set.ncard_range_of_injective]
  intro u v h
  exact Subtype.ext (map_injective X h)

def sourceRange (n : Nat) : Set Word := Set.range (fun u : Prefix n => u.val.val)

theorem sourceRange_ncard (n : Nat) :
    (sourceRange n).ncard = Nat.card (Prefix n) := by
  apply Set.ncard_range_of_injective
  intro u v h
  exact Subtype.ext (Subtype.ext h)

theorem sourceRange_strict {n m : Nat} (h : n < m) :
    sourceRange n ⊂ sourceRange m := by
  apply Set.ssubset_iff_exists.mpr
  constructor
  · rintro _ ⟨u, rfl⟩
    exact ⟨⟨u.val, by have := u.property; omega⟩, rfl⟩
  · refine ⟨(criticalNode (3*n)).val, ⟨⟨criticalNode (3*n), by simp; omega⟩, rfl⟩, ?_⟩
    rintro ⟨u, hu⟩
    have hlen := congrArg List.length hu
    have hh := u.property
    simp only [criticalNode_length] at hlen
    omega

theorem prefix_card_strict : StrictMono (fun n => Nat.card (Prefix n)) := by
  intro n m h
  rw [← sourceRange_ncard n, ← sourceRange_ncard m]
  exact Set.ncard_lt_ncard (sourceRange_strict h) (Set.finite_range _)

theorem finiteRange_injective : Function.Injective finiteRange := by
  rintro ⟨n, a⟩ ⟨m, b⟩ h
  have hc := congrArg Set.ncard h
  simp only [finiteRange_ncard] at hc
  have hnm : n = m := prefix_card_strict.injective hc
  subst m
  obtain ⟨X, hX⟩ := a.property
  obtain ⟨Y, hY⟩ := b.property
  let f : Prefix n ↪o Word :=
    OrderEmbedding.ofStrictMono a.val (by rw [← hX]; exact fun _ _ h => map_strictMono X h)
  let g : Prefix n ↪o Word :=
    OrderEmbedding.ofStrictMono b.val (by rw [← hY]; exact fun _ _ h => map_strictMono Y h)
  have heq : f = g := OrderEmbedding.eq_of_range_eq h
  have hab : a = b := Subtype.ext (congrArg (fun e : Prefix n ↪o Word => (e : Prefix n → Word)) heq)
  subst b
  rfl

theorem lowerFinite (b : system.FiniteApprox) : Set.Finite {a | leFin a b} := by
  refine Set.Finite.of_finite_image ?_ finiteRange_injective.injOn
  apply (finiteRange_finite b).finite_subsets.subset
  rintro s ⟨a, ha, rfl⟩
  exact ha

theorem finiteRange_subset_of_isInitial {n m : Nat}
    {a : system.Approx n} {b : system.Approx m}
    (hab : system.IsInitial a b) :
    finiteRange ⟨n,a⟩ ⊆ finiteRange ⟨m,b⟩ := by
  obtain ⟨hnm, X, hXa, hXb⟩ := hab
  have ha : system.finiteApprox n X = ⟨n,a⟩ := Sigma.ext rfl (heq_of_eq hXa)
  have hb : system.finiteApprox m X = ⟨m,b⟩ := Sigma.ext rfl (heq_of_eq hXb)
  rw [← ha, ← hb]
  exact prefixRange_mono X hnm

/-- A.2 in the upstream (non-strict initial segment) interface. -/
def finitization : RamseySpace.Finitization system where
  leFin := leFin
  leFin_refl _ := fun _ h => h
  leFin_trans h₁ h₂ := fun _ h => h₂ (h₁ h)
  lowerFinite := lowerFinite
  realizesOrder := realizesOrder
  prefix_leFin := by
    intro n m k a b c hab hbc
    exact ⟨k, c, system.isInitial_refl c,
      fun _ hx => hbc (finiteRange_subset_of_isInitial hab hx)⟩

/-- Metric closedness follows by taking the compatible union. Each local
constraint is checked at a single finite stage, including critical type. -/
theorem closed : system.IsClosedApproximationImage := by
  classical
  intro c hc
  let F (n : Nat) : CriticalMap := (hc n).choose
  have hF (n j : Nat) (hj : j ≤ n) : approx j (F n) = c j :=
    (hc n).choose_spec j hj
  have hcoh (i j : Nat) (hij : i ≤ j) (u : Prefix i) :
      (F i).map u.val = (F j).map u.val :=
    (approx_eq_iff.mp ((hF i i le_rfl).trans (hF j i hij).symm)) u
  let L (u : Node) : Word := (F (u.val.length+1)).map u
  have agrees (n : Nat) (u : Node) (hu : u.val.length < 3*n) :
      L u = (F n).map u := by
    let k := u.val.length+1
    let M := max k n
    exact (hcoh k M (Nat.le_max_left _ _) ⟨u, by dsimp [k]; omega⟩).trans
      (hcoh n M (Nat.le_max_right _ _) ⟨u,hu⟩).symm
  let X : CriticalMap := {
    map := L
    level_strict := by
      intro i j hij
      have hi : (criticalNode i).val.length < 3*(j+1) := by simp; omega
      have hj : (criticalNode j).val.length < 3*(j+1) := by simp; omega
      rw [agrees (j+1) _ hi, agrees (j+1) _ hj]
      exact (F (j+1)).level_strict hij
    length_map := by
      intro u
      have hu : u.val.length < 3*(u.val.length+1) := by omega
      have hv : (criticalNode u.val.length).val.length < 3*(u.val.length+1) := by
        simpa only [criticalNode_length] using hu
      rw [agrees (u.val.length+1) _ hu, agrees (u.val.length+1) _ hv]
      exact (F (u.val.length+1)).length_map u
    step := by
      intro s a hs
      have h₁ : (⟨s ++ [a], hs⟩ : Node).val.length < 3*(s.length+2) := by simp; omega
      have h₂ : (parentNode s a hs).val.length < 3*(s.length+2) := by
        simp [parentNode]; omega
      rw [agrees (s.length+2) _ h₁, agrees (s.length+2) _ h₂]
      exact (F (s.length+2)).step s a hs
    maps_tree := by
      intro u
      rw [agrees (u.val.length+1) u (by omega)]
      exact (F (u.val.length+1)).maps_tree u
    critical_image := by
      intro j
      have hj : (criticalNode j).val.length < 3*(j+1) := by simp; omega
      simp only [agrees (j+1) _ hj]
      exact (F (j+1)).critical_image j
    phase := by
      intro j
      have hj : (criticalNode j).val.length < 3*(j+1) := by simp; omega
      rw [agrees (j+1) _ hj]
      exact (F (j+1)).phase j }
  refine ⟨X, ?_⟩
  intro n
  exact ((approx_eq_iff.mpr (fun u => agrees n u.val u.property)).trans (hF n n le_rfl))

theorem tychonoffClosed : system.IsTychonoffClosed :=
  (system.isTychonoffClosed_iff_isClosedApproximationImage).mpr closed

/-- Exact remaining obligations: the concrete relative A.3 and A.4 fields.
This assembly is intentionally conditional until they have been proved. -/
theorem ellentuck_of_axioms (R : RamseySpace.AbstractRamseySpace system) :
    RamseySpace.IsTopologicalRamseySpaceTextbook (S := system) :=
  RamseySpace.abstractEllentuck_textbook R tychonoffClosed

end AllThoseBigRamsey.Pseudotree.CriticalCopies
