import PseudotreeValidation.CriticalCopies
import PseudotreeValidation.DiaryRecoveryMaps

/-!
# Pullback and composition of actual critical copies

The edge-reflection statement is purely about ray-preserving strong maps.
The remaining proofs use the literal local definition of a critical map,
including preservation of the split/coding phase. The finite version
does not presuppose that its pullback is extendible.
-/

namespace AllThoseBigRamsey.Pseudotree
open RayEmbeddings RayMapModel

namespace RayEmbeddings.RayStrongMap

/-- A strong map reflects the prefix relation. -/
theorem reflect_prefix (f : RayStrongMap) {s t : Word}
    (h : (f.map s).IsPrefix (f.map t)) : s.IsPrefix t := by
  have hlevels : StrictMono f.level := fun _ _ h => f.level_strict h
  have hlen := h.length_le
  rw [f.length_map, f.length_map] at hlen
  have hst := hlevels.le_iff_le.mp hlen
  have heq := List.prefix_iff_eq_take.mp h
  rw [f.length_map, ← DiaryRecovery.map_take f t s.length hst] at heq
  exact List.prefix_iff_eq_take.mpr (f.injective heq)

/-- Reflection of the first retained digit and the absence of further 1s
on a binary edge. The exact tail lemma is already used in the word-model
embedding proof. -/
theorem reflect_edge (f : RayStrongMap) {s t p : Word} {a : Fin 3}
    (he : f.map t = f.map s ++ a :: p)
    (hb : a ≠ 1 → Binary p) :
    ∃ q : Word, t = s ++ a :: q ∧ (a ≠ 1 → Binary q) := by
  have hp : (f.map s).IsPrefix (f.map t) := ⟨a :: p, he.symm⟩
  obtain ⟨tail, ht⟩ := f.reflect_prefix hp
  have ht' : t = s ++ tail := ht.symm
  have hn : tail ≠ [] := by
    intro h
    have heq : t = s := by simpa [h] using ht'
    have hl := congrArg List.length he
    rw [heq] at hl
    simp only [List.length_append, List.length_cons] at hl
    omega
  obtain ⟨b,q,rfl⟩ := List.exists_cons_of_ne_nil hn
  obtain ⟨r,hr,hbr⟩ := RayMapModel.map_append_cons_exact f s b q
  have hcons : a :: p = b :: r :=
    List.append_cancel_left (he.symm.trans ((congrArg f.map ht').trans hr))
  obtain ⟨hab,hpr⟩ := List.cons.inj hcons
  subst b
  exact ⟨q,ht',fun ha => (hbr ha).mp (hpr ▸ hb ha)⟩

end RayEmbeddings.RayStrongMap

namespace CriticalCopies
open SparseNormalization (Tree critical critical_length tree_prefix)

/-- Interpret a critical map as a function into the subtype of tree nodes. -/
def intoTree (X : CriticalMap) (u : Node) : Node := ⟨X.map u, X.maps_tree u⟩

theorem total_intoTree (X : CriticalMap) (u : Node) :
    (total X).map u.val = (intoTree X u).val :=
  total_agrees X u

theorem level_eq_length (X : CriticalMap) (u : Node) :
    X.level u.val.length = (X.map u).length :=
  (X.length_map u).symm

theorem intoTree_critical (X : CriticalMap) (j : Nat) :
    intoTree X (criticalNode j) = criticalNode (X.level j) :=
  Subtype.ext (X.critical_image j)

/-- The actual composition, not just a range inclusion witness. -/
noncomputable def compose (Y X : CriticalMap) : CriticalMap where
  map u := Y.map (intoTree X u)
  level_strict := by
    intro i j hij
    change (Y.map (intoTree X (criticalNode i))).length <
      (Y.map (intoTree X (criticalNode j))).length
    rw [intoTree_critical, intoTree_critical]
    exact Y.level_strict (X.level_strict hij)
  length_map := by
    intro u
    change (Y.map (intoTree X u)).length =
      (Y.map (intoTree X (criticalNode u.val.length))).length
    rw [Y.length_map (intoTree X u), intoTree_critical]
    rw [show (intoTree X u).val.length = X.level u.val.length from X.length_map u]
  step := by
    intro s a hs
    let u : Node := parentNode s a hs
    let v : Node := ⟨s ++ [a],hs⟩
    obtain ⟨p,hp,hpb⟩ := X.step s a hs
    have hp' : (intoTree X v).val = (intoTree X u).val ++ a :: p := hp
    obtain ⟨q,hq,hqb⟩ := RayMapModel.map_append_cons_exact
      (total Y) (intoTree X u).val a p
    refine ⟨q, ?_, fun ha => (hqb ha).mpr (hpb ha)⟩
    change Y.map (intoTree X v) = Y.map (intoTree X u) ++ a :: q
    rw [← total_agrees Y (intoTree X v), ← total_agrees Y (intoTree X u), hp']
    exact hq
  maps_tree := fun u => Y.maps_tree (intoTree X u)
  critical_image := by
    intro j
    change Y.map (intoTree X (criticalNode j)) =
      critical ((Y.map (intoTree X (criticalNode j))).length)
    rw [intoTree_critical]
    exact Y.critical_image _
  phase := by
    intro j
    change (Y.map (intoTree X (criticalNode j))).length % 3 = 2 ↔ j % 3 = 2
    rw [intoTree_critical]
    exact (Y.phase (X.level j)).trans (X.phase j)

@[simp] theorem compose_apply (Y X : CriticalMap) (u : Node) :
    (compose Y X).map u = Y.map (intoTree X u) := rfl

theorem compose_le (Y X : CriticalMap) : copyRange (compose Y X) ⊆ copyRange Y := by
  rintro w ⟨u,rfl⟩
  exact ⟨intoTree X u,rfl⟩

/-- Inverting a critical map on its range. Off the range the chosen value
is irrelevant. -/
noncomputable def preNode (Y : CriticalMap) (w : Word) : Node := by
  classical
  exact if h : w ∈ copyRange Y then h.choose else criticalNode 0

theorem preNode_spec (Y : CriticalMap) {w : Word} (h : w ∈ copyRange Y) :
    Y.map (preNode Y w) = w := by
  unfold preNode
  rw [dif_pos h]
  exact h.choose_spec

theorem preNode_image (Y : CriticalMap) (u : Node) :
    preNode Y (Y.map u) = u :=
  map_injective Y (preNode_spec Y ⟨u,rfl⟩)

/-- Pull back the node set of X through Y, with a single definition
usable on finite or infinite domains. -/
noncomputable def pullNode (X Y : CriticalMap) (u : Node) : Node :=
  preNode Y (X.map u)

theorem pullNode_spec (X Y : CriticalMap) (u : Node)
    (h : X.map u ∈ copyRange Y) : Y.map (pullNode X Y u) = X.map u :=
  preNode_spec Y h

theorem pullNode_length_map (X Y : CriticalMap) (u v : Node)
    (hu : X.map u ∈ copyRange Y) (hv : X.map v ∈ copyRange Y)
    (hlen : u.val.length = v.val.length) :
    (pullNode X Y u).val.length = (pullNode X Y v).val.length := by
  apply Y.level_strict.injective
  change Y.level (pullNode X Y u).val.length = Y.level (pullNode X Y v).val.length
  rw [level_eq_length, level_eq_length, pullNode_spec X Y u hu, pullNode_spec X Y v hv]
  rw [X.length_map u, X.length_map v, hlen]

theorem pullNode_length_strict (X Y : CriticalMap) (u v : Node)
    (hu : X.map u ∈ copyRange Y) (hv : X.map v ∈ copyRange Y)
    (hlt : u.val.length < v.val.length) :
    (pullNode X Y u).val.length < (pullNode X Y v).val.length := by
  apply Y.level_strict.lt_iff_lt.mp
  change Y.level (pullNode X Y u).val.length < Y.level (pullNode X Y v).val.length
  rw [level_eq_length, level_eq_length, pullNode_spec X Y u hu, pullNode_spec X Y v hv]
  rw [X.length_map u, X.length_map v]
  exact X.level_strict hlt

/-- An ambient critical node in a critical copy is the image of its
own critical node at the corresponding source height. -/
theorem pullNode_critical (X Y : CriticalMap) (j : Nat)
    (h : X.map (criticalNode j) ∈ copyRange Y) :
    pullNode X Y (criticalNode j) =
      criticalNode (pullNode X Y (criticalNode j)).val.length := by
  let u := pullNode X Y (criticalNode j)
  apply map_injective Y
  change Y.map u = Y.map (criticalNode u.val.length)
  have he := pullNode_spec X Y (criticalNode j) h
  have hl : Y.level u.val.length = X.level j := by
    rw [level_eq_length]
    exact congrArg List.length he
  calc
    Y.map u = X.map (criticalNode j) := he
    _ = critical (X.level j) := X.critical_image j
    _ = critical (Y.level u.val.length) := congrArg critical hl.symm
    _ = Y.map (criticalNode u.val.length) := (Y.critical_image _).symm

theorem pullNode_phase (X Y : CriticalMap) (j : Nat)
    (h : X.map (criticalNode j) ∈ copyRange Y) :
    (pullNode X Y (criticalNode j)).val.length % 3 = 2 ↔ j % 3 = 2 := by
  let u := pullNode X Y (criticalNode j)
  have he := pullNode_spec X Y (criticalNode j) h
  have hl : Y.level u.val.length = X.level j := by
    rw [level_eq_length]
    exact congrArg List.length he
  have hy := (Y.phase u.val.length).symm
  change u.val.length % 3 = 2 ↔ Y.level u.val.length % 3 = 2 at hy
  rw [hl] at hy
  exact hy.trans (X.phase j)

theorem pullNode_step (X Y : CriticalMap) (s : Word) (a : Fin 3)
    (hs : Tree (s ++ [a]))
    (hu : X.map (parentNode s a hs) ∈ copyRange Y)
    (hv : X.map ⟨s ++ [a],hs⟩ ∈ copyRange Y) :
    ∃ p : Word, (pullNode X Y ⟨s ++ [a],hs⟩).val =
      (pullNode X Y (parentNode s a hs)).val ++ a :: p ∧
      (a ≠ 1 → Binary p) := by
  let u := pullNode X Y (parentNode s a hs)
  let v := pullNode X Y ⟨s ++ [a],hs⟩
  obtain ⟨p,hp,hb⟩ := X.step s a hs
  have he : (total Y).map v.val = (total Y).map u.val ++ a :: p := by
    rw [total_agrees Y v,total_agrees Y u]
    change Y.map (pullNode X Y ⟨s ++ [a],hs⟩) =
      Y.map (pullNode X Y (parentNode s a hs)) ++ a :: p
    rw [pullNode_spec X Y _ hv,pullNode_spec X Y _ hu]
    exact hp
  exact (total Y).reflect_edge he hb

/-- The manuscript's finite critical embedding conditions, before assuming
any extension to an infinite critical map. Values outside height h are
irrelevant and are not part of an approximation. -/
structure FiniteCritical (h : Nat) where
  map : Node → Word
  level_strict : ∀ {i j}, i < j → j < h →
    (map (criticalNode i)).length < (map (criticalNode j)).length
  length_map : ∀ u : Node, u.val.length < h →
    (map u).length = (map (criticalNode u.val.length)).length
  step : ∀ s a (hs : Tree (s ++ [a])), (s ++ [a]).length < h →
    ∃ p : Word, map ⟨s ++ [a],hs⟩ = map (parentNode s a hs) ++ a :: p ∧
      (a ≠ 1 → Binary p)
  maps_tree : ∀ u, u.val.length < h → Tree (map u)
  critical_image : ∀ j, j < h → map (criticalNode j) =
    critical ((map (criticalNode j)).length)
  phase : ∀ j, j < h → ((map (criticalNode j)).length % 3 = 2 ↔ j % 3 = 2)

def FiniteCritical.level {h : Nat} (e : FiniteCritical h) (j : Nat) : Nat :=
  (e.map (criticalNode j)).length

def Extends {h : Nat} (X : CriticalMap) (e : FiniteCritical h) : Prop :=
  ∀ u : Node, u.val.length < h → X.map u = e.map u

def restrictCritical (X : CriticalMap) (h : Nat) : FiniteCritical h where
  map := X.map
  level_strict := fun hij _ => X.level_strict hij
  length_map := fun u _ => X.length_map u
  step := fun s a hs _ => X.step s a hs
  maps_tree := fun u _ => X.maps_tree u
  critical_image := fun j _ => X.critical_image j
  phase := fun j _ => X.phase j

/-- Finite pullback with only the containment of the prescribed finite
domain, not containment of the whole realizing copy. -/
noncomputable def pullFinite (X Y : CriticalMap) (h : Nat)
    (hsub : ∀ u : Node, u.val.length < h → X.map u ∈ copyRange Y) :
    FiniteCritical h where
  map u := (pullNode X Y u).val
  level_strict := by
    intro i j hij hj
    apply pullNode_length_strict
    · exact hsub (criticalNode i) (by simp; omega)
    · exact hsub (criticalNode j) (by simpa using hj)
    · simpa using hij
  length_map := by
    intro u hu
    exact pullNode_length_map X Y u (criticalNode u.val.length)
      (hsub u hu) (hsub _ (by simpa using hu)) (criticalNode_length _).symm
  step := by
    intro s a hs hlen
    exact pullNode_step X Y s a hs
      (hsub _ (by change s.length < h; simp at hlen; omega))
      (hsub _ hlen)
  maps_tree := fun u _ => (pullNode X Y u).property
  critical_image := by
    intro j hj
    exact congrArg Subtype.val (pullNode_critical X Y j (hsub _ (by simpa using hj)))
  phase := fun j hj => pullNode_phase X Y j (hsub _ (by simpa using hj))

/-- The infinite pullback is a genuine critical map. -/
noncomputable def pull (X Y : CriticalMap) (hsub : copyRange X ⊆ copyRange Y) :
    CriticalMap where
  map u := (pullNode X Y u).val
  level_strict := by
    intro i j hij
    exact pullNode_length_strict X Y _ _
      (hsub ⟨_,rfl⟩) (hsub ⟨_,rfl⟩) (by simpa using hij)
  length_map := by
    intro u
    exact pullNode_length_map X Y u (criticalNode u.val.length)
      (hsub ⟨_,rfl⟩) (hsub ⟨_,rfl⟩) (criticalNode_length _).symm
  step := fun s a hs => pullNode_step X Y s a hs (hsub ⟨_,rfl⟩) (hsub ⟨_,rfl⟩)
  maps_tree := fun u => (pullNode X Y u).property
  critical_image := fun j => congrArg Subtype.val (pullNode_critical X Y j (hsub ⟨_,rfl⟩))
  phase := fun j => pullNode_phase X Y j (hsub ⟨_,rfl⟩)

theorem compose_pull (X Y : CriticalMap) (hsub : copyRange X ⊆ copyRange Y) :
    compose Y (pull X Y hsub) = X := by
  apply CriticalMap.ext
  funext u
  exact pullNode_spec X Y u (hsub ⟨u,rfl⟩)

/-- Range inclusion and actual factorization coincide. -/
theorem le_iff_factor (X Y : CriticalMap) :
    copyRange X ⊆ copyRange Y ↔ ∃ Z, compose Y Z = X := by
  constructor
  · intro h
    exact ⟨pull X Y h,compose_pull X Y h⟩
  · rintro ⟨Z,rfl⟩
    exact compose_le Y Z

/-- The exact remaining local extension statement for A.3(1). -/
def WholeBlockExtension : Prop :=
  ∀ (n : Nat) (e : FiniteCritical (3*n)), ∃ X : CriticalMap, Extends X e

/-- A.3(1) reduces to extension of finite critical maps at whole-gadget
boundaries. This is a reduction, not an assertion of the remaining
relative extension theorem. -/
theorem amalgamation_nonempty_of_extension (hext : WholeBlockExtension)
    {n d : Nat} (a : system.Approx n) (Y : CriticalMap)
    (hd : finitization.HasDepth a Y d)
    {Z : CriticalMap} (hZ : Z ∈ system.levelNeighborhood d Y) :
    (system.neighborhood a Z).Nonempty := by
  obtain ⟨X,hX⟩ := system.approx_surjective n a
  have hsub : ∀ u : Node, u.val.length < 3*n → X.map u ∈ copyRange Z := by
    intro u hu
    have hmem : X.map u ∈ finiteRange (system.finiteApprox n X) := ⟨⟨u,hu⟩,rfl⟩
    have hh := hd.1
    change finiteRange (⟨n,a⟩ : system.FiniteApprox) ⊆
      finiteRange (system.finiteApprox d Y) at hh
    have hm : X.map u ∈ finiteRange (⟨n,a⟩ : system.FiniteApprox) := by
      have hEq : system.finiteApprox n X = ⟨n,a⟩ := Sigma.ext rfl (heq_of_eq hX)
      rw [← hEq]
      exact hmem
    have hYZ : system.finiteApprox d Y = system.finiteApprox d Z :=
      Sigma.ext rfl (heq_of_eq hZ.2.symm)
    have hz := hh hm
    rw [hYZ] at hz
    obtain ⟨v,hv⟩ := hz
    exact ⟨v.val,hv⟩
  obtain ⟨W,hW⟩ := hext n (pullFinite X Z (3*n) hsub)
  refine ⟨compose Z W, compose_le Z W, ?_⟩
  change approx n (compose Z W) = a
  rw [← hX]
  apply approx_eq_iff.mpr
  intro u
  change Z.map (intoTree W u.val) = X.map u.val
  have hnode : intoTree W u.val = pullNode X Z u.val :=
    Subtype.ext (hW u.val u.property)
  rw [hnode]
  exact pullNode_spec X Z u.val (hsub u.val u.property)

end CriticalCopies
end AllThoseBigRamsey.Pseudotree
