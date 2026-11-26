import PseudotreeValidation.CriticalSupport

/-!
# The A.3(2) range argument, independently of the reservoir implementation

The only remaining construction consumed by this module is a support
condition for a critical map fixing a whole-block prefix: at a level
whose critical vertex belongs to a relevant slot, every vertex of
that level in a relevant slot maps into the prescribed target copy.
This is exactly what the relative reservoir witnesses imply.
-/
namespace AllThoseBigRamsey.Pseudotree.CriticalCopies
open RayEmbeddings
open SparseNormalization (critical critical_length tree_prefix)

@[simp] theorem identity_level (j : Nat) : identity.level j = j :=
  criticalNode_length j

@[simp] theorem compose_level (Y X : CriticalMap) (j : Nat) :
    (compose Y X).level j = Y.level (X.level j) := by
  change (Y.map (intoTree X (criticalNode j))).length = _
  rw [intoTree_critical]
  rfl

theorem compose_assoc (Y X Z : CriticalMap) :
    compose (compose Y X) Z = compose Y (compose X Z) := by
  apply CriticalMap.ext
  funext u
  rfl

/-- The slots determined by the last level of the prescribed approximation. -/
def Relevant (X : CriticalMap) (n : Nat) (w : Word) : Prop :=
  ∃ u : Node, u.val.length = 3*n-1 ∧
    ∃ a : Fin 3, SparseNormalization.Tree (u.val ++ [a]) ∧
      (X.map u ++ [a]).IsPrefix w

theorem relevant_length {X : CriticalMap} {n d : Nat}
    (hd : 0 < d) (htop : X.level (3*n-1) = 3*d-1)
    {w : Word} (hw : Relevant X n w) : 3*d ≤ w.length := by
  obtain ⟨u,hu,a,_,hp⟩ := hw
  have hl := hp.length_le
  rw [List.length_append,List.length_singleton,← level_eq_length X u,hu,htop] at hl
  omega

theorem relevant_append_iff {X : CriticalMap} {n d : Nat}
    (hd : 0 < d) (htop : X.level (3*n-1) = 3*d-1)
    {w : Word} (hw : 3*d ≤ w.length) (a : Fin 3) :
    Relevant X n (w ++ [a]) ↔ Relevant X n w := by
  constructor
  · rintro ⟨u,hu,b,hb,hpre⟩
    have hl : (X.map u ++ [b]).length ≤ w.length := by
      rw [List.length_append,List.length_singleton,← level_eq_length X u,hu,htop]
      omega
    exact ⟨u,hu,b,hb,List.prefix_of_prefix_length_le hpre (List.prefix_append _ _) hl⟩
  · rintro ⟨u,hu,b,hb,hpre⟩
    exact ⟨u,hu,b,hb,hpre.trans (List.prefix_append _ _)⟩

/-- Every future node of a map agreeing on the initial approximation
extends a relevant slot. No constraint is needed on its later padding. -/
theorem relevant_of_agrees (X H : CriticalMap) {n : Nat} (hn : 0 < n)
    (ha : ∀ u : Node, u.val.length < 3*n → H.map u = X.map u)
    (u : Node) (hu : 3*n ≤ u.val.length) :
    Relevant X n (H.map u) := by
  let k := 3*n-1
  have hk : k < u.val.length := by dsimp [k]; omega
  let p : Node := ⟨u.val.take k,tree_prefix u.property (List.take_prefix _ _)⟩
  let a := u.val[k]
  have hpLen : p.val.length = k := by simp [p,Nat.min_eq_left hk.le]
  have hchild : SparseNormalization.Tree (p.val ++ [a]) := by
    change SparseNormalization.Tree (u.val.take k ++ [u.val[k]])
    rw [List.take_append_getElem hk]
    exact tree_prefix u.property (List.take_prefix _ _)
  have hform : u.val = p.val ++ a :: u.val.drop (k+1) := by
    change u.val = u.val.take k ++ u.val[k] :: u.val.drop (k+1)
    simpa only [List.drop_eq_getElem_cons hk] using (List.take_append_drop k u.val).symm
  obtain ⟨q,hq⟩ := (total H).map_append_cons p.val a (u.val.drop (k+1))
  rw [← hform,total_agrees H u,total_agrees H p,ha p (by rw [hpLen]; dsimp [k]; omega)] at hq
  refine ⟨p,hpLen,a,hchild,?_⟩
  exact ⟨q,by simpa only [List.append_assoc,List.singleton_append] using hq.symm⟩

theorem length_le_last (X : CriticalMap) {n d : Nat} (hn : 0 < n)
    (htop : X.level (3*n-1) = 3*d-1) (hd : 0 < d)
    (u : Node) (hu : u.val.length < 3*n) :
    (X.map u).length < 3*d := by
  have hle : (X.map u).length ≤ X.level (3*n-1) :=
    image_length_le_top X hn ⟨u,hu⟩
  omega

/-- The precise local output needed from relative reservoirs. -/
def RelativeSupport (X Z : CriticalMap) (n d : Nat) : Prop :=
  (∀ u : Node, u.val.length < 3*d → Z.map u = u.val) ∧
  ∀ u : Node, 3*d ≤ u.val.length → Relevant X n u.val →
    Relevant X n (critical u.val.length) → Z.map u ∈ copyRange X

/-- The abstract-free geometric core of A.3(2). The whole-block prefix
is fixed, and the relative support property applies simultaneously to
a future node and its critical vertex. -/
theorem refinement_of_support {X Z W : CriticalMap} {n d : Nat}
    (hn : 0 < n) (hd : 0 < d) (htop : X.level (3*n-1) = 3*d-1)
    (hsupport : RelativeSupport X Z n d)
    (hWZ : copyRange W ⊆ copyRange Z) (hWa : approx n W = approx n X) :
    copyRange W ⊆ copyRange X := by
  let H := pull W Z hWZ
  have hfactor : compose Z H = W := compose_pull W Z hWZ
  have hW (u : Node) : Z.map (intoTree H u) = W.map u :=
    congrArg (fun F : CriticalMap => F.map u) hfactor
  have hH (u : Node) (hu : u.val.length < 3*n) : H.map u = X.map u := by
    have hfix : Z.map (intoTree X u) = X.map u :=
      hsupport.1 _ (length_le_last X hn htop hd u hu)
    have hWu := approx_eq_iff.mp hWa ⟨u,hu⟩
    have he : Z.map (intoTree H u) = Z.map (intoTree X u) :=
      (hW u).trans (hWu.trans hfix.symm)
    exact congrArg Subtype.val (map_injective Z he)
  have hHtop : H.level (3*n-1) = 3*d-1 := by
    have he := hH (criticalNode (3*n-1)) (by simp; omega)
    exact (congrArg List.length he).trans htop
  rintro w ⟨u,rfl⟩
  by_cases hu : u.val.length < 3*n
  · exact ⟨u, (approx_eq_iff.mp hWa ⟨u,hu⟩).symm⟩
  · have htail : 3*n ≤ u.val.length := by omega
    have hl : 3*d ≤ (H.map u).length := by
      have hlt : H.level (3*n-1) < H.level u.val.length :=
        H.level_strict (by omega)
      rw [hHtop,level_eq_length H u] at hlt
      omega
    have hr := relevant_of_agrees X H hn hH u htail
    have hc := relevant_of_agrees X H hn hH (criticalNode u.val.length)
      (by simpa using htail)
    rw [H.critical_image,← H.length_map u] at hc
    have hmem := hsupport.2 (intoTree H u) hl hr hc
    rw [hW u] at hmem
    exact hmem

/-- The remaining reservoir construction is stated as a proposition,
not installed as an axiom or typeclass. -/
def RelativeSupportConstruction : Prop :=
  ∀ X : CriticalMap, ∀ n d : Nat, 0 < n → 0 < d →
    X.level (3*n-1) = 3*d-1 →
    ∃ Z : CriticalMap, RelativeSupport X Z n d

/-- Transport the local range argument through an arbitrary ambient
critical copy, obtaining the actual upstream A.3(2) formulation.
This reduction has just the explicit RelativeSupportConstruction premise. -/
theorem amalgamation_refine_of_support (hconstruct : RelativeSupportConstruction)
    {n d : Nat} (a : system.Approx n) (Y : CriticalMap)
    (hd : finitization.HasDepth a Y d)
    {A : CriticalMap} (hAY : system.le A Y)
    (hne : (system.neighborhood a A).Nonempty) :
    ∃ A', A' ∈ system.levelNeighborhood d Y ∧
      system.neighborhood a A' ⊆ system.neighborhood a A := by
  by_cases hn : n = 0
  · subst n
    have ha : a = approx 0 Y := by
      obtain ⟨W,hW⟩ := system.approx_surjective 0 a
      exact hW.symm.trans ((system.approx_zero W).trans (system.approx_zero Y).symm)
    have hzero : finitization.leFin ⟨0,a⟩ (system.finiteApprox 0 Y) := by
      rw [ha]
      exact finitization.leFin_refl _
    have hd0 : d = 0 := by
      by_contra h
      exact (hd.2 0 (by omega)) hzero
    subst d
    refine ⟨A,⟨hAY,?_⟩,fun _ h => h⟩
    exact (system.approx_zero A).trans (system.approx_zero Y).symm
  · have hnpos : 0 < n := by omega
    obtain ⟨X0,hX0⟩ := hne
    have hX0Y : copyRange X0 ⊆ copyRange Y := hX0.1.trans hAY
    let X := pull X0 Y hX0Y
    have hX : compose Y X = X0 := compose_pull X0 Y hX0Y
    have hd' : finitization.HasDepth (approx n X0) Y d := by
      change finitization.HasDepth (system.approx n X0) Y d
      rw [hX0.2]
      exact hd
    obtain ⟨hdpos,hdepth⟩ := depth_top X0 Y hnpos hd'
    have htop : X.level (3*n-1) = 3*d-1 := by
      apply Y.level_strict.injective
      change Y.level (X.level (3*n-1)) = Y.level (3*d-1)
      rw [← compose_level Y X,hX]
      exact hdepth
    obtain ⟨Z,hZ⟩ := hconstruct X n d hnpos hdpos htop
    refine ⟨compose Y Z,⟨compose_le Y Z,?_⟩,?_⟩
    · change approx d (compose Y Z) = approx d Y
      apply approx_eq_iff.mpr
      intro u
      change Y.map (intoTree Z u.val) = Y.map u.val
      have he : intoTree Z u.val = u.val := Subtype.ext (hZ.1 u.val u.property)
      rw [he]
    · intro W hW
      have hWle : copyRange W ⊆ copyRange (compose Y Z) := hW.1
      let U := pull W (compose Y Z) hWle
      let V := compose Z U
      have hV : compose Y V = W := by
        change compose Y (compose Z U) = W
        rw [← compose_assoc]
        exact compose_pull W (compose Y Z) hWle
      have hVa : approx n V = approx n X := by
        apply approx_eq_iff.mpr
        intro u
        have hv := congrArg (fun F : CriticalMap => F.map u.val) hV
        have hx := congrArg (fun F : CriticalMap => F.map u.val) hX
        have hw := approx_eq_iff.mp (hW.2.trans hX0.2.symm) u
        have he : Y.map (intoTree V u.val) = Y.map (intoTree X u.val) :=
          hv.trans (hw.trans hx.symm)
        exact congrArg Subtype.val (map_injective Y he)
      have hVX := refinement_of_support hnpos hdpos htop hZ (compose_le Z U) hVa
      refine ⟨?_,hW.2⟩
      change copyRange W ⊆ copyRange A
      rintro w ⟨u,rfl⟩
      obtain ⟨v,hv⟩ := hVX ⟨u,rfl⟩
      have he : intoTree X v = intoTree V u := Subtype.ext hv
      have hx := congrArg (fun F : CriticalMap => F.map v) hX
      have hw := congrArg (fun F : CriticalMap => F.map u) hV
      have hmem : W.map u = X0.map v := by
        calc
          W.map u = Y.map (intoTree V u) := hw.symm
          _ = Y.map (intoTree X v) := congrArg Y.map he.symm
          _ = X0.map v := hx
      exact hX0.1 ⟨v,hmem.symm⟩

end AllThoseBigRamsey.Pseudotree.CriticalCopies
