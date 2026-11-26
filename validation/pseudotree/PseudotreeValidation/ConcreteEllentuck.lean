import PseudotreeValidation.LocalPigeonhole
import PseudotreeValidation.RelevantReservoirs

/-! The concrete A.4 field and the assembly of the abstract theorem.
Colours on actual next approximations are pulled back through the
ambient critical map. No extra homogeneous-copy or extension premise
remains in the statement of the topological Ramsey-space endpoint. -/

namespace AllThoseBigRamsey.Pseudotree.CriticalCopies
open RayEmbeddings
open SparseNormalization (critical)

theorem pigeonhole {n d : Nat} (a : system.Approx n) (Y : CriticalMap)
    (hd : finitization.HasDepth a Y d) (O : Set (system.Approx (n+1))) :
    ∃ A : CriticalMap, A ∈ system.levelNeighborhood d Y ∧
      (system.oneStepApproximations a A ⊆ O ∨
       system.oneStepApproximations a A ⊆ Oᶜ) := by
  classical
  obtain ⟨X0,hX0⟩ := amalgamation_nonempty a Y hd (system.self_mem_levelNeighborhood d Y)
  have hX0Y : copyRange X0 ⊆ copyRange Y := hX0.1
  have hX0a : approx n X0 = a := hX0.2
  let X := pull X0 Y hX0Y
  have hX : compose Y X = X0 := compose_pull X0 Y hX0Y
  let colour (U : CriticalMap) : Fin 2 :=
    if approx (n+1) (compose Y U) ∈ O then 0 else 1
  have hcolour (U V : CriticalMap) (h : approx (n+1) U = approx (n+1) V) :
      colour U = colour V := by
    have hUV : approx (n+1) (compose Y U) = approx (n+1) (compose Y V) := by
      apply approx_eq_iff.mpr
      intro u
      have he : intoTree U u.val = intoTree V u.val :=
        Subtype.ext (approx_eq_iff.mp h u)
      change Y.map (intoTree U u.val) = Y.map (intoTree V u.val)
      rw [he]
    simp only [colour,hUV]
  have hlocal : ∃ Z : CriticalMap,
      (∀ u : Node, u.val.length < 3*d → Z.map u = u.val) ∧
      ∃ c : Fin 2, ∀ H : CriticalMap, approx n (compose Z H) = approx n X →
        colour (compose Z H) = c := by
    by_cases hn : n = 0
    · subst n
      have ha : a = approx 0 Y := by
        exact hX0a.symm.trans ((system.approx_zero X0).trans (system.approx_zero Y).symm)
      have hd0 : d = 0 := by
        by_contra h
        apply hd.2 0 (by omega)
        rw [ha]
        exact finitization.leFin_refl _
      subst d
      obtain ⟨Z,c,hZ⟩ := absolute_next_colour colour hcolour
      exact ⟨Z,fun u hu => False.elim (by omega),c,fun H _ => hZ H⟩
    · have hnpos : 0 < n := by omega
      have hd' : finitization.HasDepth (approx n X0) Y d := by
        rw [hX0a]
        exact hd
      obtain ⟨hdpos,hdepth⟩ := depth_top X0 Y hnpos hd'
      have htop : X.level (3*n-1) = 3*d-1 := by
        apply Y.level_strict.injective
        change Y.level (X.level (3*n-1)) = Y.level (3*d-1)
        rw [← compose_level Y X,hX]
        exact hdepth
      exact relative_next_colour X hnpos hdpos htop colour hcolour
  obtain ⟨Z,hZ,c,hmono⟩ := hlocal
  let A := compose Y Z
  have hA : A ∈ system.levelNeighborhood d Y := by
    refine ⟨compose_le Y Z,?_⟩
    change approx d A = approx d Y
    apply approx_eq_iff.mpr
    intro u
    have he : intoTree Z u.val = u.val := Subtype.ext (hZ u.val u.property)
    change Y.map (intoTree Z u.val) = Y.map u.val
    rw [he]
  have hstep (b : system.Approx (n+1)) (hb : b ∈ system.oneStepApproximations a A) :
      (if b ∈ O then (0 : Fin 2) else 1) = c := by
    obtain ⟨W,hW,hb⟩ := hb
    have hWA : copyRange W ⊆ copyRange A := hW.1
    let H := pull W A hWA
    have hH : compose Y (compose Z H) = W := by
      rw [← compose_assoc]
      exact compose_pull W A hWA
    have he : approx n (compose Z H) = approx n X := by
      apply approx_eq_iff.mpr
      intro u
      have hw := approx_eq_iff.mp (show approx n W = approx n X0 from
        hW.2.trans hX0a.symm) u
      have h₁ := congrArg (fun V : CriticalMap => V.map u.val) hH
      have h₂ := congrArg (fun V : CriticalMap => V.map u.val) hX
      have he' : Y.map (intoTree (compose Z H) u.val) = Y.map (intoTree X u.val) :=
        h₁.trans (hw.trans h₂.symm)
      exact congrArg Subtype.val (map_injective Y he')
    have hm := hmono H he
    change (if approx (n+1) (compose Y (compose Z H)) ∈ O then (0 : Fin 2) else 1) = c at hm
    rw [hH,show approx (n+1) W = b from hb] at hm
    exact hm
  refine ⟨A,hA,?_⟩
  by_cases hc : c = 0
  · left
    intro b hb
    by_contra h
    have hm := hstep b hb
    simp [h,hc] at hm
  · right
    intro b hb
    change b ∉ O
    intro h
    have hm := hstep b hb
    simp only [if_pos h] at hm
    exact hc hm.symm

/-- The actual A.1--A.4 package on critical copies of R. -/
noncomputable def ramseySpace : RamseySpace.AbstractRamseySpace system :=
  RamseySpace.AbstractRamseySpace.ofPublishedAxioms finitization
    amalgamation_nonempty amalgamation_refine pigeonhole

/-- Concrete Ellentuck theorem in the exact published abstract interface.
Transfer to the expanded-copy topology is a separate identification. -/
theorem concrete_ellentuck :
    RamseySpace.IsTopologicalRamseySpaceTextbook (S := system) :=
  ellentuck_of_axioms ramseySpace

end AllThoseBigRamsey.Pseudotree.CriticalCopies
