import PseudotreeValidation.RayMilliken

/-!
# Relative restricted Milliken

The existing fibre fusion starts at zero. Starting at a prescribed
ambient height instead preserves the entire fixed lower embedding.
The height induction can therefore stop at any nonempty initial
segment, rather than at a singleton root. In particular this yields
the synchronized forest theorem above a fixed finite prefix.

No new Halpern–Läuchli input is used.
-/

namespace AllThoseBigRamsey.Pseudotree.RayMilliken
open RayEmbeddings
variable {F G : Shape} {κ : Type}

/-- Fusion beginning at a prescribed ambient level. All lower levels
are fixed, and every extension fibre with top at least that level is
homogenized. -/
theorem all_fibres_fusion_above (hGF : G.nodes ⊆ F.nodes) (b : Nat)
    (localStep : ∀ (colour : Embedding F → κ) (e' : Embedding G) (j : ℕ),
      e'.topLevel = j →
      ∃ h : RayStrongMap, FixesThrough j h ∧ FibreConstant hGF (induced colour h) e')
    (colour : Embedding F → κ) :
    ∃ h : RayStrongMap, FixesThrough b h ∧
      ∀ e' : Embedding G, b ≤ e'.topLevel →
        FibreConstant hGF (induced colour h) e' := by
  classical
  have batches := fun j c => all_fibres_at_level hGF j
    (fun c e' he' => localStep c e' j he') c
  let step (j : ℕ) (f : RayStrongMap) : RayStrongMap :=
    if b ≤ j then (batches j (induced colour f)).choose else RayStrongMap.identity
  have stepfix (j : ℕ) (f : RayStrongMap) : FixesThrough j (step j f) := by
    by_cases hj : b ≤ j
    · simpa only [step,if_pos hj] using (batches j (induced colour f)).choose_spec.1
    · simp only [step,if_neg hj]
      exact fun _ _ => rfl
  have stepfixBase (j : ℕ) (f : RayStrongMap) : FixesThrough b (step j f) := by
    by_cases hj : b ≤ j
    · exact fun s hs => stepfix j f s (hs.trans hj)
    · simp only [step,if_neg hj]
      exact fun _ _ => rfl
  have stepcolour (j : ℕ) (hj : b ≤ j) (f : RayStrongMap)
      (e' : Embedding G) (he' : e'.topLevel = j) :
      FibreConstant hGF (induced colour (f.comp (step j f))) e' := by
    simpa only [step,if_pos hj,induced_comp] using
      (batches j (induced colour f)).choose_spec.2 e' he'
  let totals : ℕ → RayStrongMap :=
    Nat.rec RayStrongMap.identity (fun j f => f.comp (step j f))
  let increments : ℕ → RayStrongMap :=
    fun n => match n with
    | 0 => RayStrongMap.identity
    | j+1 => step j (totals j)
  have htotals (j : ℕ) : RayStrongMap.compositions increments j = totals j := by
    induction j with
    | zero => rfl
    | succ j ih =>
      change (RayStrongMap.compositions increments j).comp (step j (totals j)) =
        (totals j).comp (step j (totals j))
      rw [ih]
  have htotalsFix (j : Nat) : FixesThrough b (totals j) := by
    induction j with
    | zero => exact fun _ _ => rfl
    | succ j ih => exact fixes_comp ih (stepfixBase j (totals j))
  have hfix : ∀ j (s : Word), s.length ≤ j → (increments (j+1)).map s = s :=
    fun j s hs => stepfix j (totals j) s hs
  let limit := RayStrongMap.fusion increments hfix
  refine ⟨limit,?_,?_⟩
  · intro s hs
    obtain ⟨tail,htail,hfactor⟩ := RayStrongMap.fusion_factors increments hfix b
    rw [hfactor s,htail s hs,htotals b]
    exact htotalsFix b s hs
  · intro e' he'
    let j := e'.topLevel
    have hstage : FibreConstant hGF (induced colour (totals (j+1))) e' :=
      stepcolour j he' (totals j) e' rfl
    obtain ⟨tail,htail,hfactor⟩ := RayStrongMap.fusion_factors increments hfix (j+1)
    have htailfix : FixesThrough j tail := fun s hs => htail s (by omega)
    have hpres := fibreConstant_comp hGF (induced colour (totals (j+1))) e' j
      hstage tail htailfix le_rfl
    have hemb (e : Embedding F) :
        Embedding.comp limit e = Embedding.comp (totals (j+1)) (Embedding.comp tail e) := by
      apply Embedding.ext
      funext s
      change limit.map (e s) = (totals (j+1)).map (tail.map (e s))
      exact (hfactor (e s)).trans
        (congrArg (fun f : RayStrongMap => f.map (tail.map (e s))) (htotals (j+1)))
    intro e₁ e₂ h₁ h₂
    change colour (Embedding.comp limit e₁) = colour (Embedding.comp limit e₂)
    rw [hemb,hemb]
    exact hpres e₁ e₂ h₁ h₂

/-- If a lower shape is an initial truncation, the image of its top
node is no higher than the top of any embedding of the larger shape. -/
theorem restriction_top_le {F G : Shape} (hGF : G.nodes ⊆ F.nodes)
    (e : Embedding F) :
    (e.restrict G hGF).topLevel ≤ e.topLevel := by
  exact e.length_bounded ⟨G.topNode.val,hGF G.topNode.property⟩

/-- Work with arbitrary initial subshapes rather than dependent
equalities between nested truncations. -/
def InitialShape (G F : Shape) : Prop :=
  G.nodes ⊆ F.nodes ∧ ∀ s ∈ F.nodes, s ∈ G.nodes ↔ s.length < G.height

theorem truncate_initial (F : Shape) (k : Nat) (hk : 0 < k) (hF : k ≤ F.height) :
    InitialShape (F.truncate k hk) F := by
  refine ⟨F.truncate_subset k hk,?_⟩
  intro s hs
  rw [F.truncate_height k hk hF,F.mem_truncate]
  exact ⟨fun h => h.2,fun h => ⟨hs,h⟩⟩

theorem initial_height_le {G F : Shape} (hGF : InitialShape G F) :
    G.height ≤ F.height := by
  have h := F.length_lt_height G.topNode.val (hGF.1 G.topNode.property)
  rw [G.topNode_length] at h
  have := G.height_pos
  omega

/-- Relative restricted Milliken for any fixed initial subshape,
including the whole shape. The maps fix the entire ambient prefix
through the top image of the initial embedding. -/
theorem restricted_milliken_relative (F G : Shape) (hGF : InitialShape G F)
    {colours : Nat} (colour : Embedding F → Fin (colours+1)) (e₀ : Embedding G) :
    ∃ g : RayStrongMap, FixesThrough e₀.topLevel g ∧
      FibreConstant hGF.1 (induced colour g) e₀ := by
  classical
  generalize hN : F.height = N
  induction N using Nat.strong_induction_on generalizing F G with
  | h N ih =>
    have hle := initial_height_le hGF
    by_cases heq : G.height = F.height
    · refine ⟨RayStrongMap.identity,fun _ _ => rfl,?_⟩
      intro e₁ e₂ h₁ h₂
      rw [induced_identity]
      have h : e₁ = e₂ := by
        apply Embedding.ext
        funext s
        let t : G.Node := ⟨s.val,(hGF.2 s.val s.property).mpr
          (heq.symm ▸ F.length_lt_height s.val s.property)⟩
        exact congrArg (fun e : Embedding G => e t) (h₁.trans h₂.symm)
      rw [h]
    · let h := F.height-1
      have hh : 0 < h := by
        have := G.height_pos
        dsimp [h]
        omega
      have hF : F.height = h+1 := by dsimp [h]; omega
      let H := F.truncate h hh
      let inclusion := F.truncate_subset h hh
      have hH : H.height = h := F.truncate_height h hh (by omega)
      have hGH : InitialShape G H := by
        refine ⟨?_,?_⟩
        · intro s hs
          have hb := G.length_lt_height s hs
          exact (F.mem_truncate h hh s).mpr ⟨hGF.1 hs,by omega⟩
        · intro s hs
          exact hGF.2 s (inclusion hs)
      obtain ⟨g,hg,hgFibres⟩ := all_fibres_fusion_above inclusion e₀.topLevel
        (fun χ e' j he' => by
          obtain ⟨f,hf,hc⟩ := homogenize_fibre F h hh hF χ e'
          exact ⟨f,he' ▸ hf,hc⟩) colour
      let lift (e' : Embedding H) : Embedding F := Embedding.ofTotal F e'.realizer
      have hsection (e' : Embedding H) : (lift e').restrict H inclusion = e' := by
        apply Embedding.ext
        funext s
        exact e'.realizer_agrees s
      let χ (e' : Embedding H) := induced colour g (lift e')
      obtain ⟨f,hf,hmono⟩ := ih H.height (by rw [hH]; omega) H G hGH χ e₀ rfl
      refine ⟨g.comp f,fixes_comp hg hf,?_⟩
      intro e₁ e₂ h₁ h₂
      have hlow (e : Embedding F) (he : e.restrict G hGF.1 = e₀) :
          induced colour (g.comp f) e = induced χ f (e.restrict H inclusion) := by
        let E := Embedding.comp f e
        let e' := E.restrict H inclusion
        have hrestr : e'.restrict G hGH.1 = e₀ := by
          change ((Embedding.comp f e).restrict H inclusion).restrict G hGH.1 = e₀
          rw [Embedding.restrict_trans,Embedding.restrict_comp]
          have hfix : e.restrict G (fun _ hs => inclusion (hGH.1 hs)) = e₀ := he
          rw [hfix]
          exact comp_fixed_embedding f hf e₀ le_rfl
        have hbound : e₀.topLevel ≤ e'.topLevel := by
          rw [← hrestr]
          exact restriction_top_le hGH.1 e'
        have hEq := hgFibres e' hbound E (lift e') rfl (hsection e')
        change induced colour (g.comp f) e = induced χ f (e.restrict H inclusion)
        rw [← induced_comp]
        change induced colour g E = induced colour g (lift (Embedding.comp f (e.restrict H inclusion)))
        rw [← Embedding.restrict_comp]
        exact hEq
      rw [hlow e₁ h₁,hlow e₂ h₂]
      apply hmono
      · rw [Embedding.restrict_trans]
        exact h₁
      · rw [Embedding.restrict_trans]
        exact h₂

/-- In particular, fixed-prefix embeddings of the height-k truncation
have monochromatic extensions of the full finite tree. -/
theorem fixed_prefix_milliken (F : Shape) (k : Nat) (hk : 0 < k)
    (hF : k ≤ F.height) {colours : Nat}
    (colour : Embedding F → Fin (colours+1))
    (e₀ : Embedding (F.truncate k hk)) :
    ∃ g : RayStrongMap, FixesThrough e₀.topLevel g ∧
      FibreConstant (F.truncate_subset k hk) (induced colour g) e₀ :=
  restricted_milliken_relative F (F.truncate k hk) (truncate_initial F k hk hF) colour e₀

end AllThoseBigRamsey.Pseudotree.RayMilliken
