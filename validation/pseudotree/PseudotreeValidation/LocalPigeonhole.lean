import PseudotreeValidation.SlotTransport
import PseudotreeValidation.CriticalAmalgamation

/-!
# Local next-approximation pigeonhole theorem

The colouring only sees the next whole-block approximation. The
absolute case is restricted Milliken; the nonempty-prefix case is
fixed-prefix Milliken followed by the exact relative FIFO comparison.
This module does not require the relative reservoir (A.3(2)) theorem.
-/
namespace AllThoseBigRamsey.Pseudotree.CriticalCopies
open RayEmbeddings RayMapModel RayMilliken
open SparseNormalization (critical critical_length tree_prefix)

namespace SlotFamily

/-- Use the canonical relative lift, so the induced colour needs no
choice of an infinite critical extension. -/
noncomputable def liftMap {j : Nat} {e : FiniteCritical (j+1)}
    (B : SlotFamily e) (G : SlotMaps j) : CriticalMap :=
  (B.relativeLabels G).extendCritical (by omega)

theorem liftMap_old {j : Nat} {e : FiniteCritical (j+1)}
    (B : SlotFamily e) (G : SlotMaps j) (u : Node) (hu : u.val.length < j+1) :
    (B.liftMap G).map u = e.map u :=
  (B.relativeLabels G).extends_prefix (by omega) u hu

theorem liftMap_tail {j : Nat} {e : FiniteCritical (j+1)}
    (B : SlotFamily e) (G : SlotMaps j) (u : Node) (hu : j+1 ≤ u.val.length) :
    (B.liftMap G).map u = (B.tailLabels G).liftWord u.val := by
  change (B.relativeLabels G).mapWord u = _
  simp only [RelativeLabels.mapWord,if_neg (Nat.not_lt_of_ge hu),relativeLabels]

/-- Equality of label assignments on a whole block suffices to compare
the actual lifted approximation. This includes the critical label
automatically, since the critical node is part of that block. -/
theorem liftMap_approx_eq {j : Nat} {e : FiniteCritical (j+1)}
    (B : SlotFamily e) (G H : SlotMaps j) (m : Nat)
    (hlabels : ∀ u : Node, j+1 ≤ u.val.length → u.val.length < 3*m →
      B.labelsMap G u.val = B.labelsMap H u.val) :
    approx m (B.liftMap G) = approx m (B.liftMap H) := by
  apply approx_eq_iff.mpr
  intro u
  by_cases hu : u.val.val.length < j+1
  · rw [B.liftMap_old G _ hu,B.liftMap_old H _ hu]
  · have ht : j+1 ≤ u.val.val.length := by omega
    rw [B.liftMap_tail G _ ht,B.liftMap_tail H _ ht]
    have h1 := hlabels u.val ht u.property
    have h2 := hlabels (criticalNode u.val.val.length) (by simpa using ht)
      (by simpa using u.property)
    change B.labelsMap G (critical u.val.val.length) =
      B.labelsMap H (critical u.val.val.length) at h2
    unfold TailLabels.liftWord TailLabels.label
    change (Sparse.FIFO.liftedNode ((B.labelsMap G u.val.val).map toLetter)
      ((B.labelsMap G (critical u.val.val.length)).map toLetter)
      (decide (u.val.val.length % 3 ≠ 2))).map toFin =
      (Sparse.FIFO.liftedNode ((B.labelsMap H u.val.val).map toLetter)
      ((B.labelsMap H (critical u.val.val.length)).map toLetter)
      (decide (u.val.val.length % 3 ≠ 2))).map toFin
    rw [h1,h2]

theorem labelsMap_ofStrong {n : Nat} (hn : 0 < n)
    {e : FiniteCritical ((3*n-1)+1)} (B : SlotFamily e)
    (f : RayStrongMap) (hf : FixesBlock f n)
    (u : Node) (hu : (3*n-1)+1 ≤ u.val.length) :
    B.labelsMap (slotMapsOfStrong hn f hf) u.val =
      B.root (boundaryOf u.val u.property hu) ++
        (f.map u.val).drop ((3*n-1)+1) := by
  rw [B.labelsMap_eq _ u.property hu]
  let w := boundaryOf u.val u.property hu
  change B.root w ++
    (f.map (w.val ++ u.val.drop ((3*n-1)+1))).drop w.val.length = _
  change B.root w ++
    (f.map (u.val.take ((3*n-1)+1) ++ u.val.drop ((3*n-1)+1))).drop w.val.length =
    B.root w ++ (f.map u.val).drop ((3*n-1)+1)
  rw [List.take_append_drop,w.property.2]

/-- For fixed-prefix strong maps, the induced next approximation
depends only on their values on the finite next-block shape. -/
theorem liftStrong_approx_eq {n : Nat} (hn : 0 < n)
    {e : FiniteCritical ((3*n-1)+1)} (B : SlotFamily e)
    (f g : RayStrongMap) (hf : FixesBlock f n) (hg : FixesBlock g n)
    (heq : ∀ u : Node, u.val.length < 3*(n+1) → f.map u.val = g.map u.val) :
    approx (n+1) (B.liftMap (slotMapsOfStrong hn f hf)) =
      approx (n+1) (B.liftMap (slotMapsOfStrong hn g hg)) := by
  apply B.liftMap_approx_eq
  intro u hu hlen
  rw [B.labelsMap_ofStrong hn f hf u hu,B.labelsMap_ofStrong hn g hg u hu,heq u hlen]

/-- The map reconstructed from suffixes agrees locally with a composition
of suffix maps, even though its ordinary completion outside R can be
different. That off-domain freedom cannot affect the colour. -/
theorem labelsMap_of_composed_suffixes {n : Nat} (hn : 0 < n)
    {e : FiniteCritical ((3*n-1)+1)} (B : SlotFamily e)
    (g : RayStrongMap) (hg : FixesBlock g n)
    (K : SlotMaps (3*n-1)) (u : Node) (hu : (3*n-1)+1 ≤ u.val.length) :
    B.labelsMap ((slotMapsOfStrong hn g hg).comp K) u.val =
      B.labelsMap (slotMapsOfStrong hn (g.comp (suffixLift K).completion)
        (by
          intro v hv
          rw [RayStrongMap.comp_map,suffixLift_fixesBlock hn K v hv,hg v hv])) u.val := by
  let j := 3*n-1
  let w := boundaryOf u.val u.property hu
  let z := u.val.drop (j+1)
  let f := (suffixLift K).completion
  have hf : f.map u.val = w.val ++ (K.maps w).map z := by
    rw [suffixLift_agrees K u.val u.property,suffixLiftMap_eq K _ u.property hu]
  have hgf : FixesBlock (g.comp f) n := by
    intro v hv
    rw [RayStrongMap.comp_map,suffixLift_fixesBlock hn K v hv,hg v hv]
  rw [B.labelsMap_eq _ u.property hu,B.labelsMap_ofStrong hn (g.comp f) hgf u hu]
  change B.root w ++
    ((slotMapsOfStrong hn g hg).maps w).map ((K.maps w).map z) =
      B.root w ++ (g.map (f.map u.val)).drop (j+1)
  rw [hf,← slotMapsOfStrong_apply hn g hg w ((K.maps w).map z)]
  rw [List.drop_left' w.property.2]

end SlotFamily

/-- For a nonempty prescribed prefix, a fixed-prefix Milliken
colouring induces a homogeneous refinement of the ambient R. The
comparison lemma is used for the complete image of H, not just
a chosen finite approximation representative. -/
theorem relative_next_colour (X : CriticalMap) {n d : Nat} (hn : 0 < n) (hd : 0 < d)
    (htop : X.level (3*n-1) = 3*d-1)
    (colour : CriticalMap → Fin 2)
    (hcolour : ∀ U V : CriticalMap, approx (n+1) U = approx (n+1) V → colour U = colour V) :
    ∃ Z : CriticalMap, (∀ u : Node, u.val.length < 3*d → Z.map u = u.val) ∧
      ∃ c : Fin 2, ∀ H : CriticalMap, approx n (compose Z H) = approx n X →
        colour (compose Z H) = c := by
  classical
  let j := 3*n-1
  let k := 3*d-1
  have hj : j+1 = 3*n := by dsimp [j]; omega
  have hk : k+1 = 3*d := by dsimp [k]; omega
  let T : SlotTransport j k := {
    prefixMap := restrictCritical X (j+1)
    source_phase := by dsimp [j]; omega
    top := htop }
  obtain ⟨B⟩ := slotFamily_exists (restrictCritical identity (k+1))
    (by dsimp [k]; omega)
  let C := T.restrictRoots B
  let F := blockShape (n+1) (by omega)
  let χ (E : Embedding F) : Fin 2 :=
    if hE : FixesBlock E.realizer n then
      colour (C.liftMap (slotMapsOfStrong hn E.realizer hE))
    else 0
  have χ_agrees (f : RayStrongMap) (hf : FixesBlock f n) :
      χ (Embedding.ofTotal F f) = colour (C.liftMap (slotMapsOfStrong hn f hf)) := by
    let E := Embedding.ofTotal F f
    have heq (u : Node) (hu : u.val.length < 3*(n+1)) :
        E.realizer.map u.val = f.map u.val := by
      let s : F.Node := ⟨u.val,(mem_blockNodes _ _).mpr ⟨u.property,hu⟩⟩
      exact E.realizer_agrees s
    have hE : FixesBlock E.realizer n := by
      intro u hu
      rw [heq u (by omega),hf u hu]
    change χ E = _
    rw [χ,dif_pos hE]
    exact hcolour _ _ (C.liftStrong_approx_eq hn E.realizer f hE hf heq)
  obtain ⟨c,g,hg,_,hmono⟩ := next_block_milliken n χ
  let G := slotMapsOfStrong hn g hg
  let Z := B.liftMap (SlotMaps.transport T G)
  have hZ (u : Node) (hu : u.val.length < 3*d) : Z.map u = u.val := by
    exact B.liftMap_old _ u (by omega)
  refine ⟨Z,hZ,c,?_⟩
  intro H hH
  have he : Extends H T.prefixMap := by
    intro u hu
    have hx : (X.map u).length < 3*d :=
      length_le_last X hn htop hd u (by omega)
    have hfix : Z.map (intoTree X u) = X.map u := hZ _ hx
    have hEq := approx_eq_iff.mp hH ⟨u,by omega⟩
    change Z.map (intoTree H u) = X.map u at hEq
    exact congrArg Subtype.val (map_injective Z (hEq.trans hfix.symm))
  let K := T.suffixes H he
  let f := (suffixLift K).completion
  have hf : FixesBlock f n := suffixLift_fixesBlock hn K
  have hgf : FixesBlock (g.comp f) n := by
    intro u hu
    rw [RayStrongMap.comp_map,hf u hu,hg u hu]
  have hEq : approx (n+1) (compose Z H) =
      approx (n+1) (C.liftMap (G.comp K)) := by
    apply approx_eq_iff.mpr
    intro u
    change Z.map (intoTree H u.val) = (C.liftMap (G.comp K)).map u.val
    by_cases hu : u.val.val.length < j+1
    · have hH' : H.map u.val = X.map u.val := he u.val hu
      have hx := length_le_last X hn htop hd u.val (by omega : u.val.val.length < 3*n)
      have heq : intoTree H u.val = intoTree X u.val := Subtype.ext hH'
      rw [heq,hZ (intoTree X u.val) hx,C.liftMap_old _ _ hu]
      rfl
    · have htail : j+1 ≤ u.val.val.length := by omega
      have hl : k+1 ≤ (H.map u.val).length := by
        let w := boundaryOf u.val.val u.val.property htail
        have hform := T.suffixes_node H he u.val htail
        change H.map u.val = (T.inject w).val ++
          (K.maps w).map (u.val.val.drop (j+1)) at hform
        rw [hform,List.length_append,(T.inject w).property.2]
        omega
      rw [B.liftMap_tail _ _ hl,C.liftMap_tail _ _ htail]
      exact T.lift_comp B G H he u.val htail
  have hCompare : approx (n+1) (C.liftMap (G.comp K)) =
      approx (n+1) (C.liftMap (slotMapsOfStrong hn (g.comp f) hgf)) := by
    apply C.liftMap_approx_eq
    intro u hu _
    exact C.labelsMap_of_composed_suffixes hn g hg K u hu
  calc
    colour (compose Z H) = colour (C.liftMap (G.comp K)) := hcolour _ _ hEq
    _ = colour (C.liftMap (slotMapsOfStrong hn (g.comp f) hgf)) := hcolour _ _ hCompare
    _ = χ (Embedding.ofTotal F (g.comp f)) := (χ_agrees (g.comp f) hgf).symm
    _ = c := hmono f hf

/-- The empty-prefix comparison is the absolute analogue of the
relative locality equation. -/
theorem absolute_lift_comp (g : RayStrongMap) (H : CriticalMap) :
    compose (FIFOLifting.liftCritical g) H =
      FIFOLifting.liftCritical (g.comp (total H)) := by
  apply CriticalMap.ext
  funext u
  have hcrit : H.map (criticalNode u.val.length) = critical (H.map u).length := by
    rw [H.critical_image,← H.length_map u]
  have hphase : (H.map u).length % 3 = 2 ↔ u.val.length % 3 = 2 := by
    rw [H.length_map u]
    exact H.phase _
  have hs : decide ((H.map u).length % 3 ≠ 2) = decide (u.val.length % 3 ≠ 2) := by
    simp only [ne_eq,hphase]
  change FIFOLifting.liftWord FIFOLifting.sparseEvents g (H.map u) =
    FIFOLifting.liftWord FIFOLifting.sparseEvents (g.comp (total H)) u.val
  unfold FIFOLifting.liftWord FIFOLifting.label
  change (Sparse.FIFO.liftedNode ((g.map (H.map u)).map toLetter)
    ((g.map (critical (H.map u).length)).map toLetter)
    (decide ((H.map u).length % 3 ≠ 2))).map toFin =
    (Sparse.FIFO.liftedNode ((g.map ((total H).map u.val)).map toLetter)
      ((g.map ((total H).map (critical u.val.length))).map toLetter)
      (decide (u.val.length % 3 ≠ 2))).map toFin
  rw [total_agrees H u,show (total H).map (critical u.val.length) =
    H.map (criticalNode u.val.length) from total_agrees H (criticalNode u.val.length),
    hcrit,hs]

theorem absolute_approx_eq (f g : RayStrongMap) (m : Nat)
    (heq : ∀ u : Node, u.val.length < 3*m → f.map u.val = g.map u.val) :
    approx m (FIFOLifting.liftCritical f) = approx m (FIFOLifting.liftCritical g) := by
  apply approx_eq_iff.mpr
  intro u
  change FIFOLifting.liftWord FIFOLifting.sparseEvents f u.val.val =
    FIFOLifting.liftWord FIFOLifting.sparseEvents g u.val.val
  have hcrit := heq (criticalNode u.val.val.length) (by simpa using u.property)
  change f.map (critical u.val.val.length) = g.map (critical u.val.val.length) at hcrit
  unfold FIFOLifting.liftWord FIFOLifting.label
  change (Sparse.FIFO.liftedNode ((f.map u.val.val).map toLetter)
    ((f.map (critical u.val.val.length)).map toLetter)
    (decide (u.val.val.length % 3 ≠ 2))).map toFin =
    (Sparse.FIFO.liftedNode ((g.map u.val.val).map toLetter)
    ((g.map (critical u.val.val.length)).map toLetter)
    (decide (u.val.val.length % 3 ≠ 2))).map toFin
  rw [heq u.val u.property,hcrit]

theorem absolute_next_colour (colour : CriticalMap → Fin 2)
    (hcolour : ∀ U V : CriticalMap, approx 1 U = approx 1 V → colour U = colour V) :
    ∃ Z : CriticalMap, ∃ c : Fin 2, ∀ H : CriticalMap, colour (compose Z H) = c := by
  classical
  let F := blockShape 1 (by decide)
  let χ (E : Embedding F) := colour (FIFOLifting.liftCritical E.realizer)
  have hχ (f : RayStrongMap) : χ (Embedding.ofTotal F f) = colour (FIFOLifting.liftCritical f) := by
    apply hcolour
    apply absolute_approx_eq
    intro u hu
    let s : F.Node := ⟨u.val,(mem_blockNodes _ _).mpr ⟨u.property,hu⟩⟩
    exact (Embedding.ofTotal F f).realizer_agrees s
  obtain ⟨c,g,hmono⟩ := restricted_milliken F χ
  refine ⟨FIFOLifting.liftCritical g,c,?_⟩
  intro H
  rw [absolute_lift_comp,← hχ]
  exact hmono (Embedding.ofTotal F (total H))

end AllThoseBigRamsey.Pseudotree.CriticalCopies
