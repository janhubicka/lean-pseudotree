import PseudotreeValidation.FIFOLifting
import PseudotreeValidation.GeneralizedRecovery

/-!
# Finite-fragment canonization on the actual sparse coding set

This is the code-set form of IRT. The arbitrary finite family consists
of independent literal generalized diaries, possibly of different sizes.
The output is an actual critical self-map of R, not an assumed Ramsey
embedding. Recurrence inside arbitrary reduct self-copies and the
first-order expansion packaging are separate obligations.
-/

namespace AllThoseBigRamsey.Pseudotree
open RayEmbeddings
open SparseNormalization (Point Tree point_tree point_at_level critical)
namespace CriticalCopies

/-- Critical maps preserve coding points, without an extra model premise. -/
theorem maps_point (X : CriticalMap) {w : Word} (hw : Point w) :
    Point ((total X).map w) := by
  obtain ⟨hphase, hcrit⟩ := (point_at_level rfl).mp hw
  let u : Node := ⟨w, point_tree hw⟩
  have hu : u = criticalNode w.length := Subtype.ext hcrit
  have heq : (total X).map w = X.map (criticalNode w.length) := by
    exact (total_agrees X u).trans (congrArg X.map hu)
  rw [heq]
  exact (point_at_level rfl).mpr ⟨(X.phase _).mpr hphase, X.critical_image _⟩

/-- The literal labelled diary is hereditary under the actual critical maps. -/
theorem preserves_diary (X : CriticalMap) (C : Finset Word) :
    GeneralizedNormalization.codes (C.image (total X).map) =
      GeneralizedNormalization.codes C :=
  GeneralizedNormalization.codes_image (total X) C

theorem preserves_labelled_diary (X : CriticalMap) (C : Finset Word)
    {w : Word} (hw : w ∈ C) :
    GeneralizedNormalization.code (C.image (total X).map) ((total X).map w) =
      GeneralizedNormalization.code C w :=
  GeneralizedNormalization.code_image (total X) C hw

end CriticalCopies

namespace GeneralizedCanonization
open FIFOLifting
open GeneralizedNormalization

abbrev DiaryIndex := Σ n, GeneralizedDiary n

noncomputable def serializedImage (D : GeneralizedDiary n)
    (e : RayMilliken.Embedding D.shape) : Finset Word :=
  D.codes.image (HFin ∘ e.realizer.map)

/-- The induced colour depends only on the finite embedding, not on the
chosen total completion or its values outside the diary. -/
theorem serializedImage_agrees (D : GeneralizedDiary n)
    (e : RayMilliken.Embedding D.shape) (f : RayStrongMap)
    (hf : ∀ s : D.shape.Node, f.map s.val = e s) :
    serializedImage D e = D.codes.image (HFin ∘ f.map) := by
  classical
  unfold serializedImage
  apply Finset.image_congr
  intro w hw
  change HFin (e.realizer.map w) = HFin (f.map w)
  congr 1
  exact (e.realizer_agrees ⟨w, D.code_node hw⟩).trans (hf ⟨w, D.code_node hw⟩).symm

/-- Each literal generalized diary is actually realized in the sparse set,
with its coding labels recovered individually. -/
theorem literal_realized (D : GeneralizedDiary n) :
    (∀ w ∈ D.codes.image HFin, Point w) ∧
      codes (D.codes.image HFin) = D.codes ∧
      ∀ w ∈ D.codes, code (D.codes.image HFin) (HFin w) = w := by
  classical
  obtain ⟨f, _, hf⟩ := diary_lift D RayStrongMap.identity
  have himage : D.codes.image f.map = D.codes.image HFin := by
    apply Finset.image_congr
    intro w hw
    exact hf w hw
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw
    exact HFin_point v
  · rw [← himage]
    exact image_recovery D f
  · intro w hw
    rw [← himage, ← hf w hw]
    exact labelled_image_recovery D f hw

theorem lift_image_eq (g : RayStrongMap) (C : Finset Word)
    (hC : ∀ w ∈ C, Point w) :
    C.image (CriticalCopies.total (liftCritical g)).map =
      C.image (HFin ∘ g.map) := by
  classical
  apply Finset.image_congr
  intro w hw
  let s : CriticalCopies.Node := ⟨w, point_tree (hC w hw)⟩
  exact (CriticalCopies.total_agrees (liftCritical g) s).trans
    (liftCritical_code g s (hC w hw))

/-- Simultaneous canonization on each prescribed finite diary class. The
same critical copy works for the whole finite family; no assumption that
there are finitely many expansion types of a fixed size is used. -/
theorem finite_fragment (ds : List DiaryIndex) {r : Nat}
    (colour : Finset Word → Fin (r+1)) :
    ∃ X : CriticalCopies.CriticalMap,
      ∀ d ∈ ds, ∃ c : Fin (r+1), ∀ C : Finset Word,
        C.Nonempty → (∀ w ∈ C, Point w) → codes C = d.2.codes →
        colour (C.image (CriticalCopies.total X).map) = c := by
  classical
  obtain ⟨g, hg⟩ := RayMilliken.restricted_milliken_list
    (fun d : DiaryIndex => d.2.shape) ds
    (fun d e => colour (serializedImage d.2 e))
  refine ⟨liftCritical g, ?_⟩
  intro d hd
  obtain ⟨c, hc⟩ := hg d hd
  refine ⟨c, ?_⟩
  intro C hne hP hC
  let f := rayMap hne
  let e := RayMilliken.Embedding.ofTotal d.2.shape f
  have hmono := hc e
  have hser : serializedImage d.2 (RayMilliken.Embedding.comp g e) =
      C.image (HFin ∘ g.map) := by
    rw [serializedImage_agrees d.2 _ (g.comp f) (fun _ => rfl)]
    change d.2.codes.image ((HFin ∘ g.map) ∘ f.map) = _
    rw [← Finset.image_image, ← hC]
    change ((codes C).image (rayMap hne).map).image (HFin ∘ g.map) = _
    rw [rayMap_codes hne]
  rw [hser] at hmono
  rw [lift_image_eq g C hP]
  exact hmono

/-- IRT in the concrete finite-code-set representation: every realized
generalized diary has degree one on an expanded critical self-copy. -/
theorem codeSet_IRT (D : GeneralizedDiary n) {r : Nat}
    (colour : Finset Word → Fin (r+1)) :
    ∃ X : CriticalCopies.CriticalMap, ∃ c : Fin (r+1),
      ∀ C : Finset Word, C.Nonempty → (∀ w ∈ C, Point w) →
      codes C = D.codes → colour (C.image (CriticalCopies.total X).map) = c := by
  obtain ⟨X, hX⟩ := finite_fragment [⟨n,D⟩] colour
  obtain ⟨c, hc⟩ := hX ⟨n,D⟩ (by simp)
  exact ⟨X,c,hc⟩

end GeneralizedCanonization
end AllThoseBigRamsey.Pseudotree
