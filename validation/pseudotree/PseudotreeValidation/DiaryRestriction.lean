import PseudotreeValidation.GeneralizedCanonization
import PseudotreeValidation.SparseModel
import PseudotreeValidation.Closure

/-! Restriction to finite subsets and the precise meet-closed relation
interface. The manuscript adds diary symbols only for nonempty finite
substructures. Arbitrary finite coding subsets can be recovered from
their finite meet closures, without adding extra relation symbols. -/
namespace AllThoseBigRamsey.Pseudotree
open RayEmbeddings RayMapModel
open SparseNormalization (Point)

namespace GeneralizedNormalization

theorem subset_image_recovery {C D : Finset Word} (hC : C.Nonempty)
    (hDC : D ⊆ C) :
    (D.image (code C)).image (rayMap hC).map = D := by
  classical
  rw [Finset.image_image]
  have h : D.image ((rayMap hC).map ∘ code C) = D.image id := by
    apply Finset.image_congr
    intro w hw
    exact rayMap_code hC (hDC hw)
  rw [h,Finset.image_id]

/-- The labelled normalization of a subset can be computed from the
labelled normalization of the larger set. -/
theorem code_restriction {C D : Finset Word} (hC : C.Nonempty)
    (hDC : D ⊆ C) {w : Word} (hw : w ∈ D) :
    code D w = code (D.image (code C)) (code C w) := by
  have hn := code_image (rayMap hC) (D.image (code C))
    (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
  rw [subset_image_recovery hC hDC,rayMap_code hC (hDC hw)] at hn
  exact hn

/-- Consequently, labelled preservation on one finite superset entails
labelled preservation on all of its subsets, even when the subsets
are not substructures in the functional language. -/
theorem labelled_of_superset (f : Word → Word) {C D : Finset Word}
    (hDC : D ⊆ C)
    (h : ∀ v ∈ C, code (C.image f) (f v) = code C v)
    {w : Word} (hw : w ∈ D) :
    code (D.image f) (f w) = code D w := by
  classical
  have hC : C.Nonempty := ⟨w,hDC hw⟩
  have hsub : D.image f ⊆ C.image f := Finset.image_subset_image hDC
  have he : (D.image f).image (code (C.image f)) = D.image (code C) := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro v hv
    exact h v (hDC hv)
  calc
    code (D.image f) (f w) =
        code ((D.image f).image (code (C.image f))) (code (C.image f) (f w)) :=
      code_restriction (hC.image f) hsub (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
    _ = code (D.image (code C)) (code C w) := by rw [he,h w (hDC hw)]
    _ = code D w := (code_restriction hC hDC hw).symm

end GeneralizedNormalization

namespace CodingRelations

/-- Meet in the literal word coordinates, with the original reduct
semantics. This is not the longest common prefix operation. -/
def meet (s t : Word) : Word :=
  (wordMeet (s.map toLetter) (t.map toLetter)).map toFin

@[simp] theorem meet_model (s t : Word) :
    DiaryChains.model (meet s t) = DiaryChains.model s ⊓ DiaryChains.model t := by
  simp [meet,DiaryChains.model,List.map_map,Function.comp_def]

theorem meet_point {s t : Word} (hs : Point s) (ht : Point t) : Point (meet s t) := by
  change Sparse.InSparse ((meet s t).map toLetter)
  simpa [meet,List.map_map,Function.comp_def] using Sparse.sparse_meet_closed hs ht

def Closed (C : Finset Word) : Prop :=
  ∀ s ∈ C, ∀ t ∈ C, meet s t ∈ C

theorem meet_self (w : Word) : meet w w = w := by
  apply DiaryChains.model_injective
  rw [meet_model,inf_idem]

/-- The pairwise-meet hull is finite; the meet-tree lemma shows that it
is already closed, so no iterative closure operation is needed. -/
def hull (C : Finset Word) : Finset Word :=
  (C.product C).image (fun p => meet p.1 p.2)

theorem mem_hull {C : Finset Word} {w : Word} :
    w ∈ hull C ↔ ∃ s ∈ C, ∃ t ∈ C, meet s t = w := by
  constructor
  · intro h
    obtain ⟨⟨s,t⟩,hp,he⟩ := Finset.mem_image.mp h
    obtain ⟨hs,ht⟩ := Finset.mem_product.mp hp
    exact ⟨s,hs,t,ht,he⟩
  · rintro ⟨s,hs,t,ht,he⟩
    exact Finset.mem_image.mpr ⟨(s,t),Finset.mem_product.mpr ⟨hs,ht⟩,he⟩

theorem subset_hull (C : Finset Word) : C ⊆ hull C :=
  fun w hw => mem_hull.mpr ⟨w,hw,w,hw,meet_self w⟩

theorem hull_points {C : Finset Word} (hC : ∀ w ∈ C, Point w) :
    ∀ w ∈ hull C, Point w := by
  intro w hw
  obtain ⟨s,hs,t,ht,rfl⟩ := mem_hull.mp hw
  exact meet_point (hC _ hs) (hC _ ht)

theorem model_mem_hull {C : Finset Word} {w : Word} :
    DiaryChains.model w ∈ Set.image2 (· ⊓ ·)
      (DiaryChains.model '' (C : Set Word)) (DiaryChains.model '' (C : Set Word)) ↔
      w ∈ hull C := by
  constructor
  · rintro ⟨_,⟨s,hs,rfl⟩,_,⟨t,ht,rfl⟩,he⟩
    apply mem_hull.mpr
    refine ⟨s,hs,t,ht,DiaryChains.model_injective ?_⟩
    exact (meet_model s t).trans he
  · intro hw
    obtain ⟨s,hs,t,ht,rfl⟩ := mem_hull.mp hw
    exact ⟨DiaryChains.model s,⟨s,hs,rfl⟩,DiaryChains.model t,⟨t,ht,rfl⟩,
      (meet_model s t).symm⟩

theorem hull_closed (C : Finset Word) : Closed (hull C) := by
  intro s hs t ht
  apply model_mem_hull.mp
  rw [meet_model]
  exact image2_inf_closed RayTree.le_or_ge_of_le_common
    (DiaryChains.model '' (C : Set Word))
    _ (model_mem_hull.mpr hs) _ (model_mem_hull.mpr ht)

/-- The exact condition on finite nonempty substructures is sufficient
for the arbitrary finite-set condition used in reconstruction. -/
theorem labelled_of_closed (f : Word → Word)
    (h : ∀ C : Finset Word, C.Nonempty → (∀ w ∈ C, Point w) → Closed C →
      ∀ w ∈ C, GeneralizedNormalization.code (C.image f) (f w) =
        GeneralizedNormalization.code C w)
    (C : Finset Word) (hC : ∀ w ∈ C, Point w) (w : Word) (hw : w ∈ C) :
    GeneralizedNormalization.code (C.image f) (f w) = GeneralizedNormalization.code C w := by
  apply GeneralizedNormalization.labelled_of_superset f (subset_hull C) _ hw
  exact h (hull C) ⟨w,subset_hull C hw⟩ (hull_points hC) (hull_closed C)

/-- The actual ray maps preserve the functional reduct in word coordinates. -/
theorem model_map (f : RayStrongMap) (w : Word) :
    DiaryChains.model (f.map w) = RayMapModel.modelMap f (DiaryChains.model w) := by
  simp [DiaryChains.model,RayMapModel.modelMap,RayMapModel.act,List.map_map,Function.comp_def]

theorem map_meet (f : RayStrongMap) (s t : Word) :
    f.map (meet s t) = meet (f.map s) (f.map t) := by
  apply DiaryChains.model_injective
  rw [model_map,meet_model,RayMapModel.modelMap_inf,meet_model,model_map,model_map]

theorem closed_image_iff (f : RayStrongMap) (C : Finset Word) :
    Closed (C.image f.map) ↔ Closed C := by
  constructor
  · intro h s hs t ht
    have hm := h (f.map s) (Finset.mem_image.mpr ⟨s,hs,rfl⟩)
      (f.map t) (Finset.mem_image.mpr ⟨t,ht,rfl⟩)
    rw [← map_meet] at hm
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hm
    exact (f.injective he) ▸ hv
  · intro h s hs t ht
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ht
    rw [← map_meet]
    exact Finset.mem_image.mpr ⟨_,h u hu v hv,rfl⟩

end CodingRelations
end AllThoseBigRamsey.Pseudotree
