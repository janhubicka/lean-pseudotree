import PseudotreeValidation.RevisedSparseModel
import PseudotreeValidation.DiaryLabels

/-! Reflection conjugates every ray-preserving strong map to another such
map. Thus the already checked old-model embedding theorem proves the
revised-model embedding theorem, without reflecting the FIFO queue.
The finite meet-closed relation bridge below uses the actual revised meet. -/
namespace AllThoseBigRamsey.Pseudotree.RevisedCodingRelations

open RayEmbeddings RayMapModel
open SparseNormalization (Point)
open RevisedConvention (revisedToBlocks revisedWordMeet mirror mirrorLetter)

def flipDigit (a : Fin 3) : Fin 3 := toFin (mirrorLetter (toLetter a))

@[simp] theorem flipDigit_twice (a : Fin 3) : flipDigit (flipDigit a) = a := by
  simp [flipDigit]

@[simp] theorem flipDigit_one : flipDigit 1 = 1 := rfl

@[simp] theorem flipDigit_eq_one (a : Fin 3) : flipDigit a = 1 ↔ a = 1 := by
  constructor
  · intro h
    have hh := congrArg flipDigit h
    simpa only [flipDigit_twice,flipDigit_one] using hh
  · rintro rfl
    rfl

def reflectWord (s : Word) : Word := s.map flipDigit

@[simp] theorem reflectWord_twice (s : Word) : reflectWord (reflectWord s) = s := by
  simp [reflectWord,List.map_map,Function.comp_def]

@[simp] theorem reflectWord_length (s : Word) : (reflectWord s).length = s.length := by
  simp [reflectWord]

theorem reflectWord_injective : Function.Injective reflectWord := by
  intro s t h
  simpa only [reflectWord_twice] using congrArg reflectWord h

@[simp] theorem reflectWord_binary (s : Word) : Binary (reflectWord s) ↔ Binary s := by
  simp [reflectWord,Binary]

@[simp] theorem reflectWord_letters (w : Word) :
    (reflectWord w).map toLetter = mirror (w.map toLetter) := by
  simp [reflectWord,flipDigit,RevisedConvention.mirror,List.map_map,Function.comp_def]

/-- The conjugate acts in the old coordinates. It has the same level map. -/
def conjugate (f : RayStrongMap) : RayStrongMap where
  map := fun w => reflectWord (f.map (reflectWord w))
  level := f.level
  level_strict := f.level_strict
  length_map := by
    intro s
    change (reflectWord (f.map (reflectWord s))).length = f.level s.length
    rw [reflectWord_length,f.length_map,reflectWord_length]
  step := by
    intro s a
    obtain ⟨p,hp,hpb⟩ := f.step (reflectWord s) (flipDigit a)
    refine ⟨reflectWord p,?_,?_⟩
    · change reflectWord (f.map (reflectWord (s ++ [a]))) =
        reflectWord (f.map (reflectWord s)) ++ a :: reflectWord p
      rw [show reflectWord (s ++ [a]) = reflectWord s ++ [flipDigit a] by
        simp [reflectWord],hp]
      simp [reflectWord]
    · intro ha
      apply (reflectWord_binary p).mpr
      exact hpb (fun h => ha ((flipDigit_eq_one a).mp h))

@[simp] theorem conjugate_reflect (f : RayStrongMap) (w : Word) :
    (conjugate f).map (reflectWord w) = reflectWord (f.map w) := by
  change reflectWord (f.map (reflectWord (reflectWord w))) = _
  rw [reflectWord_twice]

/-- The revised literal word interpreted in the same ambient block model. -/
def model (w : Word) : TernaryModel := revisedToBlocks (w.map toLetter)

theorem model_reflect (w : Word) : model w = DiaryChains.model (reflectWord w) := by
  change toBlocks (mirror (w.map toLetter)) = toBlocks ((reflectWord w).map toLetter)
  rw [reflectWord_letters]

theorem model_injective : Function.Injective model := by
  intro s t h
  apply reflectWord_injective
  apply DiaryChains.model_injective
  rw [← model_reflect,← model_reflect]
  exact h

theorem model_map (f : RayStrongMap) (w : Word) :
    model (f.map w) = RayMapModel.modelMap (conjugate f) (model w) := by
  rw [model_reflect,model_reflect,← CodingRelations.model_map,conjugate_reflect]

/-- Meet in the literal word coordinates, with the revised reduct
semantics. This is not the longest common prefix operation. -/
def meet (s t : Word) : Word :=
  (revisedWordMeet (s.map toLetter) (t.map toLetter)).map toFin

@[simp] theorem meet_model (s t : Word) :
    model (meet s t) = model s ⊓ model t := by
  simp [meet,model,List.map_map,Function.comp_def]

theorem meet_point {s t : Word} (hs : Point s) (ht : Point t) : Point (meet s t) := by
  change Sparse.InSparse ((meet s t).map toLetter)
  simpa [meet,List.map_map,Function.comp_def] using RevisedConvention.revised_sparse_meet_closed hs ht

def Closed (C : Finset Word) : Prop :=
  ∀ s ∈ C, ∀ t ∈ C, meet s t ∈ C

theorem meet_self (w : Word) : meet w w = w := by
  apply model_injective
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
    model w ∈ Set.image2 (· ⊓ ·)
      (model '' (C : Set Word)) (model '' (C : Set Word)) ↔
      w ∈ hull C := by
  constructor
  · rintro ⟨_,⟨s,hs,rfl⟩,_,⟨t,ht,rfl⟩,he⟩
    apply mem_hull.mpr
    refine ⟨s,hs,t,ht,model_injective ?_⟩
    exact (meet_model s t).trans he
  · intro hw
    obtain ⟨s,hs,t,ht,rfl⟩ := mem_hull.mp hw
    exact ⟨model s,⟨s,hs,rfl⟩,model t,⟨t,ht,rfl⟩,
      (meet_model s t).symm⟩

theorem hull_closed (C : Finset Word) : Closed (hull C) := by
  intro s hs t ht
  apply model_mem_hull.mp
  rw [meet_model]
  exact image2_inf_closed RayTree.le_or_ge_of_le_common
    (model '' (C : Set Word))
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
theorem map_meet (f : RayStrongMap) (s t : Word) :
    f.map (meet s t) = meet (f.map s) (f.map t) := by
  apply model_injective
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


open GeneralizedNormalization (code codes)

/-- Exactly the two new relation families of the manuscript suffice
for the arbitrary labelled finite-set condition: length order, and
the named diaries of nonempty meet-closed sets. -/
theorem labelled_of_named_diaries (f : Word → Word)
    (horder : ∀ s t, Point s → Point t → s.length < t.length →
      (f s).length < (f t).length)
    (hdiary : ∀ C : Finset Word, C.Nonempty → (∀ w ∈ C, Point w) → Closed C →
      codes (C.image f) = codes C) :
    ∀ C : Finset Word, (∀ w ∈ C, Point w) → ∀ w ∈ C,
      code (C.image f) (f w) = code C w := by
  apply labelled_of_closed f
  intro C hne hC hcl
  exact GeneralizedNormalization.labelled_of_codes f hC
    (fun s hs t ht hlt => horder s t (hC s hs) (hC t ht) hlt)
    (hdiary C hne hC hcl)


end AllThoseBigRamsey.Pseudotree.RevisedCodingRelations
