import PseudotreeValidation.RevisedDiaryRealization
import PseudotreeValidation.RevisedChainDiaries

/-! Exact classification of the induced expanded first-order structures
on a fixed finite functional carrier A. The complete tuple relation
and the height order recover its labeled normalized diagram; restriction
to subsets recovers every relation of the infinite diary language.
The equivalence below is between actual pulled-back structures and
independently specified labeled abstract diagrams. -/
namespace AllThoseBigRamsey.Pseudotree.RevisedExpansionClassification

open FirstOrder RayEmbeddings
open scoped FirstOrder
open RevisedConvention (RevisedSparseModel)
open RevisedDiaryExpansion (expandedLanguage Relation word word_point word_injective
  word_inf Increasing tupleSet exists_increasing_tuple normalized_closed_iff)
open RevisedCopyCanonization (words words_points words_nonempty)
open RevisedDiaryRealization (IsDiaryOf word_mem)
open RevisedCodingRelations (model model_injective Closed)
open GeneralizedNormalization (code codes rayMap rayMap_codes code_length_lt_iff)

abbrev P := RevisedSparseModel
variable {A : Type} [SemilatticeInf A] [language.Structure A] [MeetsInterpreted A]
  [Fintype A] [Nonempty A]

noncomputable def label (e : A ↪[language] P) (a : A) : Word := code (words e) (word (e a))

theorem words_card (e : A ↪[language] P) : (words e).card = Fintype.card A := by
  unfold words
  rw [Finset.card_image_of_injective _ (word_injective.comp e.injective)]
  simp

theorem words_closed (e : A ↪[language] P) : Closed (words e) := by
  intro s hs t ht
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp ht
  refine Finset.mem_image.mpr ⟨a ⊓ b,Finset.mem_univ _,?_⟩
  change word (e (a ⊓ b)) = RevisedCodingRelations.meet (word (e a)) (word (e b))
  rw [embedding_map_inf,word_inf]

theorem label_height (e : A ↪[language] P) (a b : A) :
    (label e a).length < (label e b).length ↔
      (word (e a)).length < (word (e b)).length :=
  code_length_lt_iff (words_nonempty e) (word_mem e a) (word_mem e b)

theorem labels_image (e : A ↪[language] P) : Finset.univ.image (label e) = codes (words e) := by
  classical
  unfold codes words label
  rw [Finset.image_image]
  rfl

/-- The actual structure induced on A by a reduct embedding. Its
function symbols are already fixed by the reduct. -/
noncomputable def induced (e : A ↪[language] P) : expandedLanguage.Structure A where
  funMap := fun f x => match f with
    | .meet => x 0 ⊓ x 1
  RelMap := fun r x => FirstOrder.Language.Structure.RelMap (L := expandedLanguage) r (e ∘ x)

def SameExpansion (e g : A ↪[language] P) : Prop :=
  ∀ (n : Nat) (r : Relation n) (x : Fin n → A),
    FirstOrder.Language.Structure.RelMap (L := expandedLanguage) r (e ∘ x) ↔
      FirstOrder.Language.Structure.RelMap (L := expandedLanguage) r (g ∘ x)

theorem induced_eq_iff (e g : A ↪[language] P) :
    induced e = induced g ↔ SameExpansion e g := by
  constructor
  · intro h n r x
    have h' := congrArg (fun S : expandedLanguage.Structure A =>
      @FirstOrder.Language.Structure.RelMap expandedLanguage A S n r x) h
    exact Iff.of_eq h'
  · intro h
    have hr :
        @FirstOrder.Language.Structure.RelMap expandedLanguage A (induced e) =
        @FirstOrder.Language.Structure.RelMap expandedLanguage A (induced g) := by
      funext n r x
      exact propext (h n r x)
    unfold induced at hr ⊢
    congr

theorem height_of_same {e g : A ↪[language] P} (h : SameExpansion e g) (a b : A) :
    (word (e a)).length < (word (e b)).length ↔
      (word (g a)).length < (word (g b)).length := by
  let t : Fin 2 → A := fun i => if i = 0 then a else b
  have ht := h 2 Relation.height t
  change (word (e (t 0))).length < (word (e (t 1))).length ↔
    (word (g (t 0))).length < (word (g (t 1))).length at ht
  simpa [t] using ht

theorem tupleSet_surj (e : A ↪[language] P) {n : Nat}
    (y : Fin n → A) (hy : Function.Surjective y) : tupleSet (e ∘ y) = words e := by
  ext w
  constructor
  · intro hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
    exact word_mem e (y i)
  · intro hw
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨i,rfl⟩ := hy a
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

theorem increasing_tuple (e : A ↪[language] P) :
    ∃ y : Fin (words e).card → A, Function.Surjective y ∧ Increasing (e ∘ y) := by
  classical
  obtain ⟨x,hx,hxC⟩ := exists_increasing_tuple (words_points e)
  have h (i : Fin (words e).card) : ∃ a : A, e a = x i := by
    have hw : word (x i) ∈ words e := by
      rw [← hxC]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hw
    exact ⟨a,word_injective ha⟩
  choose y hy using h
  refine ⟨y,?_,?_⟩
  · intro a
    have hw : word (e a) ∈ tupleSet x := by rw [hxC]; exact word_mem e a
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hw
    exact ⟨i,e.injective ((hy i).trans (word_injective hi))⟩
  · intro i j hij
    change (word (e (y i))).length < (word (e (y j))).length
    rw [hy,hy]
    exact hx hij

theorem codes_of_same {e g : A ↪[language] P} (h : SameExpansion e g) :
    codes (words e) = codes (words g) := by
  classical
  let D := GeneralizedNormalization.normalize (words_points e) (words_nonempty e)
  have hD : Closed D.codes :=
    (normalized_closed_iff (words_nonempty e)).mpr (words_closed e)
  obtain ⟨y,hy,hinc⟩ := increasing_tuple e
  have he : Increasing (e ∘ y) ∧ Closed (tupleSet (e ∘ y)) ∧
      codes (tupleSet (e ∘ y)) = D.codes := by
    rw [tupleSet_surj e y hy]
    exact ⟨hinc,words_closed e,rfl⟩
  have hg := (h (words e).card (Relation.diary D hD) y).mp he
  change Increasing (g ∘ y) ∧ Closed (tupleSet (g ∘ y)) ∧
    codes (tupleSet (g ∘ y)) = D.codes at hg
  rw [tupleSet_surj g y hy] at hg
  exact hg.2.2.symm

/-- The two named relations for the full finite structure suffice to
recover every individual normalized label. -/
theorem labels_of_same {e g : A ↪[language] P} (h : SameExpansion e g) :
    ∀ a, label e a = label g a := by
  classical
  let f (w : Word) : Word :=
    if hw : ∃ a : A, word (e a) = w then word (g hw.choose) else []
  have hf (a : A) : f (word (e a)) = word (g a) := by
    have hw : ∃ b : A, word (e b) = word (e a) := ⟨a,rfl⟩
    have ha := e.injective (word_injective hw.choose_spec)
    simp only [f,dif_pos hw,ha]
  have himage : (words e).image f = words g := by
    unfold words
    rw [Finset.image_image]
    apply Finset.image_congr
    intro a _
    exact hf a
  have horder : ∀ s ∈ words e, ∀ t ∈ words e, s.length < t.length →
      (f s).length < (f t).length := by
    intro s hs t ht hlt
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp ht
    change (word (e a)).length < (word (e b)).length at hlt
    change (f (word (e a))).length < (f (word (e b))).length
    rw [hf,hf]
    exact (height_of_same h a b).mp hlt
  have he : codes ((words e).image f) = codes (words e) := by
    rw [himage,codes_of_same h]
  intro a
  have hh := GeneralizedNormalization.labelled_of_codes f (words_points e) horder he
    (word (e a)) (word_mem e a)
  rw [himage,hf] at hh
  exact hh.symm

/-- Restriction of normalized labels to any tuple of A, including a
tuple that is not a substructure. -/
theorem tuple_subset (e : A ↪[language] P) {n : Nat} (x : Fin n → A) :
    tupleSet (e ∘ x) ⊆ words e := by
  intro w hw
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
  exact word_mem e (x i)

theorem normalized_tuple_eq {e g : A ↪[language] P} (h : ∀ a, label e a = label g a)
    {n : Nat} (x : Fin n → A) :
    (tupleSet (e ∘ x)).image (code (words e)) =
      (tupleSet (g ∘ x)).image (code (words g)) := by
  unfold tupleSet
  rw [Finset.image_image,Finset.image_image]
  apply Finset.image_congr
  intro i _
  exact h (x i)

/-- All the named relations, including on arbitrary tuples, are
determined by the normalized labeled map. -/
theorem same_of_labels {e g : A ↪[language] P} (h : ∀ a, label e a = label g a) :
    SameExpansion e g := by
  intro n r x
  have hh (a b : A) : (word (e a)).length < (word (e b)).length ↔
      (word (g a)).length < (word (g b)).length := by
    rw [← label_height e,← label_height g,h a,h b]
  cases r with
  | order =>
    change e (x 0) ≤ e (x 1) ↔ g (x 0) ≤ g (x 1)
    rw [embedding_le_iff,embedding_le_iff]
  | height => exact hh (x 0) (x 1)
  | diary D hD =>
    let C := tupleSet (e ∘ x)
    let B := tupleSet (g ∘ x)
    let N := C.image (code (words e))
    let M := B.image (code (words g))
    have hNM : N = M := normalized_tuple_eq h x
    have hC : N.image (rayMap (words_nonempty e)).map = C :=
      GeneralizedNormalization.subset_image_recovery (words_nonempty e) (tuple_subset e x)
    have hB : M.image (rayMap (words_nonempty g)).map = B :=
      GeneralizedNormalization.subset_image_recovery (words_nonempty g) (tuple_subset g x)
    have hcN : codes C = codes N := by
      rw [← hC,GeneralizedNormalization.codes_image]
    have hbM : codes B = codes M := by
      rw [← hB,GeneralizedNormalization.codes_image]
    have hcodes : codes C = codes B := hcN.trans ((congrArg codes hNM).trans hbM.symm)
    have hcClosed : Closed C ↔ Closed N := by
      rw [← hC,RevisedCodingRelations.closed_image_iff]
    have hbClosed : Closed B ↔ Closed M := by
      rw [← hB,RevisedCodingRelations.closed_image_iff]
    have hclosed : Closed C ↔ Closed B :=
      hcClosed.trans (by rw [hNM]; exact hbClosed.symm)
    have hinc : Increasing (e ∘ x) ↔ Increasing (g ∘ x) := by
      constructor
      · intro hi i j hij
        exact (hh (x i) (x j)).mp (hi hij)
      · intro hi i j hij
        exact (hh (x i) (x j)).mpr (hi hij)
    change (Increasing (e ∘ x) ∧ Closed C ∧ codes C = D.codes) ↔
      (Increasing (g ∘ x) ∧ Closed B ∧ codes B = D.codes)
    rw [hinc,hclosed,hcodes]

theorem induced_eq_iff_labels (e g : A ↪[language] P) :
    induced e = induced g ↔ ∀ a, label e a = label g a :=
  (induced_eq_iff e g).trans ⟨labels_of_same,same_of_labels⟩

/-- The pairs in the manuscript, with fixed size |A| and the exact
functional reduct on their coding nodes. -/
structure LabeledDiary (A : Type) [language.Structure A] [Fintype A] where
  diagram : GeneralizedDiary (Fintype.card A)
  labeling : A ↪[language] TernaryModel
  range_eq : IsDiaryOf diagram labeling

theorem labeledDiary_ext {D E : LabeledDiary A} (hD : D.diagram = E.diagram)
    (hE : D.labeling = E.labeling) : D = E := by
  cases D
  cases E
  cases hD
  cases hE
  rfl

/-- All realized expanded structures on the fixed reduct A. -/
abbrev RealizedExpansion (A : Type) [SemilatticeInf A] [language.Structure A] :=
  ↥(Set.range (induced (A := A)))

noncomputable def realizeExpansion (D : LabeledDiary A) : RealizedExpansion A :=
  let e := (RevisedDiaryRealization.realize_pair D.diagram D.labeling D.range_eq).choose
  ⟨induced e,⟨e,rfl⟩⟩

/-- The canonical finite expansion type equals its labeled normalized
diary pair, bijectively, with no quotient by automorphisms of A. -/
theorem realizeExpansion_bijective : Function.Bijective (realizeExpansion (A := A)) := by
  classical
  constructor
  · intro D E h
    let e := (RevisedDiaryRealization.realize_pair D.diagram D.labeling D.range_eq).choose
    let g := (RevisedDiaryRealization.realize_pair E.diagram E.labeling E.range_eq).choose
    have he := (RevisedDiaryRealization.realize_pair D.diagram D.labeling D.range_eq).choose_spec
    have hg := (RevisedDiaryRealization.realize_pair E.diagram E.labeling E.range_eq).choose_spec
    have hEq : induced e = induced g := congrArg Subtype.val h
    have hlabel := (induced_eq_iff_labels e g).mp hEq
    have hcodes : D.diagram.codes = E.diagram.codes := by
      rw [← he.1,← hg.1,← labels_image,← labels_image]
      exact Finset.image_congr (fun a _ => hlabel a)
    apply labeledDiary_ext
    · exact RevisedChainDiaries.generalized_ext (GeneralizedDiary.nodes_eq_of_codes_eq hcodes) hcodes
    · apply FirstOrder.Language.Embedding.ext
      intro a
      exact (he.2 a).symm.trans ((congrArg model (hlabel a)).trans (hg.2 a))
  · intro E
    obtain ⟨e,he⟩ := E.property
    let D : GeneralizedDiary (Fintype.card A) :=
      ⟨GeneralizedNormalization.nodes (words e),codes (words e),
        ⟨_,GeneralizedNormalization.normalized_axioms (words_points e) (words_nonempty e)⟩,
        (GeneralizedNormalization.codes_card (words_nonempty e)).trans (words_card e)⟩
    obtain ⟨ι,hι,hlabel⟩ := RevisedDiaryRealization.normalized_pair e
    have hD : IsDiaryOf D ι := hι
    let Q : LabeledDiary A := ⟨D,ι,hD⟩
    refine ⟨Q,?_⟩
    apply Subtype.ext
    let g := (RevisedDiaryRealization.realize_pair D ι hD).choose
    have hg := (RevisedDiaryRealization.realize_pair D ι hD).choose_spec
    change induced g = E.val
    rw [← he]
    apply (induced_eq_iff_labels g e).mpr
    intro a
    apply model_injective
    exact (hg.2 a).trans (hlabel a)

noncomputable def expansionEquiv : LabeledDiary A ≃ RealizedExpansion A :=
  Equiv.ofBijective realizeExpansion realizeExpansion_bijective

end AllThoseBigRamsey.Pseudotree.RevisedExpansionClassification
