import PseudotreeValidation.DiaryExpansion
import PseudotreeValidation.SparseRecurrence

/-! Native first-order Ramsey statements. The finite-code-set IRT
is transferred to actual embeddings of finite functional
substructures, and recurrence to actual reduct self-embeddings. -/
namespace AllThoseBigRamsey.Pseudotree.DiaryExpansion
open FirstOrder RayEmbeddings RayMapModel
open scoped FirstOrder
open CriticalCopies (CriticalMap total)
open GeneralizedNormalization (codes)
open SparseNormalization (Point point_unique_length)
open CodingRelations (Closed)

/-- Recurrence in the manuscript's original functional reduct. -/
theorem native_recurrence (e : SparseModel ↪[language] SparseModel) :
    ∃ g : SparseModel ↪[expandedLanguage] SparseModel, Set.range g ⊆ Set.range e := by
  let f := SparseModel.inclusion.comp (e.comp SparseModel.equiv.toEmbedding)
  have hs (x : TernaryModel) (hx : x ∈ Set.range f) :
      Sparse.InSparse (fromBlocks x) := by
    obtain ⟨t,rfl⟩ := hx
    exact (e (SparseModel.equiv t)).property
  obtain ⟨X,hX⟩ := Reservoir.recurrence f hs
  refine ⟨criticalEmbedding X,?_⟩
  rintro _ ⟨x,rfl⟩
  obtain ⟨t,ht⟩ := hX (word x) (word_point x)
  refine ⟨SparseModel.equiv t,?_⟩
  apply Subtype.ext
  change (e (SparseModel.equiv t)).val = (criticalPointMap X x).val
  change f t = (criticalPointMap X x).val
  rw [ht,← word_model (criticalPointMap X x),criticalPointMap_word]

/-- Coding set of an actual finite first-order embedding. -/
def embeddingCodes {A : Type} [Fintype A] [expandedLanguage.Structure A]
    (e : A ↪[expandedLanguage] SparseModel) : Finset Word :=
  Finset.univ.image (word ∘ e)

theorem embeddingCodes_points {A : Type} [Fintype A] [expandedLanguage.Structure A]
    (e : A ↪[expandedLanguage] SparseModel) :
    ∀ w ∈ embeddingCodes e, Point w := by
  intro w hw
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hw
  exact word_point (e a)

theorem embeddingCodes_nonempty {A : Type} [Fintype A] [Nonempty A]
    [expandedLanguage.Structure A] (e : A ↪[expandedLanguage] SparseModel) :
    (embeddingCodes e).Nonempty := by
  obtain ⟨a⟩ := ‹Nonempty A›
  exact ⟨word (e a),Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩⟩

theorem embeddingCodes_comp (X : CriticalMap) {A : Type}
    [Fintype A] [expandedLanguage.Structure A] (e : A ↪[expandedLanguage] SparseModel) :
    embeddingCodes ((criticalEmbedding X).comp e) = (embeddingCodes e).image (total X).map := by
  unfold embeddingCodes
  rw [Finset.image_image]
  apply Finset.image_congr
  intro a _
  exact criticalPointMap_word X (e a)

/-- The code set of a finite functional substructure is meet-closed
in the actual reduct, not only closed under literal word prefixes. -/
theorem substructureCodes_closed (A : expandedLanguage.Substructure SparseModel)
    [Fintype A] : Closed (embeddingCodes A.subtype) := by
  intro s hs t ht
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp ht
  let v : Fin 2 → SparseModel := fun i => if i = 0 then a.val else b.val
  have hV : ∀ i, v i ∈ A := by
    intro i
    by_cases h : i = 0 <;> simp [v,h,a.property,b.property]
  have hm := A.fun_mem MeetFunction.meet v hV
  have hm' : a.val ⊓ b.val ∈ A := by
    change v 0 ⊓ v 1 ∈ A at hm
    simpa [v] using hm
  refine Finset.mem_image.mpr ⟨⟨a.val ⊓ b.val,hm'⟩,Finset.mem_univ _,?_⟩
  exact word_inf a.val b.val

theorem substructure_embedding_height (A : expandedLanguage.Substructure SparseModel)
    (e : A ↪[expandedLanguage] SparseModel) (a b : A) :
    (word (e a)).length < (word (e b)).length ↔
      (word a.val).length < (word b.val).length := by
  let t : Fin 2 → A := fun i => if i = 0 then a else b
  have h := e.map_rel' Relation.height t
  change (word (e (t 0))).length < (word (e (t 1))).length ↔
    (word (t 0).val).length < (word (t 1).val).length at h
  simpa [t] using h

/-- Sort a finite native substructure by its coding heights. This is
an enumeration of the actual carrier, not a choice of presentation
of an abstract diary. -/
theorem increasing_substructure_tuple (A : expandedLanguage.Substructure SparseModel)
    [Fintype A] :
    ∃ y : Fin (embeddingCodes A.subtype).card → A,
      Function.Surjective y ∧ Increasing (A.subtype ∘ y) := by
  classical
  let C := embeddingCodes A.subtype
  obtain ⟨x,hx,hxC⟩ := exists_increasing_tuple (embeddingCodes_points A.subtype)
  have hxA (i : Fin C.card) : x i ∈ A := by
    have hm : word (x i) ∈ embeddingCodes A.subtype := by
      rw [← hxC]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    obtain ⟨a,_,he⟩ := Finset.mem_image.mp hm
    have he' : a.val = x i := word_injective he
    exact he' ▸ a.property
  let y (i : Fin C.card) : A := ⟨x i,hxA i⟩
  refine ⟨y,?_,hx⟩
  intro a
  have hm : word a.val ∈ tupleSet x := by
    rw [hxC]
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
  exact ⟨i,Subtype.ext (word_injective hi)⟩

theorem tupleSet_of_surjective (A : expandedLanguage.Substructure SparseModel)
    [Fintype A] (e : A ↪[expandedLanguage] SparseModel) {n : Nat}
    (y : Fin n → A) (hy : Function.Surjective y) :
    tupleSet (e ∘ y) = embeddingCodes e := by
  ext w
  constructor
  · intro hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_image.mpr ⟨y i,Finset.mem_univ _,rfl⟩
  · intro hw
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨i,rfl⟩ := hy a
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

/-- The native relation naming the entire finite substructure forces
its normalized diary on every native embedding. -/
theorem substructure_diary_preserved (A : expandedLanguage.Substructure SparseModel)
    [Fintype A] [Nonempty A] (e : A ↪[expandedLanguage] SparseModel) :
    codes (embeddingCodes e) = codes (embeddingCodes A.subtype) := by
  classical
  let C := embeddingCodes A.subtype
  let D := GeneralizedNormalization.normalize (embeddingCodes_points A.subtype)
    (embeddingCodes_nonempty A.subtype)
  have hD : Closed D.codes :=
    (normalized_closed_iff (embeddingCodes_nonempty A.subtype)).mpr (substructureCodes_closed A)
  obtain ⟨y,hy,hinc⟩ := increasing_substructure_tuple A
  have hrel : Increasing (A.subtype ∘ y) ∧ Closed (tupleSet (A.subtype ∘ y)) ∧
      codes (tupleSet (A.subtype ∘ y)) = D.codes := by
    rw [tupleSet_of_surjective A A.subtype y hy]
    exact ⟨hinc,substructureCodes_closed A,rfl⟩
  have h := (e.map_rel' (Relation.diary D hD) y).mpr hrel
  change Increasing (e ∘ y) ∧ Closed (tupleSet (e ∘ y)) ∧
      codes (tupleSet (e ∘ y)) = D.codes at h
  rw [tupleSet_of_surjective A e y hy] at h
  exact h.2.2

/-- A native embedding of a finite substructure is determined by its
image, because its coding-height order is rigid. -/
theorem embeddingCodes_injective (A : expandedLanguage.Substructure SparseModel)
    [Fintype A] :
    Function.Injective (embeddingCodes (A:=A)) := by
  classical
  intro e₁ e₂ he
  obtain ⟨y,hy,hyinc⟩ := increasing_substructure_tuple A
  let C := embeddingCodes A.subtype
  let f₁ (i : Fin C.card) := (word (e₁ (y i))).length
  let f₂ (i : Fin C.card) := (word (e₂ (y i))).length
  have hf₁ : StrictMono f₁ :=
    fun i j hij => (substructure_embedding_height A e₁ (y i) (y j)).mpr (hyinc hij)
  have hf₂ : StrictMono f₂ :=
    fun i j hij => (substructure_embedding_height A e₂ (y i) (y j)).mpr (hyinc hij)
  let L := Finset.univ.image f₁
  have hL : L.card = C.card := by
    change (Finset.univ.image f₁).card = C.card
    rw [Finset.card_image_of_injective _ hf₁.injective]
    simp
  have hsame : Finset.univ.image f₂ = L := by
    have hh := congrArg (Finset.image List.length) he
    rw [← tupleSet_of_surjective A e₁ y hy,← tupleSet_of_surjective A e₂ y hy] at hh
    simp only [tupleSet,Finset.image_image] at hh
    exact hh.symm
  have h₁ := Finset.orderEmbOfFin_unique hL
    (f:=f₁) (fun i => Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) hf₁
  have h₂ := Finset.orderEmbOfFin_unique hL
    (f:=f₂) (fun i => by rw [← hsame]; exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) hf₂
  apply FirstOrder.Language.Embedding.ext
  intro a
  obtain ⟨i,rfl⟩ := hy a
  apply word_injective
  exact point_unique_length (word_point (e₁ (y i))) (word_point (e₂ (y i)))
    (congrFun (h₁.trans h₂.symm) i)

/-- Native IRT, including the empty finite structure. The input is a
colouring of actual first-order embeddings, not just code sets. -/
theorem native_IRT (A : expandedLanguage.Substructure SparseModel)
    [Fintype A] {r : Nat} (colour : (A ↪[expandedLanguage] SparseModel) → Fin (r+1)) :
    ∃ g : SparseModel ↪[expandedLanguage] SparseModel, ∃ c : Fin (r+1),
      ∀ e : A ↪[expandedLanguage] SparseModel, colour (g.comp e) = c := by
  classical
  cases isEmpty_or_nonempty A with
  | inl hA =>
    let g := FirstOrder.Language.Embedding.refl expandedLanguage SparseModel
    refine ⟨g,colour A.subtype,?_⟩
    intro e
    apply congrArg colour
    apply FirstOrder.Language.Embedding.ext
    intro a
    letI : IsEmpty A := hA
    exact isEmptyElim a
  | inr hA =>
    letI : Nonempty A := hA
    let C := embeddingCodes A.subtype
    let D := GeneralizedNormalization.normalize (embeddingCodes_points A.subtype)
      (embeddingCodes_nonempty A.subtype)
    let χ (B : Finset Word) : Fin (r+1) :=
      if h : ∃ e : A ↪[expandedLanguage] SparseModel, embeddingCodes e = B
      then colour h.choose else 0
    have hχ (e : A ↪[expandedLanguage] SparseModel) : χ (embeddingCodes e) = colour e := by
      have h : ∃ f : A ↪[expandedLanguage] SparseModel, embeddingCodes f = embeddingCodes e :=
        ⟨e,rfl⟩
      simp only [χ,dif_pos h]
      rw [embeddingCodes_injective A h.choose_spec]
    obtain ⟨X,c,hX⟩ := GeneralizedCanonization.codeSet_IRT D χ
    refine ⟨criticalEmbedding X,c,?_⟩
    intro e
    have hmono := hX (embeddingCodes e) (embeddingCodes_nonempty e)
      (embeddingCodes_points e) (substructure_diary_preserved A e)
    rw [← embeddingCodes_comp X e,hχ] at hmono
    exact hmono

end AllThoseBigRamsey.Pseudotree.DiaryExpansion
