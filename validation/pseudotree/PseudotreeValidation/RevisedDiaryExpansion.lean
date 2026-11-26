import PseudotreeValidation.RevisedCodingRelations
import PseudotreeValidation.LowerGeometry

/-!
# The actual first-order expansion on the sparse model

The function symbol remains meet. The relation symbols are the reduct
order, the coding-height order, and one symbol for each generalized
diary with meet-closed coding set. The interpretations use the actual
finite normalized coding sets, rather than an abstract type colouring.
-/
namespace AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion
open FirstOrder RayEmbeddings RayMapModel
open RevisedConvention (RevisedSparseModel revisedToBlocks revisedFromBlocks revisedWordEquiv
  revisedToBlocks_revisedFromBlocks revisedFromBlocks_revisedToBlocks)
open scoped FirstOrder
open SparseNormalization (Point point_unique_length)
open GeneralizedNormalization (code codes rayMap rayMap_codes)
open RevisedCodingRelations (Closed)

def word (x : RevisedSparseModel) : Word := (revisedFromBlocks x.val).map toFin

@[simp] theorem word_letters (x : RevisedSparseModel) : (word x).map toLetter = revisedFromBlocks x.val := by
  simp [word,List.map_map,Function.comp_def]

theorem word_point (x : RevisedSparseModel) : Point (word x) := by
  change Sparse.InSparse ((word x).map toLetter)
  rw [word_letters]
  exact x.property

def ofPoint (w : Word) (hw : Point w) : RevisedSparseModel :=
  RevisedSparseModel.ofWord (w.map toLetter) hw

@[simp] theorem word_ofPoint (w : Word) (hw : Point w) : word (ofPoint w hw) = w := by
  simp [word,ofPoint,RevisedSparseModel.ofWord,List.map_map,Function.comp_def]

@[simp] theorem ofPoint_word (x : RevisedSparseModel) : ofPoint (word x) (word_point x) = x := by
  apply Subtype.ext
  change revisedToBlocks ((word x).map toLetter) = x.val
  rw [word_letters,revisedToBlocks_revisedFromBlocks]

theorem word_injective : Function.Injective word := by
  intro x y h
  have he := congrArg (List.map toLetter) h
  rw [word_letters,word_letters] at he
  exact Subtype.ext (revisedWordEquiv.symm.injective he)

@[simp] theorem word_model (x : RevisedSparseModel) : RevisedCodingRelations.model (word x) = x.val := by
  unfold RevisedCodingRelations.model
  rw [word_letters,revisedToBlocks_revisedFromBlocks]

@[simp] theorem word_inf (x y : RevisedSparseModel) :
    word (x ⊓ y) = RevisedCodingRelations.meet (word x) (word y) := by
  apply RevisedCodingRelations.model_injective
  rw [RevisedCodingRelations.meet_model,word_model,word_model,word_model,RevisedSparseModel.val_inf]

/-- A tuple's actual coding set. Repetitions are excluded by the
strictly increasing height condition in the relation. -/
def tupleSet {n : Nat} (x : Fin n → RevisedSparseModel) : Finset Word :=
  Finset.univ.image (word ∘ x)

theorem tupleSet_points {n : Nat} (x : Fin n → RevisedSparseModel) :
    ∀ w ∈ tupleSet x, Point w := by
  intro w hw
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
  exact word_point (x i)

def Increasing {n : Nat} (x : Fin n → RevisedSparseModel) : Prop :=
  StrictMono (fun i => (word (x i)).length)

theorem tupleSet_card {n : Nat} {x : Fin n → RevisedSparseModel} (hx : Increasing x) :
    (tupleSet x).card = n := by
  unfold tupleSet
  rw [Finset.card_image_of_injective _ (show Function.Injective (word ∘ x) from by
    intro i j h
    exact hx.injective (congrArg List.length h))]
  simp

/-- Increasing enumeration of each finite coding set, using the
ordinary order on its lengths (which are pairwise distinct). -/
theorem exists_increasing_tuple {C : Finset Word} (hC : ∀ w ∈ C, Point w) :
    ∃ x : Fin C.card → RevisedSparseModel, Increasing x ∧ tupleSet x = C := by
  classical
  let L := C.image List.length
  have hL : L.card = C.card :=
    Finset.card_image_of_injOn (fun _ hs _ ht he => point_unique_length (hC _ hs) (hC _ ht) he)
  let e := L.orderEmbOfFin hL
  have he (i : Fin C.card) : ∃ w ∈ C, w.length = e i :=
    Finset.mem_image.mp (L.orderEmbOfFin_mem hL i)
  choose W hW hlen using he
  let x (i : Fin C.card) := ofPoint (W i) (hC _ (hW i))
  refine ⟨x,?_,?_⟩
  · intro i j hij
    change (word (ofPoint (W i) _)).length < (word (ofPoint (W j) _)).length
    rw [word_ofPoint,word_ofPoint,hlen,hlen]
    exact e.strictMono hij
  · ext w
    constructor
    · intro hw
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
      change word (ofPoint (W i) _) ∈ C
      simpa only [word_ofPoint] using hW i
    · intro hw
      have hl : w.length ∈ L := Finset.mem_image.mpr ⟨w,hw,rfl⟩
      have hr : w.length ∈ Set.range e := by
        rw [show Set.range e = (L : Set Nat) from L.range_orderEmbOfFin hL]
        exact hl
      obtain ⟨i,hi⟩ := hr
      have heq := point_unique_length (hC _ (hW i)) (hC w hw) ((hlen i).trans hi)
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by
        change word (ofPoint (W i) _) = w
        rw [word_ofPoint,heq]⟩

/-- Meet-closure of the normalized code set is equivalent to actual
meet-closure, by the ray map recovering the original finite set. -/
theorem normalized_closed_iff {C : Finset Word} (hne : C.Nonempty) :
    Closed (codes C) ↔ Closed C := by
  have h := RevisedCodingRelations.closed_image_iff (rayMap hne) (codes C)
  rw [rayMap_codes hne] at h
  exact h.symm

inductive Relation : Nat → Type
  | order : Relation 2
  | height : Relation 2
  | diary {n : Nat} (D : GeneralizedDiary n) (hD : Closed D.codes) : Relation n

def expandedLanguage : Language where
  Functions := MeetFunction
  Relations := Relation

noncomputable instance expandedStructure : expandedLanguage.Structure RevisedSparseModel where
  funMap := fun f x => match f with
    | .meet => x 0 ⊓ x 1
  RelMap := fun r x => match r with
    | .order => x 0 ≤ x 1
    | .height => (word (x 0)).length < (word (x 1)).length
    | .diary D _ => Increasing x ∧ Closed (tupleSet x) ∧ codes (tupleSet x) = D.codes

/-- The concrete embedding of the expansion induced by an actual
critical map, preserving and reflecting all relation symbols. -/
noncomputable def criticalPointMap (X : CriticalCopies.CriticalMap) (x : RevisedSparseModel) :
    RevisedSparseModel :=
  ofPoint ((CriticalCopies.total X).map (word x))
    (CriticalCopies.maps_point X (word_point x))

@[simp] theorem criticalPointMap_word (X : CriticalCopies.CriticalMap) (x : RevisedSparseModel) :
    word (criticalPointMap X x) = (CriticalCopies.total X).map (word x) :=
  word_ofPoint _ _

theorem criticalPointMap_model (X : CriticalCopies.CriticalMap) (x : RevisedSparseModel) :
    (criticalPointMap X x).val = RayMapModel.modelMap (RevisedCodingRelations.conjugate (CriticalCopies.total X)) x.val := by
  rw [← word_model (criticalPointMap X x),criticalPointMap_word,
    RevisedCodingRelations.model_map,word_model]

theorem criticalPointMap_inf (X : CriticalCopies.CriticalMap) (x y : RevisedSparseModel) :
    criticalPointMap X (x ⊓ y) = criticalPointMap X x ⊓ criticalPointMap X y := by
  apply word_injective
  rw [word_inf,criticalPointMap_word,word_inf,RevisedCodingRelations.map_meet,
    criticalPointMap_word,criticalPointMap_word]

theorem criticalPointMap_lt_iff (X : CriticalCopies.CriticalMap) (x y : RevisedSparseModel) :
    (word (criticalPointMap X x)).length < (word (criticalPointMap X y)).length ↔
      (word x).length < (word y).length := by
  rw [criticalPointMap_word,criticalPointMap_word,
    (CriticalCopies.total X).length_map,(CriticalCopies.total X).length_map]
  exact (show StrictMono (CriticalCopies.total X).level from
    fun _ _ h => (CriticalCopies.total X).level_strict h).lt_iff_lt

theorem tupleSet_criticalPointMap (X : CriticalCopies.CriticalMap) {n : Nat}
    (x : Fin n → RevisedSparseModel) :
    tupleSet (criticalPointMap X ∘ x) = (tupleSet x).image (CriticalCopies.total X).map := by
  unfold tupleSet
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i _
  exact criticalPointMap_word X (x i)

noncomputable def criticalEmbedding (X : CriticalCopies.CriticalMap) :
    RevisedSparseModel ↪[expandedLanguage] RevisedSparseModel where
  toFun := criticalPointMap X
  inj' := by
    intro x y h
    apply word_injective
    apply (CriticalCopies.total X).injective
    simpa only [criticalPointMap_word] using congrArg word h
  map_fun' := by
    intro n f x
    cases f
    exact criticalPointMap_inf X (x 0) (x 1)
  map_rel' := by
    intro n r x
    cases r with
    | order =>
      change criticalPointMap X (x 0) ≤ criticalPointMap X (x 1) ↔ x 0 ≤ x 1
      change (criticalPointMap X (x 0)).val ≤ (criticalPointMap X (x 1)).val ↔
        (x 0).val ≤ (x 1).val
      rw [criticalPointMap_model,criticalPointMap_model]
      exact (embeddingOrderEmbedding (RayMapModel.embedding (RevisedCodingRelations.conjugate (CriticalCopies.total X)))).le_iff_le
    | height =>
      exact criticalPointMap_lt_iff X (x 0) (x 1)
    | diary D hD =>
      change (Increasing (criticalPointMap X ∘ x) ∧ Closed (tupleSet (criticalPointMap X ∘ x)) ∧
        codes (tupleSet (criticalPointMap X ∘ x)) = D.codes) ↔
        Increasing x ∧ Closed (tupleSet x) ∧ codes (tupleSet x) = D.codes
      have hinc : Increasing (criticalPointMap X ∘ x) ↔ Increasing x := by
        constructor
        · intro h i j hij
          exact (criticalPointMap_lt_iff X (x i) (x j)).mp (h hij)
        · intro h i j hij
          exact (criticalPointMap_lt_iff X (x i) (x j)).mpr (h hij)
      rw [hinc,tupleSet_criticalPointMap,RevisedCodingRelations.closed_image_iff,
        GeneralizedNormalization.codes_image]

/-- Tuple preservation from native first-order embeddings implies the
two named finite relation conditions. The converse reconstruction
can then use the independent labelled-diary bridge. -/
noncomputable def codingAction (e : RevisedSparseModel ↪[expandedLanguage] RevisedSparseModel) (w : Word) : Word := by
  classical
  exact if hw : Point w then word (e (ofPoint w hw)) else []

theorem codingAction_word (e : RevisedSparseModel ↪[expandedLanguage] RevisedSparseModel) (x : RevisedSparseModel) :
    codingAction e (word x) = word (e x) := by
  classical
  rw [codingAction,dif_pos (word_point x),ofPoint_word]

theorem codingAction_point (e : RevisedSparseModel ↪[expandedLanguage] RevisedSparseModel) {w : Word}
    (hw : Point w) : Point (codingAction e w) := by
  classical
  rw [codingAction,dif_pos hw]
  exact word_point _

theorem embedding_height (e : RevisedSparseModel ↪[expandedLanguage] RevisedSparseModel) (x y : RevisedSparseModel) :
    (word (e x)).length < (word (e y)).length ↔ (word x).length < (word y).length := by
  let t : Fin 2 → RevisedSparseModel := fun i => if i = 0 then x else y
  have h := e.map_rel' Relation.height t
  change (word (e (t 0))).length < (word (e (t 1))).length ↔
    (word (t 0)).length < (word (t 1)).length at h
  simpa [t] using h

theorem codingAction_height (e : RevisedSparseModel ↪[expandedLanguage] RevisedSparseModel)
    (s t : Word) (hs : Point s) (ht : Point t) (hlt : s.length < t.length) :
    (codingAction e s).length < (codingAction e t).length := by
  classical
  rw [codingAction,dif_pos hs,codingAction,dif_pos ht]
  apply (embedding_height e (ofPoint s hs) (ofPoint t ht)).mpr
  simpa only [word_ofPoint] using hlt

theorem tupleSet_embedding (e : RevisedSparseModel ↪[expandedLanguage] RevisedSparseModel)
    {n : Nat} (x : Fin n → RevisedSparseModel) :
    tupleSet (e ∘ x) = (tupleSet x).image (codingAction e) := by
  unfold tupleSet
  rw [Finset.image_image]
  apply Finset.image_congr
  intro i _
  exact (codingAction_word e (x i)).symm

/-- All actual named diary relations on finite meet-closed sets are
preserved by a native first-order self-embedding. -/
theorem embedding_named_diaries (e : RevisedSparseModel ↪[expandedLanguage] RevisedSparseModel)
    (C : Finset Word) (hne : C.Nonempty) (hC : ∀ w ∈ C, Point w)
    (hcl : Closed C) :
    codes (C.image (codingAction e)) = codes C := by
  classical
  obtain ⟨x,hx,hxC⟩ := exists_increasing_tuple hC
  let D := GeneralizedNormalization.normalize hC hne
  have hD : Closed D.codes := (normalized_closed_iff hne).mpr hcl
  have hrel : Increasing x ∧ Closed (tupleSet x) ∧ codes (tupleSet x) = D.codes := by
    rw [hxC]
    exact ⟨hx,hcl,rfl⟩
  have hpres := (e.map_rel' (Relation.diary D hD) x).mpr hrel
  change Increasing (e ∘ x) ∧ Closed (tupleSet (e ∘ x)) ∧
    codes (tupleSet (e ∘ x)) = D.codes at hpres
  rw [tupleSet_embedding,hxC] at hpres
  exact hpres.2.2

theorem embedding_labelled (e : RevisedSparseModel ↪[expandedLanguage] RevisedSparseModel) :
    ∀ C : Finset Word, (∀ w ∈ C, Point w) → ∀ w ∈ C,
      code (C.image (codingAction e)) (codingAction e w) = code C w :=
  RevisedCodingRelations.labelled_of_named_diaries (codingAction e)
    (codingAction_height e) (embedding_named_diaries e)

end AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion
