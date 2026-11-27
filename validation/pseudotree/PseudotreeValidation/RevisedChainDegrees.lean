import PseudotreeValidation.GenericIncomparables
import PseudotreeValidation.RevisedChainDiaries
import PseudotreeValidation.RevisedRecurrence
import PseudotreeValidation.ExpandedCopyLanguage
import PseudotreeValidation.RevisedExpandedCopyLanguage
import PseudotreeValidation.DegreeAssembly

/-! Exact revised chain degrees from the already proved generalized diary
canonization and recurrence. This avoids a second chain-specific
Milliken argument. The type map is the actual normalized coding set,
not a partition obtained by an abstract isomorphism with the old model. -/
namespace AllThoseBigRamsey.Pseudotree.RevisedChainDegrees
open RayEmbeddings RayMapModel
open RevisedConvention (RevisedSparseModel)
open RevisedDiaryExpansion (word word_injective word_model word_point ofPoint word_ofPoint)
open RevisedChainDiaries (ChainDiary ChainCodes)
open RevisedCodingRelations (model conjugate model_map)
open GeneralizedNormalization (codes rayMap rayMap_codes)
open SparseNormalization (Point)
open scoped FirstOrder

variable {n : Nat}

def chainWords (e : Fin n ↪[language] RevisedSparseModel) : Finset Word :=
  Finset.univ.image (word ∘ e)

theorem words_card (e : Fin n ↪[language] RevisedSparseModel) : (chainWords e).card = n := by
  unfold chainWords
  rw [Finset.card_image_of_injective _ (word_injective.comp e.injective)]
  simp

theorem words_points (e : Fin n ↪[language] RevisedSparseModel) :
    ∀ w ∈ chainWords e, Point w := by
  intro w hw
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
  exact word_point (e i)

theorem words_nonempty (hn : 0 < n) (e : Fin n ↪[language] RevisedSparseModel) :
    (chainWords e).Nonempty := Finset.card_pos.mp (by rw [words_card]; exact hn)

def IsChain (C : Finset Word) : Prop :=
  ∀ s ∈ C, ∀ t ∈ C, model s ≤ model t ∨ model t ≤ model s

theorem words_chain (e : Fin n ↪[language] RevisedSparseModel) : IsChain (chainWords e) := by
  intro s hs t ht
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ht
  simp only [Function.comp_apply,word_model]
  exact (le_total i j).imp
    (fun h => (embedding_le_iff e i j).mpr h)
    (fun h => (embedding_le_iff e j i).mpr h)

theorem words_injective : Function.Injective (chainWords (n := n)) := by
  intro e f h
  have hr : Set.range e = Set.range f := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      have hw : word (e i) ∈ chainWords f := h ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hw
      exact ⟨j,word_injective hj⟩
    · rintro ⟨i,rfl⟩
      have hw : word (f i) ∈ chainWords e := h.symm ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hw
      exact ⟨j,word_injective hj⟩
  exact FirstOrder.Language.Embedding.ext (congrFun
    (((embeddingOrderEmbedding e).strictMono.range_inj_of_wellFoundedLT
      (embeddingOrderEmbedding f).strictMono).mp hr))

theorem chain_image (f : RayStrongMap) {C : Finset Word} (hc : IsChain C) :
    IsChain (C.image f.map) := by
  intro s hs t ht
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ht
  rw [model_map,model_map]
  exact (hc u hu v hv).imp
    (embedding_le_iff (RayMapModel.embedding (conjugate f)) _ _).mpr
    (embedding_le_iff (RayMapModel.embedding (conjugate f)) _ _).mpr

theorem chain_of_image (f : RayStrongMap) {C : Finset Word} (hc : IsChain (C.image f.map)) :
    IsChain C := by
  intro s hs t ht
  have h := hc (f.map s) (Finset.mem_image.mpr ⟨s,hs,rfl⟩)
    (f.map t) (Finset.mem_image.mpr ⟨t,ht,rfl⟩)
  rw [model_map,model_map] at h
  exact h.imp
    (embedding_le_iff (RayMapModel.embedding (conjugate f)) _ _).mp
    (embedding_le_iff (RayMapModel.embedding (conjugate f)) _ _).mp

theorem normalized_chain {C : Finset Word} (hne : C.Nonempty) (hc : IsChain C) :
    IsChain (codes C) := by
  apply chain_of_image (rayMap hne)
  rw [rayMap_codes hne]
  exact hc

noncomputable def typeOf (hn : 0 < n) (e : Fin n ↪[language] RevisedSparseModel) : ChainDiary n :=
  ⟨⟨GeneralizedNormalization.nodes (chainWords e),codes (chainWords e),
    ⟨_,GeneralizedNormalization.normalized_axioms (words_points e) (words_nonempty hn e)⟩,
    (GeneralizedNormalization.codes_card (words_nonempty hn e)).trans (words_card e)⟩,
    normalized_chain (words_nonempty hn e) (words_chain e)⟩

@[simp] theorem typeOf_codes (hn : 0 < n) (e : Fin n ↪[language] RevisedSparseModel) :
    (typeOf hn e).val.codes = codes (chainWords e) := rfl

theorem type_eq_of_codes {D E : ChainDiary n} (h : D.val.codes = E.val.codes) : D = E := by
  apply Subtype.ext
  exact RevisedChainDiaries.generalized_ext (GeneralizedDiary.nodes_eq_of_codes_eq h) h

/-- Convert a literal finite chain of coding points into an actual
embedding of the standard finite chain. -/
theorem realize_words (C : Finset Word) (hC : ∀ w ∈ C, Point w) (hc : IsChain C)
    (hcard : C.card = n) : ∃ e : Fin n ↪[language] RevisedSparseModel, chainWords e = C := by
  classical
  let p (w : ↥C) := ofPoint w.val (hC _ w.property)
  have hp : Function.Injective p := by
    intro s t h
    apply Subtype.ext
    simpa only [p,word_ofPoint] using congrArg word h
  let V : Finset RevisedSparseModel := C.attach.image p
  have hVcard : V.card = n := by
    change (C.attach.image p).card = n
    rw [Finset.card_image_of_injective _ hp,Finset.card_attach,hcard]
  have hVchain (a b : ↥V) : a ≤ b ∨ b ≤ a := by
    obtain ⟨s,_,hs⟩ := Finset.mem_image.mp a.property
    obtain ⟨t,_,ht⟩ := Finset.mem_image.mp b.property
    have h := hc s.val s.property t.val t.property
    have h₁ := word_model (p s)
    have h₂ := word_model (p t)
    rw [show word (p s) = s.val from word_ofPoint _ _,hs] at h₁
    rw [show word (p t) = t.val from word_ofPoint _ _,ht] at h₂
    rw [h₁,h₂] at h
    exact h
  letI : LinearOrder ↥V := {
    toPartialOrder := inferInstance
    le_total := hVchain
    toDecidableLE := Classical.decRel _
    toDecidableEq := Classical.decEq _ }
  let i := Fintype.orderIsoFinOfCardEq (↥V) (by rw [Fintype.card_coe,hVcard])
  let j : Fin n → RevisedSparseModel := fun a => (i a).val
  have hj : Function.Injective j := fun a b h => i.injective (Subtype.ext h)
  have hm : Monotone j := fun _ _ h => i.monotone h
  let e : Fin n ↪[language] RevisedSparseModel :=
    embeddingOfInfMap j hj (by
      intro a b
      rcases le_total a b with h | h
      · rw [inf_eq_left.mpr h,inf_eq_left.mpr (hm h)]
      · rw [inf_eq_right.mpr h,inf_eq_right.mpr (hm h)])
  refine ⟨e,?_⟩
  ext w
  constructor
  · intro hw
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hw
    obtain ⟨s,_,hs⟩ := Finset.mem_image.mp (i a).property
    have he : word (p s) = w := by
      change word (j a) = w at ha
      rw [hs]
      exact ha
    rw [show word (p s) = s.val from word_ofPoint _ _] at he
    exact he ▸ s.property
  · intro hw
    let v := p ⟨w,hw⟩
    have hv : v ∈ V := Finset.mem_image.mpr ⟨⟨w,hw⟩,Finset.mem_attach _ _,rfl⟩
    let a := i.symm ⟨v,hv⟩
    refine Finset.mem_image.mpr ⟨a,Finset.mem_univ _,?_⟩
    change word (i (i.symm ⟨v,hv⟩)).val = w
    rw [OrderIso.apply_symm_apply]
    exact word_ofPoint w (hC w hw)

/-- Every independently specified revised chain diary occurs on the
actual sparse set and its normalized label is exactly the given diary. -/
theorem realized (hn : 0 < n) (D : ChainDiary n) :
    ∃ e : Fin n ↪[language] RevisedSparseModel, typeOf hn e = D := by
  classical
  let C := D.val.codes.image FIFOLifting.HFin
  obtain ⟨g,_,hg⟩ := FIFOLifting.diary_lift D.val RayStrongMap.identity
  have heq : D.val.codes.image g.map = C := by
    apply Finset.image_congr
    intro w hw
    exact hg w hw
  have hc : IsChain C := by
    rw [← heq]
    exact chain_image g D.property
  have hcard : C.card = n := by
    rw [← heq,Finset.card_image_of_injective _ g.injective,D.val.size]
  obtain ⟨hP,hNorm,_⟩ := GeneralizedCanonization.literal_realized D.val
  obtain ⟨e,he⟩ := realize_words C hP hc hcard
  refine ⟨e,type_eq_of_codes ?_⟩
  rw [typeOf_codes,he]
  exact hNorm

/-- Forget only the expansion relations, preserving the actual
revised functional reduct. -/
noncomputable def reductCritical (X : CriticalCopies.CriticalMap) :
    RevisedSparseModel ↪[language] RevisedSparseModel :=
  embeddingOfInfMap (RevisedDiaryExpansion.criticalPointMap X)
    (RevisedDiaryExpansion.criticalEmbedding X).injective
    (RevisedDiaryExpansion.criticalPointMap_inf X)

theorem words_comp (X : CriticalCopies.CriticalMap) (e : Fin n ↪[language] RevisedSparseModel) :
    chainWords ((reductCritical X).comp e) = (chainWords e).image (CriticalCopies.total X).map := by
  unfold chainWords
  rw [Finset.image_image]
  apply Finset.image_congr
  intro a _
  exact RevisedDiaryExpansion.criticalPointMap_word X (e a)

theorem type_preserved (hn : 0 < n) (X : CriticalCopies.CriticalMap)
    (e : Fin n ↪[language] RevisedSparseModel) :
    typeOf hn ((reductCritical X).comp e) = typeOf hn e := by
  apply type_eq_of_codes
  rw [typeOf_codes,typeOf_codes,words_comp,GeneralizedNormalization.codes_image]

/-- Recurrence makes each of the literal normalized chain types unavoidable. -/
theorem unavoidable (hn : 0 < n) (f : RevisedSparseModel ↪[language] RevisedSparseModel)
    (D : ChainDiary n) : ∃ e : Fin n ↪[language] RevisedSparseModel, typeOf hn (f.comp e) = D := by
  obtain ⟨e₀,he₀⟩ := realized hn D
  obtain ⟨g,hg⟩ := RevisedDiaryExpansion.native_recurrence f
  obtain ⟨X,rfl⟩ := RevisedDiaryExpansion.criticalEmbedding_surjective g
  have hsub : Set.range ((reductCritical X).comp e₀) ⊆ Set.range f := by
    rintro _ ⟨a,rfl⟩
    exact hg ⟨e₀ a,rfl⟩
  obtain ⟨e,he⟩ := DegreeAssembly.factor_embedding f ((reductCritical X).comp e₀) hsub
  exact ⟨e,by rw [he,type_preserved hn X e₀,he₀]⟩

/-- The complete finite family of literal chain diaries canonizes every
finite colouring of chains, with the actual normalized type labels. -/
theorem canonical (hn : 0 < n) {r : Nat}
    (χ : (Fin n ↪[language] RevisedSparseModel) → Fin (r+1)) :
    ∃ g : RevisedSparseModel ↪[language] RevisedSparseModel,
      ∃ c : ChainDiary n → Fin (r+1), ∀ e, χ (g.comp e) = c (typeOf hn e) := by
  classical
  let colour (C : Finset Word) : Fin (r+1) :=
    if h : ∃ e : Fin n ↪[language] RevisedSparseModel, chainWords e = C then χ h.choose else 0
  have hχ (e : Fin n ↪[language] RevisedSparseModel) : colour (chainWords e) = χ e := by
    have h : ∃ f : Fin n ↪[language] RevisedSparseModel, chainWords f = chainWords e := ⟨e,rfl⟩
    simp only [colour,dif_pos h]
    rw [words_injective h.choose_spec]
  let ds : List GeneralizedCanonization.DiaryIndex :=
    ((Finset.univ : Finset (ChainDiary n)).toList).map (fun D => ⟨n,D.val⟩)
  obtain ⟨X,hX⟩ := GeneralizedCanonization.finite_fragment ds colour
  have h (D : ChainDiary n) : ∃ c : Fin (r+1), ∀ e : Fin n ↪[language] RevisedSparseModel,
      typeOf hn e = D → χ ((reductCritical X).comp e) = c := by
    obtain ⟨c,hc⟩ := hX ⟨n,D.val⟩ (by
      apply List.mem_map.mpr
      exact ⟨D,by simp,rfl⟩)
    refine ⟨c,fun e he => ?_⟩
    have hnorm : codes (chainWords e) = D.val.codes :=
      congrArg (fun t : ChainDiary n => t.val.codes) he
    have hmono := hc (chainWords e) (words_nonempty hn e) (words_points e) hnorm
    rw [← words_comp X e,hχ] at hmono
    exact hmono
  choose c hc using h
  exact ⟨reductCritical X,c,fun e => hc (typeOf hn e) e rfl⟩

/-- Exact finite big Ramsey bound for the literal revised sparse model,
with the number of independently defined rightmost chain diaries. -/
theorem exact_degree (hn : 0 < n) :
    GenericIncomparables.FunctionalBigRamseyBound (Fin n) RevisedSparseModel
      (diaryCount true n 1) ∧
    ∀ d, GenericIncomparables.FunctionalBigRamseyBound (Fin n) RevisedSparseModel d →
      diaryCount true n 1 ≤ d := by
  classical
  constructor
  · intro r hr χ
    cases r with
    | zero => omega
    | succ r =>
      obtain ⟨g,c,hc⟩ := canonical hn χ
      refine ⟨g,Finset.univ.image c,?_,?_⟩
      · exact Finset.card_image_le.trans (by rw [Finset.card_univ,RevisedChainDiaries.chainDiary_card])
      · intro e
        rw [hc]
        exact Finset.mem_image.mpr ⟨typeOf hn e,Finset.mem_univ _,rfl⟩
  · intro d hd
    have hne : Nonempty (ChainDiary n) := by
      cases n with
      | zero => omega
      | succ k => exact ⟨RevisedChainDiaries.fromPaper (longestDiary k).toPaper⟩
    let r := Fintype.card (ChainDiary n)
    let encode := Fintype.equivFin (ChainDiary n)
    have hr : 0 < r := Fintype.card_pos_iff.mpr hne
    obtain ⟨f,P,hcard,hP⟩ := hd r hr (fun e => encode (typeOf hn e))
    have hfull : (Finset.univ : Finset (Fin r)) ⊆ P := by
      intro i _
      obtain ⟨e,he⟩ := unavoidable hn f (encode.symm i)
      simpa only [he,Equiv.apply_symm_apply] using hP e
    have hcount : r ≤ P.card := by simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card hfull
    rw [← RevisedChainDiaries.chainDiary_card n]
    exact hcount.trans hcard

end AllThoseBigRamsey.Pseudotree.RevisedChainDegrees
