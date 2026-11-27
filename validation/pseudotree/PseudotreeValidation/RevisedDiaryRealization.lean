import PseudotreeValidation.RevisedCopyCanonization
import PseudotreeValidation.GenericIncomparables

/-! Actual labeled realization of abstract generalized diaries, and
infinitely many realized diary labels for every nonchain. The former uses
the existing finite FIFO lift, not a choice of an unrelated copy; the
latter follows from the established infinite big Ramsey degree theorem
and finite-fragment canonization. -/
namespace AllThoseBigRamsey.Pseudotree.RevisedDiaryRealization

open RayEmbeddings RayMapModel
open RevisedConvention (RevisedSparseModel)
open RevisedDiaryExpansion (word word_model word_ofPoint ofPoint)
open RevisedCodingRelations (model model_injective model_map conjugate)
open RevisedCopyCanonization (words words_points words_nonempty diary diary_copyOf)
open GeneralizedNormalization (code codes rayMap rayMap_code rayMap_codes)
open SparseNormalization (Point)
open NoInfiniteCanonical (Copy copyOf representative representative_range factorThrough factorThrough_comp)
open scoped FirstOrder

abbrev P := RevisedSparseModel
variable {A : Type} [language.Structure A] [Fintype A]

theorem word_mem (e : A ↪[language] P) (a : A) : word (e a) ∈ words e :=
  Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩

/-- A labeled abstract diary, as in the paper: its code set is exactly
the range of the specified functional embedding of A in the ambient
revised ternary model. -/
def IsDiaryOf {n : Nat} (D : GeneralizedDiary n) (ι : A ↪[language] TernaryModel) : Prop :=
  Set.range ι = model '' (D.codes : Set Word)

/-- Realize the prescribed pair (D,ι) with exact normalized code labels
on the actual unchanged sparse queue. -/
theorem realize_pair {n : Nat} (D : GeneralizedDiary n) (ι : A ↪[language] TernaryModel)
    (hι : IsDiaryOf D ι) :
    ∃ e : A ↪[language] P,
      codes (words e) = D.codes ∧
      (∀ a, model (code (words e) (word (e a))) = ι a) := by
  classical
  obtain ⟨g,_,hg⟩ := FIFOLifting.diary_lift D RayStrongMap.identity
  have hιw (a : A) : ∃ w ∈ D.codes, model w = ι a := by
    have h : ι a ∈ model '' (D.codes : Set Word) := hι ▸ Set.mem_range_self a
    obtain ⟨w,hw,he⟩ := h
    exact ⟨w,hw,he⟩
  have hP (w : Word) (hw : w ∈ D.codes) : Point (g.map w) := by
    rw [hg w hw]
    exact FIFOLifting.HFin_point w
  let F := (RayMapModel.embedding (conjugate g)).comp ι
  have hF (a : A) {w : Word} (hw : model w = ι a) : F a = model (g.map w) := by
    change RayMapModel.modelMap (conjugate g) (ι a) = model (g.map w)
    rw [← hw,model_map]
  have hs : Set.range F ⊆ Set.range RevisedSparseModel.inclusion := by
    rintro _ ⟨a,rfl⟩
    obtain ⟨w,hw,hwa⟩ := hιw a
    refine ⟨ofPoint (g.map w) (hP w hw),?_⟩
    change (ofPoint (g.map w) (hP w hw)).val = F a
    rw [hF a hwa,← word_model (ofPoint (g.map w) (hP w hw)),word_ofPoint]
  let e := factorThrough RevisedSparseModel.inclusion F hs
  have he := factorThrough_comp RevisedSparseModel.inclusion F hs
  have hword (a : A) {w : Word} (hw : model w = ι a) :
      word (e a) = g.map w := by
    apply model_injective
    rw [word_model,← hF a hw]
    exact congrArg (fun E : A ↪[language] TernaryModel => E a) he
  have hwords : words e = D.codes.image g.map := by
    ext v
    constructor
    · intro hv
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨w,hw,hwa⟩ := hιw a
      exact Finset.mem_image.mpr ⟨w,hw,(hword a hwa).symm⟩
    · intro hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      have hm : model w ∈ Set.range ι := by
        rw [hι]
        exact ⟨w,hw,rfl⟩
      obtain ⟨a,ha⟩ := hm
      exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,hword a ha.symm⟩
  refine ⟨e,?_,?_⟩
  · rw [hwords,GeneralizedNormalization.image_recovery]
  · intro a
    obtain ⟨w,hw,hwa⟩ := hιw a
    rw [hwords,hword a hwa,GeneralizedNormalization.labelled_image_recovery D g hw]
    exact hwa

variable [Nonempty A]

/-- Conversely the actual normalized code map of every finite reduct
embedding is itself a functional embedding into the revised word model,
with range exactly the normalized diary. This recovers the prescribed
labels even for nonrigid A. -/
theorem normalized_pair (e : A ↪[language] P) :
    ∃ ι : A ↪[language] TernaryModel,
      IsDiaryOf (GeneralizedNormalization.normalize (words_points e) (words_nonempty e)) ι ∧
      ∀ a, ι a = model (code (words e) (word (e a))) := by
  classical
  let f := rayMap (words_nonempty e)
  let R := RayMapModel.embedding (conjugate f)
  let E := RevisedSparseModel.inclusion.comp e
  let L (a : A) := model (code (words e) (word (e a)))
  have hRL (a : A) : R (L a) = E a := by
    change RayMapModel.modelMap (conjugate f) (model (code (words e) (word (e a)))) = (e a).val
    rw [← model_map,rayMap_code (words_nonempty e) (word_mem e a),word_model]
  have hs : Set.range E ⊆ Set.range R := by
    rintro _ ⟨a,rfl⟩
    exact ⟨L a,hRL a⟩
  let ι := factorThrough R E hs
  have hcomp := factorThrough_comp R E hs
  have hι (a : A) : ι a = L a := by
    apply R.injective
    rw [hRL]
    exact congrArg (fun G : A ↪[language] TernaryModel => G a) hcomp
  refine ⟨ι,?_,hι⟩
  change Set.range ι = model '' (codes (words e) : Set Word)
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨code (words e) (word (e a)),
      Finset.mem_image.mpr ⟨word (e a),word_mem e a,rfl⟩,(hι a).symm⟩
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨a,hι a⟩

/-- The copy-level diary labels are exactly the abstract diaries of A. -/
theorem diary_labels_iff (V : Finset Word) :
    (∃ C : Copy A P, diary C = V) ↔
      ∃ n : Nat, ∃ D : GeneralizedDiary n, ∃ ι : A ↪[language] TernaryModel,
        D.codes = V ∧ IsDiaryOf D ι := by
  constructor
  · rintro ⟨C,hC⟩
    let e := representative C
    let D := GeneralizedNormalization.normalize (words_points e) (words_nonempty e)
    obtain ⟨ι,hι,_⟩ := normalized_pair e
    exact ⟨(words e).card,D,ι,hC,hι⟩
  · rintro ⟨n,D,ι,hD,hι⟩
    obtain ⟨e,he,_⟩ := realize_pair D ι hι
    exact ⟨copyOf e,(diary_copyOf e).trans (he.trans hD)⟩

/-- There are infinitely many realized generalized diary labels for every
finite nonchain. A finite set of labels would give a finite bound for the
image-invariant oscillation colourings, contrary to their checked lower bound. -/
theorem infinite_nonchain_diaries [SemilatticeInf A] [MeetsInterpreted A]
    (hA : Nonempty (A ↪[language] P)) {x y : A}
    (hxy : ¬ x ≤ y) (hyx : ¬ y ≤ x) :
    ¬ (Set.range (diary (A := A))).Finite := by
  classical
  intro hfin
  let E := hfin.toFinset
  have hE (D : Finset Word) (hD : D ∈ E) : ∃ C : Copy A P, diary C = D :=
    hfin.mem_toFinset.mp hD
  obtain ⟨r,hr,χ,hInv,hlarge⟩ := GenericIncomparables.arbitrarily_many_copy_colours
    (GenericIncomparables.systemOfCountable RevisedSparseModel.predecessors_comparable)
    (fun {u v} h => RevisedSparseModel.exists_opposite_cone u v h)
    RevisedSparseModel.isUltrahomogeneous hA hxy hyx E.card
  cases r with
  | zero => omega
  | succ r =>
    let χ' (C : Copy A P) := χ (representative C)
    have hχ (e : A ↪[language] P) : χ' (copyOf e) = χ e :=
      hInv _ _ (representative_range (copyOf e))
    obtain ⟨g,_,_,hcanon⟩ := RevisedCopyCanonization.finite_fragment E hE χ'
      (FirstOrder.Language.Embedding.refl language P)
    let c (i : ↥E) : Fin (r+1) := (hcanon i.val i.property).choose
    let palette := E.attach.image c
    have hcard : palette.card ≤ E.card := Finset.card_image_le.trans (by rw [Finset.card_attach])
    have hcover (e : A ↪[language] P) : χ (g.comp e) ∈ palette := by
      have hm : diary (copyOf (g.comp e)) ∈ E :=
        hfin.mem_toFinset.mpr ⟨copyOf (g.comp e),rfl⟩
      let i : ↥E := ⟨diary (copyOf (g.comp e)),hm⟩
      have hc := (hcanon i.val i.property).choose_spec e rfl
      change χ' (copyOf (g.comp e)) = c i at hc
      rw [hχ] at hc
      exact Finset.mem_image.mpr ⟨i,Finset.mem_attach _ _,hc.symm⟩
    exact (not_lt_of_ge hcard) (hlarge g palette hcover)

end AllThoseBigRamsey.Pseudotree.RevisedDiaryRealization
