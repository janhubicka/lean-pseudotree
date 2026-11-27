import PseudotreeValidation.RevisedExpansionClassification

/-! Generalized big Ramsey structure: each labeled induced expansion
is unavoidable and its embedding colorings canonize inside any given
reduct self-copy. The finite-fragment theorem is on literal copies;
within one expanded type, a copy determines its embedding. -/
namespace AllThoseBigRamsey.Pseudotree.RevisedExpansionClassification
open RayEmbeddings
open scoped FirstOrder
open RevisedDiaryExpansion (word word_injective)
open RevisedCopyCanonization (words words_nonempty diary diary_copyOf reductCritical critical_inside words_comp)
open RevisedDiaryRealization (word_mem)
open NoInfiniteCanonical (Copy copyOf copy_range_eq factorThrough factorThrough_comp)
open GeneralizedNormalization (code codes rayMap_code)

variable {A : Type} [SemilatticeInf A] [language.Structure A] [MeetsInterpreted A]
  [Fintype A] [Nonempty A]

theorem critical_labels (X : CriticalCopies.CriticalMap) (e : A ↪[language] P) (a : A) :
    label ((reductCritical X).comp e) a = label e a := by
  unfold label
  rw [words_comp]
  change code ((words e).image (CriticalCopies.total X).map)
    (word (RevisedDiaryExpansion.criticalPointMap X (e a))) = code (words e) (word (e a))
  rw [RevisedDiaryExpansion.criticalPointMap_word]
  exact GeneralizedNormalization.code_image (CriticalCopies.total X) (words e) (word_mem e a)

theorem expansion_unavoidable (f : P ↪[language] P) (e₀ : A ↪[language] P) :
    ∃ e : A ↪[language] P, induced (f.comp e) = induced e₀ := by
  obtain ⟨X,hX⟩ := critical_inside f
  let g := (reductCritical X).comp e₀
  have hs : Set.range g ⊆ Set.range f := by
    rintro _ ⟨a,rfl⟩
    exact hX ⟨e₀ a,rfl⟩
  refine ⟨factorThrough f g hs,?_⟩
  rw [factorThrough_comp]
  exact (induced_eq_iff_labels g e₀).mpr (critical_labels X e₀)

theorem embedding_eq_of_expansion_and_range {e g : A ↪[language] P}
    (ht : induced e = induced g) (hr : Set.range e = Set.range g) : e = g := by
  have hw := (RevisedCopyCanonization.words_range_iff e g).mpr hr
  have hl := (induced_eq_iff_labels e g).mp ht
  apply FirstOrder.Language.Embedding.ext
  intro a
  apply word_injective
  have ha : word (g a) ∈ words e := by rw [hw]; exact word_mem g a
  have h := hl a
  change code (words e) (word (e a)) = code (words g) (word (g a)) at h
  rw [← hw] at h
  exact GeneralizedNormalization.code_injective (words_nonempty e) (word_mem e a) ha h

abbrev ExpansionFiber (e₀ : A ↪[language] P) :=
  {e : A ↪[language] P // induced e = induced e₀}

/-- Actual local generalized BRS property on the labeled embedding fiber. -/
theorem local_embedding_canonization (e₀ : A ↪[language] P) {r : Nat}
    (χ : ExpansionFiber e₀ → Fin (r+1)) (f : P ↪[language] P) :
    ∃ g : P ↪[language] P, Set.range g ⊆ Set.range f ∧
      ∃ c : Fin (r+1), ∀ (e : A ↪[language] P)
        (he : induced (g.comp e) = induced e₀), χ ⟨g.comp e,he⟩ = c := by
  classical
  let χ' (C : Copy A P) : Fin (r+1) :=
    if h : ∃ e : ExpansionFiber e₀, copyOf e.val = C then χ h.choose else 0
  have hχ (e : A ↪[language] P) (he : induced e = induced e₀) :
      χ' (copyOf e) = χ ⟨e,he⟩ := by
    have h : ∃ u : ExpansionFiber e₀, copyOf u.val = copyOf e := ⟨⟨e,he⟩,rfl⟩
    simp only [χ',dif_pos h]
    apply congrArg χ
    apply Subtype.ext
    exact embedding_eq_of_expansion_and_range (h.choose.property.trans he.symm)
      ((copy_range_eq _ _).mp h.choose_spec)
  let D := diary (copyOf e₀)
  obtain ⟨g,hg,_,hcanon⟩ := RevisedCopyCanonization.finite_fragment {D}
    (fun B hB => ⟨copyOf e₀,(Finset.mem_singleton.mp hB).symm⟩) χ' f
  obtain ⟨c,hc⟩ := hcanon D (by simp)
  refine ⟨g,hg,c,?_⟩
  intro e he
  have hd : diary (copyOf (g.comp e)) = D := by
    unfold D
    rw [diary_copyOf,diary_copyOf]
    exact codes_of_same ((induced_eq_iff _ _).mp he)
  have h := hc e hd
  rw [hχ (g.comp e) he] at h
  exact h

end AllThoseBigRamsey.Pseudotree.RevisedExpansionClassification
