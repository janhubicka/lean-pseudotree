import PseudotreeValidation.RevisedRecurrence
import PseudotreeValidation.RevisedExpandedCopyLanguage
import PseudotreeValidation.CopyPartitionTransfer

/-! Native form of the manuscript's finite-fragment theorem: literal
copies of an arbitrary nonempty finite functional structure, a prescribed
reduct self-copy, exact normalized diary labels, minimal unavoidability,
and sharpness. This uses the same finite-code-set canonization and actual
revised recurrence as the chain-degree proof. -/
namespace AllThoseBigRamsey.Pseudotree.RevisedCopyCanonization
open RayEmbeddings
open RevisedConvention (RevisedSparseModel)
open RevisedDiaryExpansion (word word_point word_injective)
open NoInfiniteCanonical (Copy copyOf copy_range_eq representative representative_range)
open SparseNormalization (Point)
open GeneralizedNormalization (codes)
open scoped FirstOrder

abbrev P := RevisedSparseModel
variable {A : Type} [language.Structure A] [Fintype A]

def words (e : A ↪[language] P) : Finset Word := Finset.univ.image (word ∘ e)

theorem words_points (e : A ↪[language] P) : ∀ w ∈ words e, Point w := by
  intro w hw
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hw
  exact word_point (e a)

theorem words_range_iff (e g : A ↪[language] P) :
    words e = words g ↔ Set.range e = Set.range g := by
  constructor
  · intro h
    have hsub (u v : A ↪[language] P) (he : words u = words v) :
        Set.range u ⊆ Set.range v := by
      rintro _ ⟨a,rfl⟩
      have hw : word (u a) ∈ words u := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
      rw [he] at hw
      obtain ⟨b,_,hb⟩ := Finset.mem_image.mp hw
      exact ⟨b,word_injective hb⟩
    exact Set.Subset.antisymm (hsub e g h) (hsub g e h.symm)
  · intro h
    have hsub (u v : A ↪[language] P) (he : Set.range u ⊆ Set.range v) :
        words u ⊆ words v := by
      intro w hw
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨b,hb⟩ := he (Set.mem_range_self a)
      exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,congrArg word hb⟩
    exact Finset.Subset.antisymm (hsub e g (by rw [h])) (hsub g e (by rw [h]))

/-- The actual finite set of code words of a literal copy is independent
of the chosen labelling. -/
noncomputable def diary (C : Copy A P) : Finset Word := codes (words (representative C))

@[simp] theorem diary_copyOf (e : A ↪[language] P) : diary (copyOf e) = codes (words e) := by
  unfold diary
  rw [(words_range_iff _ _).mpr (representative_range (copyOf e))]

theorem copy_comp_congr (f : P ↪[language] P) {e g : A ↪[language] P}
    (h : copyOf e = copyOf g) : copyOf (f.comp e) = copyOf (f.comp g) := by
  have h' := (copy_range_eq _ _).mp h
  apply (copy_range_eq _ _).mpr
  have H (u v : A ↪[language] P) (huv : Set.range u ⊆ Set.range v) :
      Set.range (f.comp u) ⊆ Set.range (f.comp v) := by
    rintro _ ⟨a,rfl⟩
    obtain ⟨b,hb⟩ := huv (Set.mem_range_self a)
    exact ⟨b,congrArg f hb⟩
  exact Set.Subset.antisymm (H e g (by rw [h'])) (H g e (by rw [h']))

noncomputable def reductCritical (X : CriticalCopies.CriticalMap) : P ↪[language] P :=
  embeddingOfInfMap (RevisedDiaryExpansion.criticalPointMap X)
    (RevisedDiaryExpansion.criticalEmbedding X).injective
    (RevisedDiaryExpansion.criticalPointMap_inf X)

theorem words_comp (X : CriticalCopies.CriticalMap) (e : A ↪[language] P) :
    words ((reductCritical X).comp e) = (words e).image (CriticalCopies.total X).map := by
  unfold words
  rw [Finset.image_image]
  apply Finset.image_congr
  intro a _
  exact RevisedDiaryExpansion.criticalPointMap_word X (e a)

theorem diary_preserved (X : CriticalCopies.CriticalMap) (e : A ↪[language] P) :
    diary (copyOf ((reductCritical X).comp e)) = diary (copyOf e) := by
  simp only [diary_copyOf,words_comp,GeneralizedNormalization.codes_image]

theorem critical_inside (f : P ↪[language] P) :
    ∃ X : CriticalCopies.CriticalMap, Set.range (reductCritical X) ⊆ Set.range f := by
  obtain ⟨g,hg⟩ := RevisedDiaryExpansion.native_recurrence f
  obtain ⟨X,rfl⟩ := RevisedDiaryExpansion.criticalEmbedding_surjective g
  exact ⟨X,hg⟩

/-- Every realized diary occurs in every reduct copy. -/
theorem unavoidable (f : P ↪[language] P) (C : Copy A P) :
    ∃ e : A ↪[language] P, diary (copyOf (f.comp e)) = diary C := by
  obtain ⟨X,hX⟩ := critical_inside f
  let g := (reductCritical X).comp (representative C)
  have hs : Set.range g ⊆ Set.range f := by
    rintro _ ⟨a,rfl⟩
    exact hX ⟨representative C a,rfl⟩
  let e := NoInfiniteCanonical.factorThrough f g hs
  refine ⟨e,?_⟩
  rw [NoInfiniteCanonical.factorThrough_comp]
  change diary (copyOf ((reductCritical X).comp (representative C))) = diary C
  rw [diary_preserved,NoInfiniteCanonical.representative_copy]

variable [Nonempty A]

theorem words_nonempty (e : A ↪[language] P) : (words e).Nonempty := by
  obtain ⟨a⟩ := ‹Nonempty A›
  exact ⟨word (e a),Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩⟩

/-- Given any finite family of realized normalized labels and any reduct
copy, one smaller reduct copy simultaneously canonizes all those labels
and preserves the original labels. The input colour is on literal copies,
not on labelled embeddings. -/
theorem finite_fragment (E : Finset (Finset Word))
    (hE : ∀ D ∈ E, ∃ C : Copy A P, diary C = D)
    {r : Nat} (χ : Copy A P → Fin (r+1)) (f : P ↪[language] P) :
    ∃ g : P ↪[language] P, Set.range g ⊆ Set.range f ∧
      (∀ e : A ↪[language] P, diary (copyOf (g.comp e)) = diary (copyOf e)) ∧
      ∀ D ∈ E, ∃ c : Fin (r+1), ∀ e : A ↪[language] P,
        diary (copyOf (g.comp e)) = D → χ (copyOf (g.comp e)) = c := by
  classical
  obtain ⟨X₀,h₀⟩ := critical_inside f
  let g₀ := reductCritical X₀
  let pick (i : ↥E) := (hE i.val i.property).choose
  have hpick (i : ↥E) : diary (pick i) = i.val := (hE i.val i.property).choose_spec
  let W (i : ↥E) := words (representative (pick i))
  let D (i : ↥E) := GeneralizedNormalization.normalize
    (words_points (representative (pick i))) (words_nonempty (representative (pick i)))
  let ds : List GeneralizedCanonization.DiaryIndex :=
    E.attach.toList.map (fun i => ⟨(W i).card,D i⟩)
  let colour (C : Finset Word) : Fin (r+1) :=
    if h : ∃ e : A ↪[language] P, words e = C then χ (copyOf (g₀.comp h.choose)) else 0
  have hχ (e : A ↪[language] P) : colour (words e) = χ (copyOf (g₀.comp e)) := by
    have h : ∃ u : A ↪[language] P, words u = words e := ⟨e,rfl⟩
    simp only [colour,dif_pos h]
    exact congrArg χ (copy_comp_congr g₀ ((copy_range_eq _ _).mpr
      ((words_range_iff _ _).mp h.choose_spec)))
  obtain ⟨X₁,h₁⟩ := GeneralizedCanonization.finite_fragment ds colour
  let g₁ := reductCritical X₁
  let g := g₀.comp g₁
  have hg (e : A ↪[language] P) : g.comp e = g₀.comp (g₁.comp e) := by
    apply FirstOrder.Language.Embedding.ext
    intro a
    rfl
  have hpres (e : A ↪[language] P) : diary (copyOf (g.comp e)) = diary (copyOf e) := by
    rw [hg]
    exact (diary_preserved X₀ (g₁.comp e)).trans (diary_preserved X₁ e)
  refine ⟨g,?_,hpres,?_⟩
  · rintro _ ⟨x,rfl⟩
    exact h₀ ⟨g₁ x,rfl⟩
  · intro B hB
    let i : ↥E := ⟨B,hB⟩
    have hmem : (⟨(W i).card,D i⟩ : GeneralizedCanonization.DiaryIndex) ∈ ds := by
      apply List.mem_map.mpr
      exact ⟨i,by simp,rfl⟩
    obtain ⟨c,hc⟩ := h₁ _ hmem
    refine ⟨c,fun e he => ?_⟩
    have hnorm : codes (words e) = (D i).codes := by
      change codes (words e) = diary (pick i)
      rw [hpick]
      exact (diary_copyOf e).symm.trans ((hpres e).symm.trans he)
    have hm := hc (words e) (words_nonempty e) (words_points e) hnorm
    rw [← words_comp X₁ e,hχ] at hm
    simpa only [hg] using hm

/-- A partition properly refining the diary partition cannot be unavoidable.
This formalizes minimality for arbitrary finite nonempty A, without any
rigidity assumption. -/
theorem no_proper_unavoidable_refinement {β : Type*} (γ : Copy A P → β)
    (href : ∀ C D, γ C = γ D → diary C = diary D)
    {C D : Copy A P} (hsame : diary C = diary D) (hsplit : γ C ≠ γ D) :
    ¬(∀ f : P ↪[language] P, ∀ V : Copy A P,
      ∃ e : A ↪[language] P, γ (copyOf (f.comp e)) = γ V) := by
  classical
  intro h
  let χ (V : Copy A P) : Fin 2 := if γ V = γ C then 0 else 1
  obtain ⟨g,_,_,hg⟩ := finite_fragment {diary C}
    (fun B hB => ⟨C,(Finset.mem_singleton.mp hB).symm⟩)
    χ (FirstOrder.Language.Embedding.refl language P)
  obtain ⟨c,hc⟩ := hg (diary C) (by simp)
  obtain ⟨e,he⟩ := h g C
  obtain ⟨u,hu⟩ := h g D
  have hec := hc e (href _ _ he)
  have huc := hc u ((href _ _ hu).trans hsame.symm)
  have hz : χ (copyOf (g.comp e)) = 0 := by simp [χ,he]
  have ho : χ (copyOf (g.comp u)) = 1 := by simp [χ,hu,Ne.symm hsplit]
  rw [hz] at hec
  rw [ho] at huc
  exact (by decide : (0 : Fin 2) ≠ 1) (hec.trans huc.symm)

/-- One fixed finite colouring witnesses sharpness of the bound on each
prescribed finite family, including the empty family. Every one of the
distinct colours indexed by E occurs in every reduct copy. -/
theorem sharpness (E : Finset (Finset Word))
    (hE : ∀ D ∈ E, ∃ C : Copy A P, diary C = D) :
    ∃ χ : Copy A P → Option ↥E,
      ∀ f : P ↪[language] P, ∀ i : ↥E, ∃ e : A ↪[language] P,
        diary (copyOf (f.comp e)) = i.val ∧ χ (copyOf (f.comp e)) = some i := by
  classical
  let χ (C : Copy A P) : Option ↥E :=
    if h : diary C ∈ E then some ⟨diary C,h⟩ else none
  refine ⟨χ,fun f i => ?_⟩
  obtain ⟨C,hC⟩ := hE i.val i.property
  obtain ⟨e,he⟩ := unavoidable f C
  have hi : diary (copyOf (f.comp e)) = i.val := he.trans hC
  refine ⟨e,hi,?_⟩
  have hm : diary (copyOf (f.comp e)) ∈ E := hi.symm ▸ i.property
  change (if h : diary (copyOf (f.comp e)) ∈ E then some ⟨_,h⟩ else none) = some i
  rw [dif_pos hm]
  exact congrArg some (Subtype.ext hi)

end AllThoseBigRamsey.Pseudotree.RevisedCopyCanonization
