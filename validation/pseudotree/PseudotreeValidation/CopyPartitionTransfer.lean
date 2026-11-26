import PseudotreeValidation.NoInfiniteCanonical

/-! Transfer the obstruction from embeddings to literal copies. A fibre is
indexed by all self-embeddings of the finite domain; no rigidity is assumed.
The auxiliary argument works for any functional first-order language used here. -/
namespace AllThoseBigRamsey.Pseudotree.NoInfiniteCanonical
open FirstOrder
open scoped FirstOrder

section Factor
variable {A B M : Type*} [language.Structure A] [language.Structure B]
    [language.Structure M]

/-- Pull an embedding back through another embedding whose range contains it. -/
noncomputable def factorThrough (f : B ↪[language] M) (e : A ↪[language] M)
    (h : Set.range e ⊆ Set.range f) : A ↪[language] B :=
  f.equivRange.symm.toEmbedding.comp
    (FirstOrder.Language.Embedding.codRestrict f.toHom.range e
      (fun a => h (Set.mem_range_self a)))

theorem factorThrough_comp (f : B ↪[language] M) (e : A ↪[language] M)
    (h : Set.range e ⊆ Set.range f) :
    f.comp (factorThrough f e h) = e := by
  apply FirstOrder.Language.Embedding.ext
  intro a
  let x : f.toHom.range := ⟨e a,h (Set.mem_range_self a)⟩
  change f (f.equivRange.symm x) = e a
  exact congrArg (fun z : f.toHom.range => (z : M)) (f.equivRange.apply_symm_apply x)

theorem comp_cancel_left (f : B ↪[language] M)
    {e g : A ↪[language] B} (h : f.comp e = f.comp g) : e = g := by
  apply FirstOrder.Language.Embedding.ext
  intro a
  apply f.injective
  exact congrArg (fun v : A ↪[language] M => v a) h

end Factor

section Transfer
variable {A M : Type*} [language.Structure A] [language.Structure M]

/-- A literal copy is a subset which is the range of an actual embedding. -/
abbrev Copy (A M : Type*) [language.Structure A] [language.Structure M] :=
  ↥(Set.range (fun e : A ↪[language] M => Set.range e))

def copyOf (e : A ↪[language] M) : Copy A M := ⟨Set.range e,⟨e,rfl⟩⟩

noncomputable def representative (C : Copy A M) : A ↪[language] M :=
  C.property.choose

theorem representative_range (C : Copy A M) :
    Set.range (representative C) = C.val := C.property.choose_spec

theorem representative_copy (C : Copy A M) :
    copyOf (representative C) = C :=
  Subtype.ext (representative_range C)

theorem copy_range_eq (e g : A ↪[language] M) :
    copyOf e = copyOf g ↔ Set.range e = Set.range g := by
  constructor
  · intro h
    exact congrArg (fun C : Copy A M => C.val) h
  · intro h
    apply Subtype.ext
    exact h

/-- The fibre coordinate relative to the fixed representative of the image. -/
noncomputable def tag (e : A ↪[language] M) : A ↪[language] A :=
  factorThrough (representative (copyOf e)) e
    (by rw [representative_range]; exact Set.Subset.rfl)

theorem representative_tag (e : A ↪[language] M) :
    (representative (copyOf e)).comp (tag e) = e :=
  factorThrough_comp _ _ _

variable [Finite A]

theorem copy_comp_self (e : A ↪[language] M) (t : A ↪[language] A) :
    copyOf (e.comp t) = copyOf e := by
  apply (copy_range_eq _ _).mpr
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨t a,rfl⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨b,hb⟩ := Finite.surjective_of_injective t.injective a
    exact ⟨b,by change e (t b) = e a; rw [hb]⟩

/-- Every fibre coordinate occurs exactly once for each copy. -/
theorem tag_rep_comp (C : Copy A M) (t : A ↪[language] A) :
    tag ((representative C).comp t) = t := by
  have h := representative_tag ((representative C).comp t)
  rw [copy_comp_self,representative_copy] at h
  exact comp_cancel_left (representative C) h

theorem copy_rep_comp (C : Copy A M) (t : A ↪[language] A) :
    copyOf ((representative C).comp t) = C :=
  (copy_comp_self _ _).trans (representative_copy C)

theorem finite_self_embeddings : Finite (A ↪[language] A) :=
  Finite.of_injective (fun e : A ↪[language] A => (fun a : A => e a))
    (by intro e g h; exact FirstOrder.Language.Embedding.ext (congrFun h))

/-- Every realized copy class occurs inside every reduct self-copy. -/
def CopyUnavoidable (γ : Copy A M → Nat) : Prop :=
  ∀ (f : M ↪[language] M) (C : Copy A M),
    ∃ g : A ↪[language] M, γ (copyOf (f.comp g)) = γ C

def CopyCanonicalOn {D : Type*} (γ : Copy A M → Nat) (χ : Copy A M → D)
    (f : M ↪[language] M) : Prop :=
  ∀ e g : A ↪[language] M, γ (copyOf (f.comp e)) = γ (copyOf (f.comp g)) →
    χ (copyOf (f.comp e)) = χ (copyOf (f.comp g))

/-- A universal copy partition would induce an unavoidable embedding partition
which also canonizes every finite embedding colouring. The proof uses a
tuple of colours indexed by the finite set of self-embeddings of A. -/
theorem transfer_obstruction (γ : Copy A M → Nat) (hγ : CopyUnavoidable γ)
    (hbad : ∀ Γ : (A ↪[language] M) → Nat, Unavoidable Γ →
      ∃ χ : (A ↪[language] M) → Bool × Bool,
        ∀ f : M ↪[language] M, ¬ CanonicalOn Γ χ f) :
    ∃ r : Nat, ∃ χ : Copy A M → Fin r,
      ∀ f : M ↪[language] M, ¬ CopyCanonicalOn γ χ f := by
  classical
  letI : Finite (A ↪[language] A) := finite_self_embeddings
  letI : Fintype (A ↪[language] A) := Fintype.ofFinite _
  obtain ⟨encode,hencode⟩ := exists_injective_nat (Nat × (A ↪[language] A))
  let Γ (e : A ↪[language] M) : Nat := encode (γ (copyOf e),tag e)
  have hΓ : Unavoidable Γ := by
    intro f e
    obtain ⟨g,hg⟩ := hγ f (copyOf e)
    let C := copyOf (f.comp g)
    let v := (representative C).comp (tag e)
    have hvC : copyOf v = C := copy_rep_comp C (tag e)
    have hvt : tag v = tag e := tag_rep_comp C (tag e)
    have hsub : Set.range v ⊆ Set.range f := by
      have hr : Set.range v = Set.range (f.comp g) :=
        (copy_range_eq v (f.comp g)).mp hvC
      rw [hr]
      rintro _ ⟨a,rfl⟩
      exact ⟨g a,rfl⟩
    let u := factorThrough f v hsub
    refine ⟨u,?_⟩
    have hu : f.comp u = v := factorThrough_comp f v hsub
    change encode (γ (copyOf (f.comp u)),tag (f.comp u)) =
      encode (γ (copyOf e),tag e)
    rw [hu,hvC,hvt]
    exact congrArg (fun k => encode (k,tag e)) hg
  obtain ⟨χ,hχ⟩ := hbad Γ hΓ
  let palette (C : Copy A M) : (A ↪[language] A) → Bool × Bool :=
    fun t => χ ((representative C).comp t)
  let enc := Fintype.equivFin ((A ↪[language] A) → Bool × Bool)
  refine ⟨_,fun C => enc (palette C),?_⟩
  intro f hf
  apply hχ f
  intro e g h
  have hh := hencode h
  have hcol : γ (copyOf (f.comp e)) = γ (copyOf (f.comp g)) :=
    congrArg Prod.fst hh
  have htag : tag (f.comp e) = tag (f.comp g) := congrArg Prod.snd hh
  have hp := enc.injective (hf e g hcol)
  have ht := congrFun hp (tag (f.comp e))
  change χ ((representative (copyOf (f.comp e))).comp (tag (f.comp e))) =
    χ ((representative (copyOf (f.comp g))).comp (tag (f.comp e))) at ht
  rw [representative_tag,htag,representative_tag] at ht
  exact ht

end Transfer

/-- No unavoidable partition of literal copies of a finite nonchain in the
concrete binary pseudotree canonizes every finite colouring. -/
theorem ternary_no_universal_copy_partition {A : Type*} [Finite A]
    [SemilatticeInf A] [language.Structure A] [MeetsInterpreted A]
    (hA : Nonempty (A ↪[language] TernaryModel)) {x y : A} (hxy : ¬x ≤ y) (hyx : ¬y ≤ x)
    (γ : Copy A TernaryModel → Nat) (hγ : CopyUnavoidable γ) :
    ∃ r : Nat, ∃ χ : Copy A TernaryModel → Fin r,
      ∀ f : TernaryModel ↪[language] TernaryModel, ¬ CopyCanonicalOn γ χ f :=
  transfer_obstruction γ hγ (fun Γ hΓ => ternary_no_universal_partition hA hxy hyx Γ hΓ)

end AllThoseBigRamsey.Pseudotree.NoInfiniteCanonical
