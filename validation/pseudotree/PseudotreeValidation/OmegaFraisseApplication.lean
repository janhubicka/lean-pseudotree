import PseudotreeValidation.GenericAvoidance
import PseudotreeValidation.FraisseModel

/-! Application to the manuscript's defining Fraisse age, rather than
an extra hypothesis about a chosen countably branching model.

The manuscript defines Psi_omega as the Fraisse limit of all finite
meet-trees. Here the age is specified independently and the required
geometric properties are derived from that age. We do not assert a new
construction of the Fraisse limit. The ambient meet and order are the
interpreted operations of the manuscript. -/
namespace AllThoseBigRamsey.Pseudotree
open FirstOrder
open scoped FirstOrder

/-- All finite meet-trees, without a branching restriction. -/
def finiteMeetTreeClass : Set (CategoryTheory.Bundled.{u} language.Structure) :=
  {S | Finite S ∧ ∃ i : SemilatticeInf S,
    letI := i
    MeetsInterpreted S ∧
      (∀ {x y z : S}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)}

theorem finiteBinaryClass_subset_finiteMeetTreeClass :
    finiteBinaryClass.{u} ⊆ finiteMeetTreeClass.{u} := by
  intro S hS
  obtain ⟨hf,i,hi,ht,_⟩ := hS
  exact ⟨hf,i,hi,ht⟩

namespace OmegaFraisse

variable {M : Type} [SemilatticeInf M] [language.Structure M]
    [MeetsInterpreted M] [Countable M]

/-- Every finite chain occurs in the intrinsic age. -/
theorem chain_mem_class (n : Nat) :
    (⟨Fin n, inferInstance⟩ : CategoryTheory.Bundled language.Structure) ∈ finiteMeetTreeClass := by
  refine ⟨inferInstance,inferInstance,inferInstance,?_⟩
  intro x y z hx hy
  exact le_total x y

/-- The finite fork is in the same age. -/
theorem fork_mem_class :
    (⟨Incomparables.Fork, inferInstance⟩ : CategoryTheory.Bundled language.Structure) ∈ finiteMeetTreeClass := by
  refine ⟨inferInstance,inferInstance,inferInstance,?_⟩
  intro x y z hx hy
  change x = Incomparables.Fork.root ∨ x = z at hx
  change y = Incomparables.Fork.root ∨ y = z at hy
  change (x = Incomparables.Fork.root ∨ x = y) ∨
    (y = Incomparables.Fork.root ∨ y = x)
  rcases hx with hx | hx
  · exact Or.inl (Or.inl hx)
  · rcases hy with hy | hy
    · exact Or.inr (Or.inl hy)
    · exact Or.inl (Or.inr (hx.trans hy.symm))

theorem chain_embeds (hM : language.IsFraisseLimit finiteMeetTreeClass M)
    (n : Nat) : Nonempty (Fin n ↪[language] M) := by
  have h := chain_mem_class n
  rw [← hM.age] at h
  exact h.2

theorem fork_embeds (hM : language.IsFraisseLimit finiteMeetTreeClass M) :
    Nonempty (Incomparables.Fork ↪[language] M) := by
  have h := fork_mem_class
  rw [← hM.age] at h
  exact h.2

theorem nonempty_model (hM : language.IsFraisseLimit finiteMeetTreeClass M) : Nonempty M := by
  obtain ⟨e⟩ := chain_embeds hM 1
  exact ⟨e 0⟩

/-- Common predecessors are comparable: apply age membership to the
finitely generated substructure on three prescribed ambient points. -/
theorem predecessors (hM : language.IsFraisseLimit finiteMeetTreeClass M)
    {x y z : M} (hx : x ≤ z) (hy : y ≤ z) : x ≤ y ∨ y ≤ x := by
  let B := FirstOrder.Language.Substructure.closure language ({x,y,z} : Set M)
  have hB : B.FG := FirstOrder.Language.Substructure.fg_closure (by simp)
  have ha := FirstOrder.Language.age.fg_substructure hB
  rw [hM.age] at ha
  obtain ⟨_,i,hi,ht⟩ := ha
  letI : SemilatticeInf B := i
  letI : MeetsInterpreted B := hi
  let p : B := ⟨x,FirstOrder.Language.Substructure.subset_closure (by simp)⟩
  let q : B := ⟨y,FirstOrder.Language.Substructure.subset_closure (by simp)⟩
  let r : B := ⟨z,FirstOrder.Language.Substructure.subset_closure (by simp)⟩
  have hp : @LE.le B i.toLE p r :=
    (@embedding_le_iff B M i _ _ _ hi _ B.subtype p r).mp hx
  have hq : @LE.le B i.toLE q r :=
    (@embedding_le_iff B M i _ _ _ hi _ B.subtype q r).mp hy
  exact (ht hp hq).imp
    (@embedding_le_iff B M i _ _ _ hi _ B.subtype p q).mpr
    (@embedding_le_iff B M i _ _ _ hi _ B.subtype q p).mpr

section SmallEmbeddings
variable {N : Type*} [SemilatticeInf N] [language.Structure N] [MeetsInterpreted N]

/-- Singleton and two-element chain embeddings, for any interpreted
meet-semilattice. -/
def one (a : N) : Fin 1 ↪[language] N :=
  embeddingOfInfMap (fun _ => a) (fun _ _ _ => Subsingleton.elim _ _)
    (fun _ _ => (inf_idem a).symm)

def pairFun (a b : N) (i : Fin 2) : N := if i = 0 then a else b

theorem pairFun_strict {a b : N} (hab : a < b) : StrictMono (pairFun a b) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [pairFun]

def pair {a b : N} (hab : a < b) : Fin 2 ↪[language] N :=
  embeddingOfInfMap (pairFun a b) (pairFun_strict hab).injective
    (by
      intro i j
      rcases le_total i j with h | h
      · rw [inf_eq_left.mpr h,inf_eq_left.mpr ((pairFun_strict hab).monotone h)]
      · rw [inf_eq_right.mpr h,inf_eq_right.mpr ((pairFun_strict hab).monotone h)])

@[simp] theorem pair_zero {a b : N} (h : a < b) : pair h 0 = a := rfl
@[simp] theorem pair_one {a b : N} (h : a < b) : pair h 1 = b := rfl

end SmallEmbeddings

theorem model_noMinOrder (hM : language.IsFraisseLimit finiteMeetTreeClass M) :
    NoMinOrder M := by
  constructor
  intro a
  obtain ⟨e,he⟩ := hM.ultrahomogeneous.extend_embedding
    (FirstOrder.Language.Structure.FG.of_finite :
      FirstOrder.Language.Structure.FG language (Fin 1))
    (one a) (one (1 : Fin 2)) (h := chain_embeds hM 2)
  have h := congrArg (fun f : Fin 1 ↪[language] M => f 0) he
  change a = e 1 at h
  refine ⟨e 0,?_⟩
  rw [h]
  exact (embedding_lt_iff e 0 1).mpr (by decide)

theorem model_noMaxOrder (hM : language.IsFraisseLimit finiteMeetTreeClass M) :
    NoMaxOrder M := by
  constructor
  intro a
  obtain ⟨e,he⟩ := hM.ultrahomogeneous.extend_embedding
    (FirstOrder.Language.Structure.FG.of_finite :
      FirstOrder.Language.Structure.FG language (Fin 1))
    (one a) (one (0 : Fin 2)) (h := chain_embeds hM 2)
  have h := congrArg (fun f : Fin 1 ↪[language] M => f 0) he
  change a = e 0 at h
  refine ⟨e 1,?_⟩
  rw [h]
  exact (embedding_lt_iff e 0 1).mpr (by decide)

theorem model_dense (hM : language.IsFraisseLimit finiteMeetTreeClass M) :
    DenselyOrdered M := by
  constructor
  intro a b hab
  let g : Fin 2 ↪[language] Fin 3 := pair (show (0 : Fin 3) < 2 by decide)
  obtain ⟨e,he⟩ := hM.ultrahomogeneous.extend_embedding
    (FirstOrder.Language.Structure.FG.of_finite :
      FirstOrder.Language.Structure.FG language (Fin 2))
    (pair hab) g (h := chain_embeds hM 3)
  have h₀ := congrArg (fun f : Fin 2 ↪[language] M => f 0) he
  have h₁ := congrArg (fun f : Fin 2 ↪[language] M => f 1) he
  change a = e 0 at h₀
  change b = e 2 at h₁
  refine ⟨e 1,?_⟩
  rw [h₀,h₁]
  exact ⟨(embedding_lt_iff e 0 1).mpr (by decide),
    (embedding_lt_iff e 1 2).mpr (by decide)⟩

theorem opposite_branch (hM : language.IsFraisseLimit finiteMeetTreeClass M)
    {a b : M} (hab : a < b) : ∃ c, a < c ∧ c ⊓ b = a := by
  have hl : Incomparables.Fork.root < Incomparables.Fork.left :=
    lt_of_le_of_ne (show Incomparables.Fork.root ≤ Incomparables.Fork.left from Or.inl rfl)
      (by decide)
  have hr : Incomparables.Fork.root < Incomparables.Fork.right :=
    lt_of_le_of_ne (show Incomparables.Fork.root ≤ Incomparables.Fork.right from Or.inl rfl)
      (by decide)
  let g : Fin 2 ↪[language] Incomparables.Fork := pair hl
  obtain ⟨e,he⟩ := hM.ultrahomogeneous.extend_embedding
    (FirstOrder.Language.Structure.FG.of_finite :
      FirstOrder.Language.Structure.FG language (Fin 2))
    (pair hab) g (h := fork_embeds hM)
  have h₀ := congrArg (fun f : Fin 2 ↪[language] M => f 0) he
  have h₁ := congrArg (fun f : Fin 2 ↪[language] M => f 1) he
  change a = e Incomparables.Fork.root at h₀
  change b = e Incomparables.Fork.left at h₁
  refine ⟨e Incomparables.Fork.right,?_⟩
  rw [h₀,h₁]
  constructor
  · exact (embedding_lt_iff e _ _).mpr hr
  · rw [← embedding_map_inf]
    rfl

/-- The manuscript's infinite degree theorem at the actual defining
Fraisse-limit interface of Psi_omega. No geometric hypothesis besides the
ambient interpretation of the symbols is required from the caller. -/
theorem no_finite_bound
    (hM : language.IsFraisseLimit finiteMeetTreeClass M)
    {A : Type*} [Finite A] [SemilatticeInf A] [language.Structure A] [MeetsInterpreted A]
    (hA : Nonempty (A ↪[language] M)) {x y : A} (hxy : ¬x ≤ y) (hyx : ¬y ≤ x) (d : Nat) :
    ¬GenericIncomparables.FunctionalBigRamseyBound A M d := by
  letI : Nonempty M := nonempty_model hM
  letI : NoMaxOrder M := model_noMaxOrder hM
  letI : DenselyOrdered M := model_dense hM
  exact GenericIncomparables.no_finite_bound_of_countable
    (predecessors hM) (opposite_branch hM) hM.ultrahomogeneous hA hxy hyx d

/-- The stronger obstruction to simultaneous canonization, for the same
defining Fraisse-limit interface and actual literal copies. -/
theorem no_universal_copy_partition
    (hM : language.IsFraisseLimit finiteMeetTreeClass M)
    {A : Type*} [Finite A] [SemilatticeInf A] [language.Structure A] [MeetsInterpreted A]
    (hA : Nonempty (A ↪[language] M)) {x y : A} (hxy : ¬x ≤ y) (hyx : ¬y ≤ x)
    (γ : NoInfiniteCanonical.Copy A M → Nat) (hγ : NoInfiniteCanonical.CopyUnavoidable γ) :
    ∃ r : Nat, ∃ χ : NoInfiniteCanonical.Copy A M → Fin r,
      ∀ f : M ↪[language] M, ¬ NoInfiniteCanonical.CopyCanonicalOn γ χ f := by
  letI : Nonempty M := nonempty_model hM
  letI : NoMinOrder M := model_noMinOrder hM
  letI : NoMaxOrder M := model_noMaxOrder hM
  letI : DenselyOrdered M := model_dense hM
  exact NoInfiniteCanonical.no_universal_copy_partition_of_countable
    (predecessors hM) (opposite_branch hM) hM.ultrahomogeneous hA hxy hyx γ hγ

end OmegaFraisse
end AllThoseBigRamsey.Pseudotree
