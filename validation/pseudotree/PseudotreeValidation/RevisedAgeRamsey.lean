import PseudotreeValidation.RevisedNativeRamsey
import Mathlib.Topology.Compactness.Compact

/-! The finite age Ramsey corollary of native IRT. Compactness of the
product of finite discrete colour spaces gives finitely many candidate
B-copies. Their finite meet hull is the desired finite substructure.
This avoids a separate countable exhaustion or Koenig-tree development. -/
namespace AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion
open FirstOrder
open scoped FirstOrder
open RevisedConvention (RevisedSparseModel)

local instance colourTopology (r : Nat) : TopologicalSpace (Fin (r+1)) := ⊥
local instance colourDiscrete (r : Nat) : DiscreteTopology (Fin (r+1)) := ⟨rfl⟩

/-- An actual finite functional substructure containing any finite set. -/
theorem finite_superstructure (S : Set RevisedSparseModel) (hS : S.Finite) :
    ∃ C : expandedLanguage.Substructure RevisedSparseModel,
      (C : Set RevisedSparseModel).Finite ∧ S ⊆ C := by
  let H := Set.image2 (· ⊓ ·) S S
  have hH : ∀ x ∈ H, ∀ y ∈ H, x ⊓ y ∈ H :=
    image2_inf_closed RevisedConvention.RevisedSparseModel.predecessors_comparable S
  let C : expandedLanguage.Substructure RevisedSparseModel := {
    carrier := H
    fun_mem := by
      intro n f x hx
      cases f
      exact hH (x 0) (hx 0) (x 1) (hx 1) }
  refine ⟨C,hS.image2 (· ⊓ ·) hS,?_⟩
  intro x hx
  exact ⟨x,hx,x,hx,inf_idem x⟩

/-- The finite set of embeddings between finite native structures is finite
even when the expansion language has infinitely many relation symbols. -/
private theorem finiteEmbeddings (A B : Type) [expandedLanguage.Structure A]
    [expandedLanguage.Structure B] [Finite A] [Finite B] :
    Finite (A ↪[expandedLanguage] B) :=
  Finite.of_injective (fun e : A ↪[expandedLanguage] B => (fun a : A => e a))
    (by intro e g h; exact FirstOrder.Language.Embedding.ext (congrFun h))

/-- The age Ramsey theorem for finite actual substructures of the revised
expansion, including the empty A or B. Every abstract member of its age is
isomorphic to such a substructure. -/
theorem finite_age_ramsey (A B : expandedLanguage.Substructure RevisedSparseModel)
    [Finite A] [Finite B] (r : Nat) :
    ∃ C : expandedLanguage.Substructure RevisedSparseModel,
      ∃ _ : Finite C,
      ∀ colour : (A ↪[expandedLanguage] C) → Fin (r+1),
        ∃ f : B ↪[expandedLanguage] C, ∃ c : Fin (r+1),
          ∀ e : A ↪[expandedLanguage] B, colour (f.comp e) = c := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Finite (A ↪[expandedLanguage] B) := finiteEmbeddings A B
  let Colours := (A ↪[expandedLanguage] RevisedSparseModel) → Fin (r+1)
  let U (f : B ↪[expandedLanguage] RevisedSparseModel) : Set Colours :=
    {χ | ∃ c : Fin (r+1), ∀ e : A ↪[expandedLanguage] B, χ (f.comp e) = c}
  have hU (f : B ↪[expandedLanguage] RevisedSparseModel) : IsOpen (U f) := by
    have hEq : U f = ⋃ c : Fin (r+1),
        ⋂ e : A ↪[expandedLanguage] B, {χ : Colours | χ (f.comp e) = c} := by
      ext χ
      simp [U]
    rw [hEq]
    apply isOpen_iUnion
    intro c
    apply isOpen_iInter_of_finite
    intro e
    change IsOpen ((fun χ : Colours => χ (f.comp e)) ⁻¹' ({c} : Set (Fin (r+1))))
    exact (isOpen_discrete _).preimage (continuous_apply (f.comp e))
  have hcover : (Set.univ : Set Colours) ⊆ ⋃ f, U f := by
    intro χ _
    obtain ⟨g,c,hg⟩ := native_IRT A χ
    refine Set.mem_iUnion.mpr ⟨g.comp B.subtype,c,?_⟩
    intro e
    exact hg (B.subtype.comp e)
  obtain ⟨F,hF⟩ := (isCompact_univ : IsCompact (Set.univ : Set Colours)).elim_finite_subcover U hU hcover
  let S : Set RevisedSparseModel := ⋃ f ∈ (F : Set (B ↪[expandedLanguage] RevisedSparseModel)), Set.range f
  have hS : S.Finite := F.finite_toSet.biUnion (fun f _ => Set.finite_range f)
  obtain ⟨C,hC,hSC⟩ := finite_superstructure S hS
  letI : Finite C := hC.to_subtype
  refine ⟨C,inferInstance,?_⟩
  intro colour
  let χ : Colours := fun e =>
    if h : ∀ a, e a ∈ C then colour (FirstOrder.Language.Embedding.codRestrict C e h) else 0
  have hc := hF (Set.mem_univ χ)
  obtain ⟨f,hf⟩ := Set.mem_iUnion.mp hc
  obtain ⟨hfF,hmono⟩ := Set.mem_iUnion.mp hf
  have hfC (b : B) : f b ∈ C := by
    apply hSC
    exact Set.mem_iUnion.mpr ⟨f,Set.mem_iUnion.mpr ⟨hfF,Set.mem_range_self b⟩⟩
  let g := FirstOrder.Language.Embedding.codRestrict C f hfC
  obtain ⟨c,hc⟩ := hmono
  refine ⟨g,c,?_⟩
  intro e
  have he : ∀ a, (f.comp e) a ∈ C := fun a => hfC (e a)
  have h := hc e
  change (if h : ∀ a, (f.comp e) a ∈ C
    then colour (FirstOrder.Language.Embedding.codRestrict C (f.comp e) h) else 0) = c at h
  rw [dif_pos he] at h
  have hEq : FirstOrder.Language.Embedding.codRestrict C (f.comp e) he = g.comp e := by
    apply FirstOrder.Language.Embedding.ext
    intro a
    rfl
  simpa only [hEq] using h

end AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion
