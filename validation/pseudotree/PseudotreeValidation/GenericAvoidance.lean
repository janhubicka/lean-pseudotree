import PseudotreeValidation.CopyPartitionTransfer
import Mathlib.Order.WithBot

/-! Finite-set avoidance in any countable homogeneous meet-tree without
endpoints. Adjoin a single formal bottom, embed the enlarged tree into
the original one, and prescribe the image of the formal bottom. This
works for arbitrary branching, so no binary-specific extension axiom
or an assumed cone-isomorphism theorem is needed. -/
namespace AllThoseBigRamsey.Pseudotree.NoInfiniteCanonical
open FirstOrder
open scoped FirstOrder

section Avoidance
variable {M : Type*} [SemilatticeInf M] [Nonempty M]
    [language.Structure M] [MeetsInterpreted M]

/-- Every finite set has a strict common lower bound. -/
theorem finite_strict_lower [NoMinOrder M] (F : Finset M) :
    ∃ p : M, ∀ x ∈ F, p < x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨Classical.choice inferInstance,by simp⟩
  | @insert x F hx ih =>
    obtain ⟨p,hp⟩ := ih
    obtain ⟨q,hq⟩ := exists_lt (p ⊓ x)
    refine ⟨q,?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hq.trans_le inf_le_right
    · exact (hq.trans_le inf_le_left).trans (hp y hy)

/-- Choose a point not below any point of a finite forbidden set. -/
theorem finite_escape [NoMaxOrder M] (F : Finset M) :
    ∃ a : M, ∀ x ∈ F, ¬ a ≤ x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨Classical.choice inferInstance,by simp⟩
  | @insert x F hx ih =>
    obtain ⟨a,ha⟩ := ih
    by_cases hax : a ≤ x
    · obtain ⟨b,hb⟩ := exists_gt x
      refine ⟨b,?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact not_le_of_gt hb
      · exact fun h => ha y hy (hax.trans (hb.le.trans h))
    · refine ⟨a,?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hax
      · exact ha y hy

/-- Adjoining a bottom preserves comparability of common predecessors. -/
theorem withBot_tree
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    {x y z : WithBot M} (hx : x ≤ z) (hy : y ≤ z) : x ≤ y ∨ y ≤ x := by
  cases x with
  | bot => exact Or.inl bot_le
  | coe x =>
    cases y with
    | bot => exact Or.inr bot_le
    | coe y =>
      cases z with
      | bot =>
        have h : (x : WithBot M) ≤ ⊥ := hx
        exact False.elim (not_le_of_gt (WithBot.bot_lt_coe x) h)
      | coe z =>
        have hx' : x ≤ z := WithBot.coe_le_coe.mp hx
        have hy' : y ≤ z := WithBot.coe_le_coe.mp hy
        rcases htree hx' hy' with h | h
        · exact Or.inl (WithBot.coe_le_coe.mpr h)
        · exact Or.inr (WithBot.coe_le_coe.mpr h)

/-- Every finite substructure of the bottom-adjoined model embeds into M:
replace the bottom by a point strictly below its finitely many ordinary
points, and leave all ordinary points unchanged. -/
theorem finite_withBot_embeds [NoMinOrder M]
    (B : language.Substructure (WithBot M)) [Finite B] :
    Nonempty (B ↪[language] M) := by
  classical
  let F : Set M := {x | (x : WithBot M) ∈ B}
  have hB : (B : Set (WithBot M)).Finite := by
    change Finite B
    infer_instance
  have hF : F.Finite := hB.preimage WithBot.coe_injective.injOn
  obtain ⟨p,hp⟩ := finite_strict_lower hF.toFinset
  have hlt (x : M) (hx : (x : WithBot M) ∈ B) : p < x :=
    hp x (by simpa [F] using hx)
  let j (x : B) : M := WithBot.unbotD p x.val
  refine ⟨embeddingOfInfMap j ?_ ?_⟩
  · rintro ⟨x,hx⟩ ⟨y,hy⟩ he
    apply Subtype.ext
    change WithBot.unbotD p x = WithBot.unbotD p y at he
    cases x with
    | bot =>
      cases y with
      | bot => rfl
      | coe y =>
        have h : p = y := he
        exact False.elim ((hlt y hy).ne h)
    | coe x =>
      cases y with
      | bot =>
        have h : x = p := he
        exact False.elim ((hlt x hx).ne h.symm)
      | coe y =>
        have h : x = y := he
        exact congrArg (fun t : M => (t : WithBot M)) h
  · rintro ⟨x,hx⟩ ⟨y,hy⟩
    change WithBot.unbotD p (x ⊓ y) =
      WithBot.unbotD p x ⊓ WithBot.unbotD p y
    cases x with
    | bot =>
      cases y with
      | bot => simp [WithBot.unbotD_bot]
      | coe y =>
        change p = p ⊓ y
        exact (inf_eq_left.mpr (hlt y hy).le).symm
    | coe x =>
      cases y with
      | bot =>
        change p = x ⊓ p
        exact (inf_eq_right.mpr (hlt x hx).le).symm
      | coe y => rfl

/-- The finite embedding property plus ultrahomogeneity gives the actual
one-point extension pair for the countable bottom-adjoined structure. -/
theorem withBot_extensionPair [NoMinOrder M]
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hhom : language.IsUltrahomogeneous M) :
    language.IsExtensionPair (WithBot M) M := by
  apply FirstOrder.Language.isExtensionPair_iff_exists_embedding_closure_singleton_sup.mpr
  intro S hS f m
  let B : language.Substructure (WithBot M) :=
    FirstOrder.Language.Substructure.closure language {m} ⊔ S
  have hBfg : B.FG := (FirstOrder.Language.Substructure.fg_closure_singleton m).sup hS
  obtain ⟨X,hX,hXB⟩ := FirstOrder.Language.Substructure.fg_def.mp hBfg
  have hf := finite_meet_closure (withBot_tree htree) hX
  rw [hXB] at hf
  letI : Finite B := hf.to_subtype
  letI : Nonempty (B ↪[language] M) := finite_withBot_embeds B
  obtain ⟨g,hg⟩ := hhom.extend_embedding
    ((FirstOrder.Language.Substructure.fg_iff_structure_fg S).mp hS)
    f (FirstOrder.Language.Substructure.inclusion (show S ≤ B from le_sup_right))
  exact ⟨g,hg⟩

/-- Embed the enlarged structure with a prescribed image of its bottom. -/
theorem embed_withBot_at [NoMinOrder M] [Countable M]
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hhom : language.IsUltrahomogeneous M) (a : M) :
    ∃ g : WithBot M ↪[language] M, g ⊥ = a := by
  classical
  let S : language.Substructure (WithBot M) :=
    substructureOfInfClosed {⊥} (by intro x hx y hy; simp at hx hy; subst x; subst y; simp)
  have hS : S.FG := by
    apply FirstOrder.Language.Substructure.fg_def.mpr
    refine ⟨{⊥},Set.finite_singleton _,?_⟩
    apply le_antisymm
    · exact FirstOrder.Language.Substructure.closure_le.mpr (fun x hx => hx)
    · intro x hx
      exact FirstOrder.Language.Substructure.subset_closure (show x ∈ ({⊥} : Set (WithBot M)) from hx)
  let e : S ↪[language] M := by
    apply embeddingOfInfMap (fun _ : S => a)
    · intro x y _
      apply Subtype.ext
      have hx : x.val = (⊥ : WithBot M) := x.property
      have hy : y.val = (⊥ : WithBot M) := y.property
      exact hx.trans hy.symm
    · intro x y
      exact (inf_idem a).symm
  let F : language.FGEquiv (WithBot M) M :=
    ⟨⟨S,e.toHom.range,e.equivRange⟩,hS⟩
  obtain ⟨g,hg⟩ := FirstOrder.Language.embedding_from_cg
    FirstOrder.Language.Structure.cg_of_countable F (withBot_extensionPair htree hhom)
  refine ⟨g,?_⟩
  obtain ⟨hle,he⟩ := (FirstOrder.Language.PartialEquiv.le_def F.val g.toPartialEquiv).mp hg
  have hbot : (⊥ : WithBot M) ∈ S := by
    change (⊥ : WithBot M) ∈ ({⊥} : Set (WithBot M))
    simp
  have hh := congrArg (fun e' : S ↪[language] M => e' ⟨⊥,hbot⟩) he
  change g ⊥ = a at hh
  exact hh

/-- Every finite set is avoided by a self-embedding, for arbitrary branching. -/
theorem finite_set_avoidance [NoMinOrder M] [NoMaxOrder M] [Countable M]
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hhom : language.IsUltrahomogeneous M) (F : Set M) (hF : F.Finite) :
    ∃ g : M ↪[language] M, ∀ x, g x ∉ F := by
  obtain ⟨a,ha⟩ := finite_escape hF.toFinset
  obtain ⟨h,hh⟩ := embed_withBot_at htree hhom a
  let inclusion : M ↪[language] WithBot M :=
    embeddingOfInfMap (fun x => (x : WithBot M)) WithBot.coe_injective WithBot.coe_inf
  refine ⟨h.comp inclusion,fun x hx => ?_⟩
  have hax : a < h (x : WithBot M) := by
    rw [← hh]
    exact (embedding_lt_iff h _ _).mpr (WithBot.bot_lt_coe x)
  change h (x : WithBot M) ∈ F at hx
  have hmem : h (x : WithBot M) ∈ hF.toFinset := hF.mem_toFinset.mpr hx
  exact ha _ hmem hax.le

theorem generic_rank_avoidance [NoMinOrder M] [NoMaxOrder M] [Countable M]
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hhom : language.IsUltrahomogeneous M)
    (rank : M → Nat) (hrank : Function.Injective rank)
    (f : M ↪[language] M) (k : Nat) :
    ∃ g : M ↪[language] M, ∀ a, k ≤ rank (f (g a)) := by
  let F : Set M := {a | rank (f a) < k}
  have hF : F.Finite := (Set.finite_lt_nat k).preimage (hrank.comp f.injective).injOn
  obtain ⟨g,hg⟩ := finite_set_avoidance htree hhom F hF
  exact ⟨g,fun a => Nat.le_of_not_gt (hg a)⟩

end Avoidance

/-- Generic embedding-level endpoint, with no finite-avoidance assumption. -/
theorem no_universal_partition_of_countable
    {M A : Type*} [SemilatticeInf M] [Nonempty M] [Countable M]
    [DenselyOrdered M] [NoMinOrder M] [NoMaxOrder M]
    [language.Structure M] [MeetsInterpreted M]
    [SemilatticeInf A] [language.Structure A] [MeetsInterpreted A]
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbranch : ∀ {x a : M}, x < a → ∃ z, x < z ∧ z ⊓ a = x)
    (hhom : language.IsUltrahomogeneous M)
    (hA : Nonempty (A ↪[language] M)) {x y : A} (hxy : ¬x ≤ y) (hyx : ¬y ≤ x)
    (γ : (A ↪[language] M) → Nat) (hγ : Unavoidable γ) :
    ∃ χ : (A ↪[language] M) → Bool × Bool,
      ∀ f : M ↪[language] M, ¬ CanonicalOn γ χ f := by
  obtain ⟨rank,hrank⟩ := exists_injective_nat M
  exact no_universal_partition (GenericIncomparables.systemOfCountable htree)
    hbranch hhom hA hxy hyx rank (generic_rank_avoidance htree hhom rank hrank) γ hγ

/-- Generic copy-level endpoint, including nonrigid finite structures. -/
theorem no_universal_copy_partition_of_countable
    {M A : Type*} [SemilatticeInf M] [Nonempty M] [Countable M]
    [DenselyOrdered M] [NoMinOrder M] [NoMaxOrder M]
    [language.Structure M] [MeetsInterpreted M]
    [Finite A] [SemilatticeInf A] [language.Structure A] [MeetsInterpreted A]
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbranch : ∀ {x a : M}, x < a → ∃ z, x < z ∧ z ⊓ a = x)
    (hhom : language.IsUltrahomogeneous M)
    (hA : Nonempty (A ↪[language] M)) {x y : A} (hxy : ¬x ≤ y) (hyx : ¬y ≤ x)
    (γ : Copy A M → Nat) (hγ : CopyUnavoidable γ) :
    ∃ r : Nat, ∃ χ : Copy A M → Fin r,
      ∀ f : M ↪[language] M, ¬ CopyCanonicalOn γ χ f :=
  transfer_obstruction γ hγ
    (fun Γ hΓ => no_universal_partition_of_countable htree hbranch hhom hA hxy hyx Γ hΓ)

end AllThoseBigRamsey.Pseudotree.NoInfiniteCanonical
