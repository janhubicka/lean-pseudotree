import PseudotreeValidation.AnchoredOscillation
import PseudotreeValidation.RayMapEmbedding

/-! The four-colour diagonal obstruction to universal canonization.
The abstract functional theorem separates the geometric anchored oscillation
from finite-set avoidance. The concrete ternary model discharges avoidance
by prefixing words, not by assuming a cone is isomorphic to the model. -/
namespace AllThoseBigRamsey.Pseudotree
namespace NoInfiniteCanonical

open FirstOrder Profiles FiniteOscillation
open scoped FirstOrder

/-- Binary digits, with an elementary interface for prescribing an arbitrary
finite initial block and an arbitrarily large value. -/
def binaryBit (n : Nat) : Nat → Bool
  | 0 => decide (n % 2 = 1)
  | k+1 => binaryBit (n / 2) k

theorem binaryBit_double (n : Nat) (b : Bool) :
    binaryBit (2*n + (if b then 1 else 0)) 0 = b ∧
    ∀ k, binaryBit (2*n + (if b then 1 else 0)) (k+1) = binaryBit n k := by
  cases b with
  | false =>
    have hd : (2*n + 0)/2 = n := by omega
    have hm : (2*n + 0)%2 ≠ 1 := by omega
    constructor
    · simpa [binaryBit,hm]
    · intro k
      simpa only [binaryBit, Bool.false_eq_true, if_false, hd]
  | true =>
    have hd : (2*n + 1)/2 = n := by omega
    have hm : (2*n + 1)%2 = 1 := by omega
    constructor
    · simpa [binaryBit,hm]
    · intro k
      simpa only [binaryBit, if_true, hd]

theorem prescribe_bits (m : Nat) (d : Nat → Bool) (N : Nat) :
    ∃ n ≥ N, ∀ k ≤ m, binaryBit n k ≠ d k := by
  induction m generalizing d N with
  | zero =>
    let b := !(d 0)
    let n := 2*N + (if b then 1 else 0)
    refine ⟨n,by dsimp [n]; split <;> omega,?_⟩
    intro k hk
    have he : k = 0 := by omega
    subst k
    change binaryBit (2*N + (if b then 1 else 0)) 0 ≠ d 0
    rw [(binaryBit_double N b).1]
    dsimp [b]
    cases d 0 <;> decide
  | succ m ih =>
    obtain ⟨q,hq,hbits⟩ := ih (fun k => d (k+1)) N
    let b := !(d 0)
    let n := 2*q + (if b then 1 else 0)
    refine ⟨n,by dsimp [n]; split <;> omega,?_⟩
    intro k hk
    cases k with
    | zero =>
      change binaryBit (2*q + (if b then 1 else 0)) 0 ≠ d 0
      rw [(binaryBit_double q b).1]
      dsimp [b]
      cases d 0 <;> decide
    | succ k =>
      change binaryBit (2*q + (if b then 1 else 0)) (k+1) ≠ d (k+1)
      rw [(binaryBit_double q b).2]
      exact hbits k (by omega)

section Functional

variable {M A : Type*} [SemilatticeInf M] [SemilatticeInf A]
    [language.Structure M] [MeetsInterpreted M]
    [language.Structure A] [MeetsInterpreted A]
    [Nonempty M] [DenselyOrdered M] [NoMaxOrder M]

/-- Every realized partition class survives every reduct self-copy. -/
def Unavoidable (γ : (A ↪[language] M) → Nat) : Prop :=
  ∀ (f : M ↪[language] M) (e : A ↪[language] M),
    ∃ g : A ↪[language] M, γ (f.comp g) = γ e

/-- The colouring is constant on every partition class in the self-copy. -/
def CanonicalOn (γ : (A ↪[language] M) → Nat)
    (χ : (A ↪[language] M) → Bool × Bool) (f : M ↪[language] M) : Prop :=
  ∀ e g : A ↪[language] M, γ (f.comp e) = γ (f.comp g) →
    χ (f.comp e) = χ (f.comp g)

/-- The exact anchored extension result for actual functional embeddings. -/
theorem anchored_embeddings
    (E : System M) (hbranch : ∀ {x a : M}, x < a → ∃ z, x < z ∧ z ⊓ a = x)
    (hhom : language.IsUltrahomogeneous M)
    (hA : Nonempty (A ↪[language] M)) {x y : A} (hxy : ¬x ≤ y) (hyx : ¬y ≤ x)
    (f : M ↪[language] M) (a : M) :
    ∃ k₀ : Nat, ∀ k ≥ k₀, ∃ e : A ↪[language] M,
      f (e (x ⊓ y)) = f a ∧
      osc (E.profile (f (e x))) (E.profile (f (e y))) = k := by
  obtain ⟨k₀,h⟩ := E.anchored_oscillations
    (GenericIncomparables.copy_rich E hbranch f) (Set.mem_range_self a)
  refine ⟨k₀,fun k hk => ?_⟩
  obtain ⟨b,c,⟨u,rfl⟩,⟨v,rfl⟩,hab,hac,hmeet,hosc⟩ := h k hk
  have huv : ¬u ≤ v := by
    intro huv
    have hle : f u ≤ f v := (embeddingOrderEmbedding f).monotone huv
    rw [inf_eq_left.mpr hle] at hmeet
    exact hab.ne hmeet.symm
  have hvu : ¬v ≤ u := by
    intro hvu
    have hle : f v ≤ f u := (embeddingOrderEmbedding f).monotone hvu
    rw [inf_eq_right.mpr hle] at hmeet
    exact hac.ne hmeet.symm
  obtain ⟨e,he₁,he₂⟩ := GenericIncomparables.extend_pair hhom hA hxy hyx huv hvu
  refine ⟨e,?_,by simpa only [he₁,he₂] using hosc⟩
  rw [embedding_map_inf e,he₁,he₂,embedding_map_inf f,hmeet]

/-- The four-colour witness is fixed before choosing the self-copy.
Avoidance says that any finite initial rank segment can be avoided in a
further self-copy; it does not assume any canonization conclusion. -/
theorem no_universal_partition
    (E : System M) (hbranch : ∀ {x a : M}, x < a → ∃ z, x < z ∧ z ⊓ a = x)
    (hhom : language.IsUltrahomogeneous M)
    (hA : Nonempty (A ↪[language] M)) {x y : A} (hxy : ¬x ≤ y) (hyx : ¬y ≤ x)
    (rank : M → Nat)
    (havoid : ∀ (f : M ↪[language] M) k, ∃ g : M ↪[language] M,
      ∀ a, k ≤ rank (f (g a)))
    (γ : (A ↪[language] M) → Nat) (hγ : Unavoidable γ) :
    ∃ χ : (A ↪[language] M) → Bool × Bool,
      ∀ f : M ↪[language] M, ¬ CanonicalOn γ χ f := by
  classical
  let o (e : A ↪[language] M) := osc (E.profile (e x)) (E.profile (e y))
  let χ (e : A ↪[language] M) : Bool × Bool :=
    (decide (rank (e (x ⊓ y)) < γ e),binaryBit (o e) (γ e))
  refine ⟨χ,?_⟩
  intro f hc
  have hbound (e : A ↪[language] M) :
      γ (f.comp e) ≤ rank (f (e (x ⊓ y))) := by
    let k := γ (f.comp e)
    obtain ⟨g,hg⟩ := havoid f k
    obtain ⟨v,hv⟩ := hγ (f.comp g) (f.comp e)
    have hcomp : (f.comp g).comp v = f.comp (g.comp v) := by
      apply FirstOrder.Language.Embedding.ext
      intro a
      rfl
    rw [hcomp] at hv
    have he := congrArg Prod.fst (hc (g.comp v) e hv)
    change decide (rank (f (g (v (x ⊓ y)))) < γ (f.comp (g.comp v))) =
      decide (rank (f (e (x ⊓ y))) < γ (f.comp e)) at he
    rw [hv] at he
    have hnot : ¬rank (f (g (v (x ⊓ y)))) < γ (f.comp e) :=
      Nat.not_lt.mpr (hg (v (x ⊓ y)))
    have hfalse : decide (rank (f (e (x ⊓ y))) < γ (f.comp e)) = false := by
      simpa [hnot] using he.symm
    exact Nat.le_of_not_gt (of_decide_eq_false hfalse)
  let a : M := Classical.choice (inferInstance : Nonempty M)
  let m := rank (f a)
  let d (j : Nat) : Bool :=
    if h : ∃ e : A ↪[language] M, γ (f.comp e) = j
    then (χ (f.comp h.choose)).2 else false
  have hd (e : A ↪[language] M) : d (γ (f.comp e)) = (χ (f.comp e)).2 := by
    have h : ∃ v : A ↪[language] M, γ (f.comp v) = γ (f.comp e) := ⟨e,rfl⟩
    simp only [d,dif_pos h]
    exact congrArg Prod.snd (hc h.choose e h.choose_spec)
  obtain ⟨k₀,hk₀⟩ := anchored_embeddings E hbranch hhom hA hxy hyx f a
  obtain ⟨n,hn,hbits⟩ := prescribe_bits m d k₀
  obtain ⟨e,hea,heo⟩ := hk₀ n hn
  have hle : γ (f.comp e) ≤ m := by
    have h := hbound e
    rw [hea] at h
    exact h
  have hbit := hd e
  change d (γ (f.comp e)) = binaryBit (o (f.comp e)) (γ (f.comp e)) at hbit
  have ho : o (f.comp e) = n := heo
  rw [ho] at hbit
  exact hbits (γ (f.comp e)) hle hbit.symm

end Functional

/-- Prefixing every literal word by L zeroes is a ray-preserving strong map. -/
def prefixShift (L : Nat) : RayEmbeddings.RayStrongMap where
  map := fun s => List.replicate L 0 ++ s
  level := fun n => L+n
  level_strict := by intro i j hij; omega
  length_map := by intro s; simp
  step := by
    intro s a
    exact ⟨[],by simp [List.append_assoc],fun _ => RayEmbeddings.binary_nil⟩

theorem prefixShift_length (L : Nat) (x : TernaryModel) :
    (fromBlocks (RayMapModel.embedding (prefixShift L) x)).length =
      L + (fromBlocks x).length := by
  have h : RayMapModel.embedding (prefixShift L) x =
      toBlocks (RayMapModel.act (prefixShift L) (fromBlocks x)) := by
    rw [← toBlocks_fromBlocks x,RayMapModel.embedding_apply_word,fromBlocks_toBlocks]
  rw [h,fromBlocks_toBlocks,RayMapModel.act_length]
  rfl

/-- Any finite set of forbidden preimages is avoided by a sufficiently long
common prefix. Hence rank avoidance holds in every actual binary self-copy. -/
theorem ternary_rank_avoidance (rank : TernaryModel → Nat)
    (hrank : Function.Injective rank)
    (f : TernaryModel ↪[language] TernaryModel) (k : Nat) :
    ∃ g : TernaryModel ↪[language] TernaryModel, ∀ a, k ≤ rank (f (g a)) := by
  classical
  let F : Set TernaryModel := {a | rank (f a) < k}
  have hF : F.Finite :=
    (Set.finite_lt_nat k).preimage (hrank.comp f.injective).injOn
  let L := hF.toFinset.sup (fun a => (fromBlocks a).length) + 1
  let g := RayMapModel.embedding (prefixShift L)
  refine ⟨g,fun a => ?_⟩
  by_contra h
  have ha : g a ∈ F := Nat.lt_of_not_ge h
  have hb : (fromBlocks (g a)).length ≤ hF.toFinset.sup (fun a => (fromBlocks a).length) :=
    Finset.le_sup (f := fun a => (fromBlocks a).length) (by simpa using ha)
  change (fromBlocks (RayMapModel.embedding (prefixShift L) a)).length ≤ _ at hb
  rw [prefixShift_length] at hb
  dsimp [L] at hb
  omega

/-- The manuscript's four-colour obstruction for every finite nonchain in
the concrete, identified binary model, at the embedding level. -/
theorem ternary_no_universal_partition {A : Type*} [SemilatticeInf A]
    [language.Structure A] [MeetsInterpreted A]
    (hA : Nonempty (A ↪[language] TernaryModel)) {x y : A} (hxy : ¬x ≤ y) (hyx : ¬y ≤ x)
    (γ : (A ↪[language] TernaryModel) → Nat) (hγ : Unavoidable γ) :
    ∃ χ : (A ↪[language] TernaryModel) → Bool × Bool,
      ∀ f : TernaryModel ↪[language] TernaryModel, ¬ CanonicalOn γ χ f := by
  letI : Nonempty TernaryModel := ⟨RayTree.point ⟨[]⟩⟩
  obtain ⟨rank,hrank⟩ := exists_injective_nat TernaryModel
  exact no_universal_partition ternarySystem ternary_branch RayTree.isUltrahomogeneous
    hA hxy hyx rank (ternary_rank_avoidance rank hrank) γ hγ

end NoInfiniteCanonical
end AllThoseBigRamsey.Pseudotree
