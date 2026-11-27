import Std

/-!
# Triangular Boolean block schemes

Boolean elements are represented by their actual characteristic functions.
Addition is exclusive-or and multiplication is conjunction.  For an ordered
triangular family `b`, the product of an earlier block sum with a later basis
element is controlled by the parity character of the earlier block.

This file proves the finite product criterion, its converse under uniqueness
of coefficients, and composition of the resulting incidence profiles.  It
does not assume or prove cofinality, atomlessness, fairness, or a Ramsey theorem.
Nonempty disjoint supports and their order are supplied by an application;
the algebraic character identities themselves allow arbitrary finite lists.
-/

namespace AllThoseBigRamsey.BooleanAlgebra.BlockSchemes

universe u v w

/-- Exclusive-or of a finite family, with the empty sum equal to zero. -/
def xorSum (xs : List ι) (f : ι → Bool) : Bool :=
  match xs with
  | [] => false
  | i :: is => f i ^^ xorSum is f

theorem xorSum_congr (xs : List ι) (f g : ι → Bool)
    (h : ∀ i ∈ xs, f i = g i) : xorSum xs f = xorSum xs g := by
  induction xs with
  | nil => rfl
  | cons i is ih =>
      simp only [xorSum]
      rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]

theorem xorSum_append (xs ys : List ι) (f : ι → Bool) :
    xorSum (xs ++ ys) f = (xorSum xs f ^^ xorSum ys f) := by
  induction xs with
  | nil =>
      simp only [List.nil_append, xorSum]
      cases xorSum ys f <;> rfl
  | cons i is ih =>
      simp only [List.cons_append, xorSum, ih, Bool.xor_assoc]

theorem xorSum_flatMap (xs : List κ) (blocks : κ → List ι)
    (f : ι → Bool) :
    xorSum (xs.flatMap blocks) f =
      xorSum xs (fun p => xorSum (blocks p) f) := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.flatMap_cons, xorSum_append, xorSum, ih]

theorem xorSum_and (xs : List ι) (f : ι → Bool) (c : Bool) :
    (xorSum xs f && c) = xorSum xs (fun i => f i && c) := by
  induction xs with
  | nil => rfl
  | cons i is ih =>
      simp only [xorSum]
      rw [← ih]
      cases f i <;> cases xorSum is f <;> cases c <;> rfl

theorem and_xorSum (xs : List ι) (f : ι → Bool) (c : Bool) :
    (c && xorSum xs f) = xorSum xs (fun i => c && f i) := by
  simpa only [Bool.and_comm] using xorSum_and xs f c

/-- The Boolean sum of the indicated basis elements. -/
def combination (b : ι → Ω → Bool) (xs : List ι) : Ω → Bool :=
  fun x => xorSum xs (fun i => b i x)

/-- A finite linear combination with explicit Boolean coefficients. -/
def weightedCombination (b : ι → Ω → Bool) (xs : List ι)
    (c : ι → Bool) : Ω → Bool :=
  fun x => xorSum xs (fun i => c i && b i x)

/-- The parity with which an earlier block sees one later basis element. -/
def character (ε : ι → ι → Bool) (xs : List ι) (j : ι) : Bool :=
  xorSum xs (fun i => ε i j)

/-- Coefficient uniqueness on the later finite family.  Actual linearly
independent Boolean bases supply this condition; it is not a Ramsey input. -/
def HasUniqueCoefficientsOn (b : ι → Ω → Bool) (xs : List ι) : Prop :=
  ∀ c d : ι → Bool,
    weightedCombination b xs c = weightedCombination b xs d →
      ∀ j ∈ xs, c j = d j

/-- Bilinearity and the triangular products compute every later coefficient.
The hypothesis is needed only for the indicated earlier/later pair of blocks. -/
theorem triangular_product_expansion
    (b : ι → Ω → Bool) (ε : ι → ι → Bool) (earlier later : List ι)
    (hTri : ∀ i ∈ earlier, ∀ j ∈ later, ∀ x,
      (b i x && b j x) = (ε i j && b j x)) :
    (fun x => combination b earlier x && combination b later x) =
      weightedCombination b later (character ε earlier) := by
  funext x
  unfold combination weightedCombination
  rw [and_xorSum]
  apply xorSum_congr
  intro j hj
  rw [xorSum_and]
  calc
    xorSum earlier (fun i => b i x && b j x) =
        xorSum earlier (fun i => ε i j && b j x) :=
      xorSum_congr earlier _ _ (fun i hi => hTri i hi j hj x)
    _ = (character ε earlier j && b j x) :=
      (xorSum_and earlier (fun i => ε i j) (b j x)).symm

theorem weightedCombination_constant (b : ι → Ω → Bool)
    (xs : List ι) (c : Bool) :
    weightedCombination b xs (fun _ => c) =
      fun x => c && combination b xs x := by
  funext x
  exact (and_xorSum xs (fun i => b i x) c).symm

/-- A constant character makes the product either zero or the whole later
block.  No coefficient uniqueness is needed for this direction. -/
theorem triangular_product_of_uniform
    (b : ι → Ω → Bool) (ε : ι → ι → Bool) (earlier later : List ι)
    (c : Bool)
    (hTri : ∀ i ∈ earlier, ∀ j ∈ later, ∀ x,
      (b i x && b j x) = (ε i j && b j x))
    (hUniform : ∀ j ∈ later, character ε earlier j = c) :
    (fun x => combination b earlier x && combination b later x) =
      fun x => c && combination b later x := by
  rw [triangular_product_expansion b ε earlier later hTri]
  calc
    weightedCombination b later (character ε earlier) =
        weightedCombination b later (fun _ => c) := by
      funext x
      apply xorSum_congr
      intro j hj
      rw [hUniform j hj]
    _ = _ := weightedCombination_constant b later c

/-- For an independent later family, local uniformity is also necessary.
This is the finite Boolean condensation criterion in coefficient form. -/
theorem triangular_product_scalar_iff
    (b : ι → Ω → Bool) (ε : ι → ι → Bool) (earlier later : List ι)
    (c : Bool)
    (hTri : ∀ i ∈ earlier, ∀ j ∈ later, ∀ x,
      (b i x && b j x) = (ε i j && b j x))
    (hUnique : HasUniqueCoefficientsOn b later) :
    ((fun x => combination b earlier x && combination b later x) =
        fun x => c && combination b later x) ↔
      ∀ j ∈ later, character ε earlier j = c := by
  constructor
  · intro h
    apply hUnique (character ε earlier) (fun _ => c)
    calc
      weightedCombination b later (character ε earlier) =
          (fun x => combination b earlier x && combination b later x) :=
        (triangular_product_expansion b ε earlier later hTri).symm
      _ = (fun x => c && combination b later x) := h
      _ = weightedCombination b later (fun _ => c) :=
        (weightedCombination_constant b later c).symm
  · exact triangular_product_of_uniform b ε earlier later c hTri

/-- Grouping blocks sums their characters.  With disjoint supports, flatMap
is literal block union, so no cancellation of support indices occurs. -/
theorem character_flatMap (ε : ι → ι → Bool)
    (blocks : κ → List ι) (group : List κ) (j : ι) :
    character ε (group.flatMap blocks) j =
      xorSum group (fun p => character ε (blocks p) j) :=
  xorSum_flatMap group blocks (fun i => ε i j)

/-- Two successive groupings give the same actual Boolean element as their
single composite grouping. -/
theorem combination_flatMap (b : ι → Ω → Bool)
    (blocks : κ → List ι) (group : List κ) :
    combination b (group.flatMap blocks) =
      combination (fun p => combination b (blocks p)) group := by
  funext x
  exact xorSum_flatMap group blocks (fun i => b i x)

/-- Incidences of each earlier condensed generator are constant on each
later block.  This records the triangular multiplication table after grouping. -/
def UniformProfiles (ε : ι → ι → Bool) (blocks : Nat → List ι)
    (η : Nat → Nat → Bool) : Prop :=
  ∀ p q, p < q → ∀ j ∈ blocks q, character ε (blocks p) j = η p q

/-- If both levels of grouping have constant incidence profiles, the
composite grouping has the expected profile.  Separation concerns the
intermediate block indices and is exactly the order needed in this proof. -/
theorem uniformProfiles_comp
    (ε : ι → ι → Bool) (blocks : Nat → List ι)
    (η : Nat → Nat → Bool) (groups : Nat → List Nat)
    (θ : Nat → Nat → Bool)
    (hFirst : UniformProfiles ε blocks η)
    (hSecond : UniformProfiles η groups θ)
    (hSeparated : ∀ r s, r < s →
      ∀ p ∈ groups r, ∀ q ∈ groups s, p < q) :
    UniformProfiles ε (fun r => (groups r).flatMap blocks) θ := by
  intro r s hrs j hj
  obtain ⟨q, hq, hj⟩ := List.mem_flatMap.mp hj
  rw [character_flatMap]
  calc
    xorSum (groups r) (fun p => character ε (blocks p) j) =
        xorSum (groups r) (fun p => η p q) := by
      apply xorSum_congr
      intro p hp
      exact hFirst p q (hSeparated r s hrs p hp q hq) j hj
    _ = θ r s := hSecond r s hrs q hq

/-- Constant valuations from the finite initial algebra must also survive
condensation.  This condition is separate from the triangular tail table. -/
def BaseProfiles (valuation : α → ι → Bool) (blocks : κ → List ι)
    (profile : α → κ → Bool) : Prop :=
  ∀ a p, ∀ j ∈ blocks p, valuation a j = profile a p

theorem baseProfiles_comp
    (valuation : α → ι → Bool) (blocks : κ → List ι)
    (profile : α → κ → Bool) (groups : ν → List κ)
    (result : α → ν → Bool)
    (hFirst : BaseProfiles valuation blocks profile)
    (hSecond : BaseProfiles profile groups result) :
    BaseProfiles valuation (fun r => (groups r).flatMap blocks) result := by
  intro a r j hj
  obtain ⟨p, hp, hj⟩ := List.mem_flatMap.mp hj
  exact (hFirst a p j hj).trans (hSecond a r p hp)

/-- Uniform valuations also preserve multiplication by the initial algebra.
This is the additional compatibility needed when the initial algebra has
more than the two constant elements. -/
theorem condensed_base_products
    (a : α → Ω → Bool) (b : ι → Ω → Bool)
    (valuation : α → ι → Bool) (blocks : κ → List ι)
    (profile : α → κ → Bool)
    (hBase : ∀ t i x, (a t x && b i x) = (valuation t i && b i x))
    (hUniform : BaseProfiles valuation blocks profile) :
    ∀ t p x, (a t x && combination b (blocks p) x) =
      (profile t p && combination b (blocks p) x) := by
  intro t p x
  unfold combination
  rw [and_xorSum, and_xorSum]
  apply xorSum_congr
  intro i hi
  rw [hBase, hUniform t p i hi]

/-- A uniform ordered grouping of an actual triangular family is again
triangular, with exactly the specified new incidence table. -/
theorem condensed_triangular
    (b : Nat → Ω → Bool) (ε : Nat → Nat → Bool)
    (blocks : Nat → List Nat) (η : Nat → Nat → Bool)
    (hTri : ∀ i j, i < j → ∀ x, (b i x && b j x) = (ε i j && b j x))
    (hSeparated : ∀ p q, p < q →
      ∀ i ∈ blocks p, ∀ j ∈ blocks q, i < j)
    (hUniform : UniformProfiles ε blocks η) :
    ∀ p q, p < q → ∀ x,
      (combination b (blocks p) x && combination b (blocks q) x) =
        (η p q && combination b (blocks q) x) := by
  intro p q hpq x
  have h := triangular_product_of_uniform b ε (blocks p) (blocks q) (η p q)
    (fun i hi j hj => hTri i j (hSeparated p q hpq i hi j hj))
    (hUniform p q hpq)
  exact congrFun h x

end AllThoseBigRamsey.BooleanAlgebra.BlockSchemes
