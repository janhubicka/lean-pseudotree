import AllThoseBigRamsey.BooleanAlgebra.BlockSchemes

/-!
# Signed support words and compatible block substitution

A sign is a Boolean parity: `false` is positive and `true` is negative.
While reading a finite support in order, the sign at a basis index is the
parity with which the earlier selected indices contain that basis cut.
An initial offset accommodates a previously fixed Boolean element.

The main theorem computes the full word under a compatible block
substitution.  Each substituted block contributes its own internal word,
reversed precisely by the corresponding source sign.  The hypotheses are
finite incidence equations, not Ramsey assumptions.  To interpret the
flattened list as an ordered set support, an application additionally uses
its nonempty disjoint ordered block supports.
-/

namespace AllThoseBigRamsey.BooleanAlgebra.SignedSupport

open BlockSchemes

/-- Add one constant parity to every sign. -/
def flip (c : Bool) (w : List Bool) : List Bool :=
  w.map (fun s => c ^^ s)

/-- Read incidence parities, retaining the contribution of an old element
in `offset`.  Appending the current index updates all future parities. -/
def wordFrom (ε : ι → ι → Bool) (offset : ι → Bool) : List ι → List Bool
  | [] => []
  | i :: is => offset i ::
      wordFrom ε (fun j => offset j ^^ ε i j) is

def word (ε : ι → ι → Bool) (xs : List ι) : List Bool :=
  wordFrom ε (fun _ => false) xs

theorem wordFrom_length (ε : ι → ι → Bool) (offset : ι → Bool)
    (xs : List ι) : (wordFrom ε offset xs).length = xs.length := by
  induction xs generalizing offset with
  | nil => rfl
  | cons i is ih => simp only [wordFrom, List.length_cons, ih]

/-- Only the initial offset values on the actual support matter. -/
theorem wordFrom_congr (ε : ι → ι → Bool) (xs : List ι)
    (offset offset' : ι → Bool)
    (h : ∀ i ∈ xs, offset i = offset' i) :
    wordFrom ε offset xs = wordFrom ε offset' xs := by
  induction xs generalizing offset offset' with
  | nil => rfl
  | cons i is ih =>
      simp only [wordFrom]
      rw [h i (by simp)]
      congr 1
      apply ih
      intro j hj
      rw [h j (by simp [hj])]

theorem wordFrom_flip (ε : ι → ι → Bool) (xs : List ι)
    (offset : ι → Bool) (c : Bool) :
    wordFrom ε (fun j => c ^^ offset j) xs = flip c (wordFrom ε offset xs) := by
  induction xs generalizing offset with
  | nil => rfl
  | cons i is ih =>
      simp only [wordFrom, flip, List.map_cons, Bool.xor_assoc]
      exact congrArg (List.cons (c ^^ offset i))
        (ih (fun j => offset j ^^ ε i j))

/-- A constant old valuation changes all signs of the internal block by
that same parity. -/
theorem wordFrom_uniform (ε : ι → ι → Bool) (xs : List ι)
    (offset : ι → Bool) (c : Bool)
    (h : ∀ i ∈ xs, offset i = c) :
    wordFrom ε offset xs = flip c (word ε xs) := by
  calc
    wordFrom ε offset xs = wordFrom ε (fun _ => c) xs :=
      wordFrom_congr ε xs offset (fun _ => c) h
    _ = flip c (word ε xs) := by
      simpa only [Bool.xor_false, word] using
        wordFrom_flip ε xs (fun _ => false) c

/-- Concatenation adds the full earlier-block character to the offset
used for the later block. -/
theorem wordFrom_append (ε : ι → ι → Bool) (xs ys : List ι)
    (offset : ι → Bool) :
    wordFrom ε offset (xs ++ ys) = wordFrom ε offset xs ++
      wordFrom ε (fun j => offset j ^^ character ε xs j) ys := by
  induction xs generalizing offset with
  | nil =>
      simp only [List.nil_append, wordFrom, character, xorSum, Bool.xor_false]
  | cons i is ih =>
      simp only [List.cons_append, wordFrom, ih, character, xorSum,
        Bool.xor_assoc]

theorem word_append (ε : ι → ι → Bool) (xs ys : List ι) :
    word ε (xs ++ ys) = word ε xs ++ wordFrom ε (character ε xs) ys := by
  simpa only [word, Bool.false_xor] using
    wordFrom_append ε xs ys (fun _ => false)

/-- The block word determined by the source signs, written recursively. -/
def evaluatedBlocks (ε : Nat → Nat → Bool) (blockWords : Nat → List Bool)
    (offset : Nat → Bool) : List Nat → List Bool
  | [] => []
  | p :: ps => flip (offset p) (blockWords p) ++
      evaluatedBlocks ε blockWords (fun q => offset q ^^ ε p q) ps

/-- The recursive formula is literal signed substitution into the source
word; no reduction of runs or deletion of internal signs is performed. -/
theorem evaluatedBlocks_eq_zip
    (ε : Nat → Nat → Bool) (blockWords : Nat → List Bool)
    (xs : List Nat) (offset : Nat → Bool) :
    evaluatedBlocks ε blockWords offset xs =
      ((xs.zip (wordFrom ε offset xs)).map
        (fun p => flip p.2 (blockWords p.1))).flatten := by
  induction xs generalizing offset with
  | nil => rfl
  | cons p ps ih =>
      simp only [evaluatedBlocks, wordFrom, List.zip_cons_cons, List.map_cons,
        List.flatten_cons, ih]

/-- An offset-compatible triangular substitution preserves the signed
evaluation formula on every listed source support. -/
theorem wordFrom_block_substitution
    (ε : Nat → Nat → Bool) (δ : ι → ι → Bool)
    (blocks : Nat → List ι) (xs : List Nat)
    (hProfiles : UniformProfiles δ blocks ε)
    (hOrder : xs.Pairwise (fun p q => p < q))
    (sourceOffset : Nat → Bool) (targetOffset : ι → Bool)
    (hOffsets : ∀ p ∈ xs, ∀ j ∈ blocks p, targetOffset j = sourceOffset p) :
    wordFrom δ targetOffset (xs.flatMap blocks) =
      evaluatedBlocks ε (fun p => word δ (blocks p)) sourceOffset xs := by
  induction xs generalizing sourceOffset targetOffset with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨hHead, hTail⟩ := List.pairwise_cons.mp hOrder
      simp only [List.flatMap_cons, evaluatedBlocks]
      rw [wordFrom_append]
      rw [wordFrom_uniform δ (blocks p) targetOffset (sourceOffset p)
        (hOffsets p (by simp))]
      congr 1
      apply ih hTail
      intro q hq j hj
      rw [hOffsets q (by simp [hq]) j hj,
        hProfiles p q (hHead q hq) j hj]

/-- Exact signed support evaluation under compatible block substitution:
the image word concatenates each block's internal word, flipped by the
source sign at that block. -/
theorem word_block_substitution
    (ε : Nat → Nat → Bool) (δ : ι → ι → Bool)
    (blocks : Nat → List ι) (xs : List Nat)
    (hProfiles : UniformProfiles δ blocks ε)
    (hOrder : xs.Pairwise (fun p q => p < q)) :
    word δ (xs.flatMap blocks) =
      ((xs.zip (word ε xs)).map
        (fun p => flip p.2 (word δ (blocks p.1)))).flatten := by
  have h := wordFrom_block_substitution ε δ blocks xs hProfiles hOrder
    (fun _ => false) (fun _ => false) (fun _ _ _ _ => rfl)
  rw [evaluatedBlocks_eq_zip] at h
  exact h

/-- A list with no earlier containment has an entirely positive support
word.  This is a finite calculation, not a cofinality assertion. -/
theorem word_of_antichain (ε : ι → ι → Bool) (xs : List ι)
    (h : xs.Pairwise (fun i j => ε i j = false)) :
    word ε xs = List.replicate xs.length false := by
  induction xs with
  | nil => rfl
  | cons i is ih =>
      obtain ⟨hHead, hTail⟩ := List.pairwise_cons.mp h
      simp only [word, wordFrom, Bool.false_xor, List.length_cons,
        List.replicate_succ]
      congr 1
      calc
        wordFrom ε (fun j => ε i j) is = word ε is :=
          wordFrom_congr ε is (fun j => ε i j) (fun _ => false) hHead
        _ = _ := ih hTail

end AllThoseBigRamsey.BooleanAlgebra.SignedSupport
