import AllThoseBigRamsey.Pseudotree.SparseOrder

/-! The manuscript now uses 0 < end-of-word < 2. This file defines
that comparison literally, not by changing the already validated one.
The FIFO queue itself is unchanged. The full word models are conjugate
by swapping 0 and 2; the fixed queue's geometry is proved separately. -/
namespace AllThoseBigRamsey.Pseudotree.RevisedConvention
open Sparse RayMapModel
abbrev Word := Sparse.Word

def binaryLERevised : List Bool → List Bool → Bool
  | [], [] => true
  | [], b :: _ => b
  | a :: _, [] => !a
  | a :: s, b :: t => if a == b then binaryLERevised s t else !a

def binaryMinRevised (s t : List Bool) : List Bool :=
  if binaryLERevised s t then s else t

def revisedWordBelow (s t : Word) : Prop :=
  RayTree.Below (fun a b => binaryLERevised a b = true) (parseWord s) (parseWord t)

def revisedWordMeet (s t : Word) : Word :=
  printWord (RayTree.meet binaryMinRevised (parseWord s) (parseWord t))

def mirrorLetter : TernaryLetter → TernaryLetter
  | .zero => .two
  | .one => .one
  | .two => .zero

def mirror (s : Word) : Word := s.map mirrorLetter

@[simp] theorem mirrorLetter_twice (a : TernaryLetter) :
    mirrorLetter (mirrorLetter a) = a := by cases a <;> rfl

@[simp] theorem mirror_twice (s : Word) : mirror (mirror s) = s := by
  simp [mirror,List.map_map,Function.comp_def]

@[simp] theorem mirror_length (s : Word) : (mirror s).length = s.length := by
  simp [mirror]

@[simp] theorem mirror_append (s t : Word) : mirror (s ++ t) = mirror s ++ mirror t := by
  simp [mirror]

def flipBits (s : List Bool) : List Bool := s.map Bool.not

@[simp] theorem flipBits_twice (s : List Bool) : flipBits (flipBits s) = s := by
  simp [flipBits,List.map_map,Function.comp_def]

theorem flipBits_injective : Function.Injective flipBits := by
  intro a b h
  simpa using congrArg flipBits h

/-- Literal binary comparison is the reflected old comparison. -/
theorem binaryLE_revised_eq (s t : List Bool) :
    binaryLERevised s t = binaryLE (flipBits s) (flipBits t) := by
  induction s generalizing t with
  | nil =>
    cases t with
    | nil => rfl
    | cons b t => cases b <;> rfl
  | cons a s ih =>
    cases t with
    | nil => cases a <;> rfl
    | cons b t =>
      cases a <;> cases b <;> simp [binaryLERevised,binaryLE,flipBits] <;> exact ih t

theorem parse_mirror (s : Word) :
    parseWord (mirror s) = RayTree.map flipBits (parseWord s) := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    change parseWord (mirrorLetter a :: mirror s) = _
    cases a <;> cases h : parseWord s <;>
      simp [mirrorLetter,parseWord,prependBlock,RayTree.map,ih,h,flipBits]

theorem mirror_below_iff (s t : Word) :
    wordBelow (mirror s) (mirror t) ↔ revisedWordBelow s t := by
  unfold wordBelow revisedWordBelow
  rw [parse_mirror,parse_mirror]
  exact RayTree.below_map_iff (f := flipBits)
    (fun h => flipBits_injective h)
    (fun a b => by rw [binaryLE_revised_eq]) (parseWord s) (parseWord t)

theorem revisedWordBelow_refl (s : Word) : revisedWordBelow s s :=
  (mirror_below_iff s s).mp (wordBelow_refl _)

theorem flipBits_min (s t : List Bool) :
    flipBits (binaryMinRevised s t) = binaryMin (flipBits s) (flipBits t) := by
  unfold binaryMinRevised binaryMin
  rw [binaryLE_revised_eq]
  split <;> rfl

theorem mirror_revisedMeet (s t : Word) :
    mirror (revisedWordMeet s t) = wordMeet (mirror s) (mirror t) := by
  have h : parseWord (mirror (revisedWordMeet s t)) =
      parseWord (wordMeet (mirror s) (mirror t)) := by
    simp only [parse_mirror,revisedWordMeet,wordMeet,parse_print]
    exact RayTree.map_meet (f := flipBits) (fun h => flipBits_injective h)
      flipBits_min (parseWord s) (parseWord t)
  simpa using congrArg printWord h

/-- The unchanged FIFO range is meet-closed also in the revised order.
The proof uses the original separator-origin invariant, which is
independent of the orientation of the binary order. -/
theorem revised_sparse_meet_closed {s t : Word} (hs : InSparse s) (ht : InSparse t) :
    InSparse (revisedWordMeet s t) := by
  have hmin : ∀ a b, binaryMinRevised a b = a ∨ binaryMinRevised a b = b := by
    intro a b
    unfold binaryMinRevised
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases RayTree.meet_operand_or_separator binaryMinRevised hmin (parseWord s) (parseWord t)
    with h | h | h | h
  · have he : revisedWordMeet s t = s := by simpa [revisedWordMeet] using congrArg printWord h
    simpa [he] using hs
  · have he : revisedWordMeet s t = t := by simpa [revisedWordMeet] using congrArg printWord h
    simpa [he] using ht
  · apply inSparse_origins hs
    have hp := (List.mem_map (f := printWord)).mpr ⟨_, h, rfl⟩
    simpa [Sparse.print_separatorRoots,revisedWordMeet] using hp
  · apply inSparse_origins ht
    have hp := (List.mem_map (f := printWord)).mpr ⟨_, h, rfl⟩
    simpa [Sparse.print_separatorRoots,revisedWordMeet] using hp

private theorem noOne_iff_point (s : Word) :
    NoOne s ↔ ∃ b, parseWord s = .point b := by
  induction s with
  | nil => simp [parseWord]
  | cons a s ih =>
      cases h : parseWord s with
      | point b =>
          have hs : NoOne s := ih.mpr ⟨b, h⟩
          cases a <;> simp [parseWord, prependBlock, h, hs]
      | above b t =>
          have hs : ¬ NoOne s := by
            intro hbin
            obtain ⟨c, hc⟩ := ih.mp hbin
            rw [h] at hc
            cases hc
          cases a <;> simp [parseWord, prependBlock, h, hs]

private theorem below_cons_same (a : TernaryLetter) (s t : Word) :
    revisedWordBelow (a :: s) (a :: t) ↔ revisedWordBelow s t := by
  cases a <;> cases hs : parseWord s <;> cases ht : parseWord t <;>
    simp [revisedWordBelow, parseWord, prependBlock, hs, ht, RayTree.Below, RayTree.first, binaryLERevised]

theorem below_common_prefix (p s t : Word) :
    revisedWordBelow (p ++ s) (p ++ t) ↔ revisedWordBelow s t := by
  induction p with
  | nil => rfl
  | cons a p ih => simpa only [List.cons_append, below_cons_same] using ih

private theorem below_nil_cons (a : TernaryLetter) (t : Word) :
    revisedWordBelow [] (a :: t) ↔ a ≠ .zero := by
  cases a <;> cases h : parseWord t <;>
    simp [revisedWordBelow, parseWord, prependBlock, h, RayTree.first, binaryLERevised]

private theorem below_cons_nil (a : TernaryLetter) (s : Word) :
    revisedWordBelow (a :: s) [] ↔ a = .zero ∧ NoOne s := by
  rw [noOne_iff_point]
  cases a <;> cases h : parseWord s <;>
    simp [revisedWordBelow, parseWord, prependBlock, h, RayTree.first, binaryLERevised]

private theorem below_cons_distinct (a b : TernaryLetter) (s t : Word)
    (hab : a ≠ b) : revisedWordBelow (a :: s) (b :: t) ↔ a = .zero ∧ NoOne s := by
  rw [noOne_iff_point]
  cases a <;> cases b <;> cases hs : parseWord s <;> cases ht : parseWord t <;>
    simp_all [revisedWordBelow, parseWord, prependBlock, RayTree.first, binaryLERevised]

private theorem binaryMinRevised_cons (a : Bool) (s t : List Bool) :
    binaryMinRevised (a :: s) (a :: t) = a :: binaryMinRevised s t := by
  simp only [binaryMinRevised, binaryLERevised, beq_self_eq_true, ↓reduceIte]
  split <;> rfl

private theorem meet_prependBlock (a : Bool) (s t : RayTree (List Bool)) :
    RayTree.meet binaryMinRevised (prependBlock a s) (prependBlock a t) =
      prependBlock a (RayTree.meet binaryMinRevised s t) := by
  cases s <;> cases t <;>
    simp [prependBlock, RayTree.meet, binaryMinRevised_cons]
  split <;> rfl

private theorem meet_cons_same (a : TernaryLetter) (s t : Word) :
    revisedWordMeet (a :: s) (a :: t) = a :: revisedWordMeet s t := by
  cases a
  · simp only [revisedWordMeet, parseWord, meet_prependBlock, printWord_prependBlock]
    rfl
  · simp [revisedWordMeet, parseWord, RayTree.meet, printWord]
  · simp only [revisedWordMeet, parseWord, meet_prependBlock, printWord_prependBlock]
    rfl

theorem meet_common_prefix (p s t : Word) :
    revisedWordMeet (p ++ s) (p ++ t) = p ++ revisedWordMeet s t := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [List.cons_append, meet_cons_same, ih]

/-- Appending any binary tail beyond the end of an older word preserves both
comparisons with that older word. -/
theorem shorter_binary_tail (c w b : Word) (hlen : c.length < w.length)
    (hb : .one ∉ b) :
    (revisedWordBelow c (w ++ b) ↔ revisedWordBelow c w) ∧
      (revisedWordBelow (w ++ b) c ↔ revisedWordBelow w c) := by
  have hbb : NoOne b := by
    intro a ha heq
    subst a
    exact hb ha
  induction c generalizing w with
  | nil =>
      cases w with
      | nil => simp at hlen
      | cons a w =>
          simp only [List.cons_append, below_nil_cons, below_cons_nil, noOne_append]
          simp [hbb]
  | cons a c ih =>
      cases w with
      | nil => simp at hlen
      | cons d w =>
          by_cases had : a = d
          · subst d
            simp only [List.cons_append, below_cons_same]
            exact ih w (by simpa using hlen)
          · have hda : d ≠ a := Ne.symm had
            simp only [List.cons_append, below_cons_distinct a d _ _ had,
              below_cons_distinct d a _ _ hda, noOne_append]
            simp [hbb]

/-- Different binary continuations of a word longer than `c` have the same
comparison profile with `c`. -/
theorem shorter_binary_tails (c w p q : Word) (hlen : c.length < w.length)
    (hp : .one ∉ p) (hq : .one ∉ q) :
    (revisedWordBelow c (w ++ p) ↔ revisedWordBelow c (w ++ q)) ∧
      (revisedWordBelow (w ++ p) c ↔ revisedWordBelow (w ++ q) c) := by
  obtain ⟨hp₁, hp₂⟩ := shorter_binary_tail c w p hlen hp
  obtain ⟨hq₁, hq₂⟩ := shorter_binary_tail c w q hlen hq
  exact ⟨hp₁.trans hq₁.symm, hp₂.trans hq₂.symm⟩

private theorem active_head (n : Nat) :
    ∃ u rest, (stage n).active = u :: rest ∧ u.length = 3 * n ∧ code n = u ++ [.zero, .two] := by
  have hn : (stage n).active ≠ [] := by
    intro heq
    have hlen := (stage_lengths n).1
    simp [heq] at hlen
  obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hn
  refine ⟨u, rest, ha, ?_, ?_⟩
  · exact active_length n u (by simp [ha])
  · simp [code, ha, List.head!, newCode]

/-- The first child is now strictly below the selected code. -/
theorem code_lower_child (n : Nat) :
    revisedWordBelow (code (3 * n + 1)) (code n) ∧
      ¬ revisedWordBelow (code n) (code (3 * n + 1)) := by
  obtain ⟨u, rest, ha, _, heq⟩ := active_head n
  obtain ⟨b, hb, hc⟩ := child_binary_code n 0 (by decide) ha
  simp only [Nat.add_zero, newSlots, List.getElem_cons_zero] at hc
  rw [heq, hc]
  simp only [List.append_assoc, List.cons_append, List.nil_append,
    below_common_prefix, below_cons_same]
  rw [below_cons_distinct .zero .two _ _ (by decide),
    below_cons_distinct .two .zero _ _ (by decide)]
  have hbb : NoOne b := by
    intro a ha heq
    subst a
    exact hb ha
  simp [hbb]

/-- The third child is now strictly above the selected code. -/
theorem code_upper_child (n : Nat) :
    revisedWordBelow (code n) (code (3 * n + 3)) ∧
      ¬ revisedWordBelow (code (3 * n + 3)) (code n) := by
  obtain ⟨u, rest, ha, _, heq⟩ := active_head n
  obtain ⟨b, hb, hc⟩ := child_binary_code n 2 (by decide) ha
  have hi : 3 * n + 1 + 2 = 3 * n + 3 := by omega
  rw [hi] at hc
  simp only [newSlots, List.getElem_cons_succ, List.getElem_cons_zero] at hc
  rw [heq, hc]
  simp only [List.append_assoc, List.cons_append, List.nil_append, below_common_prefix]
  rw [below_cons_distinct .zero .two _ _ (by decide),
    below_cons_distinct .two .zero _ _ (by decide)]
  simp [NoOne]

/-- The middle and third children form the fork in the revised model. -/
theorem code_fork (n : Nat) :
    revisedWordBelow (code n) (code (3 * n + 3)) ∧
    ¬ revisedWordBelow (code (3 * n + 3)) (code n) ∧
    revisedWordBelow (code n) (code (3 * n + 2)) ∧
    ¬ revisedWordBelow (code (3 * n + 2)) (code n) ∧
    revisedWordMeet (code (3 * n + 3)) (code (3 * n + 2)) = code n := by
  obtain ⟨u, rest, ha, _, heq⟩ := active_head n
  obtain ⟨p, hp, hc₂⟩ := child_binary_code n 2 (by decide) ha
  obtain ⟨q, hq, hc₁⟩ := child_binary_code n 1 (by decide) ha
  have hi₂ : 3 * n + 1 + 2 = 3 * n + 3 := by omega
  rw [hi₂] at hc₂
  simp only [newSlots, List.getElem_cons_succ, List.getElem_cons_zero] at hc₂
  have hi₁ : 3 * n + 1 + 1 = 3 * n + 2 := by omega
  rw [hi₁] at hc₁
  simp only [newSlots, List.getElem_cons_succ, List.getElem_cons_zero] at hc₁
  refine ⟨(code_upper_child n).1, (code_upper_child n).2, ?_, ?_, ?_⟩
  · rw [heq, hc₁]
    have hpref := below_common_prefix (u ++ [.zero, .two]) [] (.one :: q)
    simpa using hpref.mpr ((below_nil_cons .one q).mpr (by decide))
  · rw [heq, hc₁]
    have hpref := below_common_prefix (u ++ [.zero, .two]) (.one :: q) []
    simpa using fun h => (show ¬ revisedWordBelow (.one :: q) [] by
      simp [below_cons_nil]) (hpref.mp h)
  · rw [heq, hc₂, hc₁]
    simp only [List.append_assoc, List.cons_append, List.nil_append,
      meet_common_prefix]
    congr 1
    cases h : parseWord p <;>
      simp [revisedWordMeet, parseWord, prependBlock, h, RayTree.meet, binaryMinRevised,
        binaryLERevised, printWord, binaryLetter]

/-- A lower child has the same comparisons as its parent with every older
coding node. -/
theorem lower_child_profile {k n : Nat} (hkn : k < n) :
    (revisedWordBelow (code k) (code (3 * n + 1)) ↔ revisedWordBelow (code k) (code n)) ∧
    (revisedWordBelow (code (3 * n + 1)) (code k) ↔ revisedWordBelow (code n) (code k)) := by
  obtain ⟨u, rest, ha, hlen, heq⟩ := active_head n
  obtain ⟨b, hb, hc⟩ := child_binary_code n 0 (by decide) ha
  simp only [Nat.add_zero, newSlots, List.getElem_cons_zero] at hc
  rw [heq, hc, List.append_assoc]
  apply shorter_binary_tails
  · rw [code_length, hlen]
    omega
  · simp [hb]
  · simp

/-- An upper child has the same comparisons as its parent with every older
coding node. -/
theorem upper_child_profile {k n : Nat} (hkn : k < n) :
    (revisedWordBelow (code k) (code (3 * n + 3)) ↔ revisedWordBelow (code k) (code n)) ∧
    (revisedWordBelow (code (3 * n + 3)) (code k) ↔ revisedWordBelow (code n) (code k)) := by
  obtain ⟨u, rest, ha, hlen, heq⟩ := active_head n
  obtain ⟨b, hb, hc⟩ := child_binary_code n 2 (by decide) ha
  have hi : 3 * n + 1 + 2 = 3 * n + 3 := by omega
  rw [hi] at hc
  simp only [newSlots, List.getElem_cons_succ, List.getElem_cons_zero] at hc
  rw [heq, hc, List.append_assoc]
  apply shorter_binary_tails
  · rw [code_length, hlen]
    omega
  · simp [hb]
  · simp

/-- Every strict interval between actual coding nodes contains an actual
coding node. The child of the later-coded endpoint provides a witness. -/
theorem code_dense (n m : Nat) (hnm : revisedWordBelow (code n) (code m))
    (hmn : ¬ revisedWordBelow (code m) (code n)) :
    ∃ k, revisedWordBelow (code n) (code k) ∧ ¬ revisedWordBelow (code k) (code n) ∧
      revisedWordBelow (code k) (code m) ∧ ¬ revisedWordBelow (code m) (code k) := by
  rcases Nat.lt_trichotomy n m with h | h | h
  · obtain ⟨h₁, h₂⟩ := lower_child_profile h
    exact ⟨3 * m + 1, h₁.mpr hnm, fun hk => hmn (h₂.mp hk),
      (code_lower_child m).1, (code_lower_child m).2⟩
  · subst m
    exact False.elim (hmn (revisedWordBelow_refl _))
  · obtain ⟨h₁, h₂⟩ := upper_child_profile h
    exact ⟨3 * n + 3, (code_upper_child n).1, (code_upper_child n).2,
      h₂.mpr hnm, fun hk => hmn (h₁.mp hk)⟩

/-- Density of the literal meet-closed sparse set, without an isomorphism
hypothesis or an assumed fair scheduling principle. -/
theorem sparse_dense {s t : Word} (hs : InSparse s) (ht : InSparse t)
    (hst : revisedWordBelow s t) (hts : ¬ revisedWordBelow t s) :
    ∃ u, InSparse u ∧ revisedWordBelow s u ∧ ¬ revisedWordBelow u s ∧
      revisedWordBelow u t ∧ ¬ revisedWordBelow t u := by
  obtain ⟨n, rfl⟩ := (inSparse_iff_code s).mp hs
  obtain ⟨m, rfl⟩ := (inSparse_iff_code t).mp ht
  obtain ⟨k, hk⟩ := code_dense n m hst hts
  exact ⟨code k, (inSparse_iff_code _).mpr ⟨k, rfl⟩, hk⟩

/-- Both strict directions are inhabited at every point of the sparse set. -/
theorem sparse_no_endpoints {s : Word} (hs : InSparse s) :
    (∃ u, InSparse u ∧ revisedWordBelow u s ∧ ¬ revisedWordBelow s u) ∧
    (∃ v, InSparse v ∧ revisedWordBelow s v ∧ ¬ revisedWordBelow v s) := by
  obtain ⟨n, rfl⟩ := (inSparse_iff_code s).mp hs
  exact ⟨⟨code (3 * n + 1), (inSparse_iff_code _).mpr ⟨_, rfl⟩,
      code_lower_child n⟩,
    ⟨code (3 * n + 3), (inSparse_iff_code _).mpr ⟨_, rfl⟩,
      code_upper_child n⟩⟩

/-- At each sparse node, two sparse upper nodes have precisely that meet. -/
theorem sparse_fork {s : Word} (hs : InSparse s) :
    ∃ u v, InSparse u ∧ InSparse v ∧
      revisedWordBelow s u ∧ ¬ revisedWordBelow u s ∧
      revisedWordBelow s v ∧ ¬ revisedWordBelow v s ∧ revisedWordMeet u v = s := by
  obtain ⟨n, rfl⟩ := (inSparse_iff_code s).mp hs
  exact ⟨code (3 * n + 3), code (3 * n + 2),
    (inSparse_iff_code _).mpr ⟨_, rfl⟩, (inSparse_iff_code _).mpr ⟨_, rfl⟩,
    code_fork n⟩


end AllThoseBigRamsey.Pseudotree.RevisedConvention
