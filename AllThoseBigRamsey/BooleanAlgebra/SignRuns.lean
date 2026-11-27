import Std

/-!
# Runs of signed words and reflected blocks

This file checks the finite-word calculation used in the reflected-copy
obstruction.  It does not formalize the interval Boolean algebra, the dyadic
endpoint enumeration, or the infinite Boolean embedding.
-/

namespace AllThoseBigRamsey.BooleanAlgebra.SignRuns

structure Summary where
  first : Bool
  last : Bool
  changes : Nat
  deriving DecidableEq

def jump (a b : Bool) : Nat := if a = b then 0 else 1

theorem jump_symm (a b : Bool) : jump a b = jump b a := by
  cases a <;> cases b <;> rfl

theorem jump_neg (a b : Bool) : jump (!a) (!b) = jump a b := by
  cases a <;> cases b <;> rfl

theorem jump_opposite (a : Bool) : jump a (!a) = 1 := by
  cases a <;> rfl

namespace Summary

def append (s t : Summary) : Summary :=
  ⟨s.first, t.last, s.changes + t.changes + jump s.last t.first⟩

def reverse (s : Summary) : Summary := ⟨s.last, s.first, s.changes⟩

def negate (s : Summary) : Summary := ⟨!s.first, !s.last, s.changes⟩

def runs (s : Summary) : Nat := s.changes + 1

theorem append_assoc (s t u : Summary) :
    append (append s t) u = append s (append t u) := by
  cases s; cases t; cases u
  simp [append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem reverse_append (s t : Summary) :
    reverse (append s t) = append (reverse t) (reverse s) := by
  cases s; cases t
  simp [reverse, append, jump_symm, Nat.add_comm]

theorem negate_append (s t : Summary) :
    negate (append s t) = append (negate s) (negate t) := by
  simp [negate, append, jump_neg]

theorem append_runs_lower (s t : Summary) :
    runs s + runs t ≤ runs (append s t) + 1 := by
  simp only [runs, append]
  omega

theorem append_runs_of_opposite (s t : Summary) (h : s.last ≠ t.first) :
    runs (append s t) = runs s + runs t := by
  simp only [runs, append, jump, ite_eq_right h]
  omega

theorem reflected_pair_runs (s : Summary) :
    runs (append s (negate (reverse s))) = 2 * runs s := by
  simp only [runs, append, negate, reverse, jump_opposite]
  omega

/-- A summary of `n+1` consecutive nonempty copies. -/
def repeatNonempty (s : Summary) : Nat → Summary
  | 0 => s
  | n + 1 => append s (repeatNonempty s n)

theorem repeat_first (s : Summary) (n : Nat) :
    (repeatNonempty s n).first = s.first := by
  cases n <;> rfl

theorem repeat_runs_of_opposite (s : Summary) (n : Nat)
    (h : s.last ≠ s.first) :
    runs (repeatNonempty s n) = (n + 1) * runs s := by
  induction n with
  | zero => simp [repeatNonempty]
  | succ n ih =>
      have hj : s.last ≠ (repeatNonempty s n).first := by
        simpa [repeat_first] using h
      rw [repeatNonempty, append_runs_of_opposite s _ hj, ih]
      simp only [Nat.add_mul, Nat.one_mul]
      omega

end Summary

def merge : Option Summary → Option Summary → Option Summary
  | none, t => t
  | s, none => s
  | some s, some t => some (s.append t)

theorem merge_assoc (s t u : Option Summary) :
    merge (merge s t) u = merge s (merge t u) := by
  cases s <;> cases t <;> cases u <;> simp [merge, Summary.append_assoc]

def summarize : List Bool → Option Summary
  | [] => none
  | a :: w => merge (some ⟨a,a,0⟩) (summarize w)

theorem summarize_append (v w : List Bool) :
    summarize (v ++ w) = merge (summarize v) (summarize w) := by
  induction v with
  | nil => rfl
  | cons a v ih => simp [summarize, ih, merge_assoc]

theorem summarize_singleton (a : Bool) : summarize [a] = some ⟨a,a,0⟩ := rfl

theorem summarize_reverse (w : List Bool) :
    summarize w.reverse = (summarize w).map Summary.reverse := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp only [List.reverse_cons, summarize_append, summarize_singleton, ih]
      cases hw : summarize w with
      | none => simp [summarize, hw, merge, Summary.reverse]
      | some s =>
          simp [summarize, hw, merge, Summary.reverse, Summary.append,
            jump_symm, Nat.add_comm]

theorem summarize_negate (w : List Bool) :
    summarize (w.map Bool.not) = (summarize w).map Summary.negate := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp only [List.map_cons, summarize, ih]
      cases hw : summarize w with
      | none => simp [merge, Summary.negate]
      | some s => simp [merge, Summary.negate, Summary.append, jump_neg]

def reflected (w : List Bool) : List Bool := w.reverse.map Bool.not

theorem summarize_reflected (w : List Bool) :
    summarize (reflected w) =
      (summarize w).map (fun s => s.reverse.negate) := by
  unfold reflected
  rw [summarize_negate, summarize_reverse]
  cases summarize w <;> rfl

def runs (w : List Bool) : Nat :=
  match summarize w with
  | none => 0
  | some s => s.runs

/-- Each join between a word and its reversed sign-complement is a change,
so reflection doubles the run count exactly, including the empty case. -/
theorem reflected_pair_runs (w : List Bool) :
    runs (w ++ reflected w) = 2 * runs w := by
  simp only [runs, summarize_append, summarize_reflected]
  cases hw : summarize w with
  | none => rfl
  | some s => exact Summary.reflected_pair_runs s

/-- Concatenating two arbitrary depth blocks can lose at most one run. -/
theorem append_runs_lower (v w : List Bool) :
    runs v + runs w ≤ runs (v ++ w) + 1 := by
  simp only [runs, summarize_append]
  cases hv : summarize v <;> cases hw : summarize w
  · decide
  · simp [merge]
  · simp [merge]
  · exact Summary.append_runs_lower _ _

theorem negate_runs (w : List Bool) : runs (w.map Bool.not) = runs w := by
  simp only [runs, summarize_negate]
  cases summarize w <;> rfl

theorem append_runs_left (v w : List Bool) : runs v ≤ runs (v ++ w) := by
  simp only [runs, summarize_append]
  cases summarize v <;> cases summarize w <;>
    simp [merge, Summary.runs, Summary.append] <;> omega

theorem append_runs_right (v w : List Bool) : runs w ≤ runs (v ++ w) := by
  simp only [runs, summarize_append]
  cases summarize v <;> cases summarize w <;>
    simp [merge, Summary.runs, Summary.append] <;> omega

/-- A whole consecutive boundary block cannot have more runs than the word
containing it.  This is used for fresh cuts in a Boolean partition refinement. -/
theorem middle_runs_le (v w z : List Bool) : runs w ≤ runs (v ++ w ++ z) :=
  Nat.le_trans (append_runs_right v w) (append_runs_left (v ++ w) z)

/-- Removing a high-endpoint subpiece appends the negation of its signed word;
if that subpiece has both signs, the old run count strictly increases. -/
theorem remove_block_growth (v w : List Bool) (hw : 2 ≤ runs w) :
    runs v + 1 ≤ runs (v ++ w.map Bool.not) := by
  have h := append_runs_lower v (w.map Bool.not)
  rw [negate_runs] at h
  omega

def repeatWord (w : List Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => w ++ repeatWord w n

theorem summarize_repeat (w : List Bool) (s : Summary)
    (hw : summarize w = some s) (n : Nat) :
    summarize (repeatWord w (n + 1)) = some (s.repeatNonempty n) := by
  induction n with
  | zero => simp [repeatWord, hw, Summary.repeatNonempty]
  | succ n ih =>
      change summarize (w ++ repeatWord w (n + 1)) =
        some (s.append (s.repeatNonempty n))
      rw [summarize_append, hw, ih]
      rfl

theorem repeatWord_nil (n : Nat) : repeatWord [] n = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatWord, ih]

theorem summarize_none_iff (w : List Bool) : summarize w = none ↔ w = [] := by
  cases w with
  | nil => simp [summarize]
  | cons a w => cases hs : summarize w <;> simp [summarize, hs, merge]

/-- The exact identity for any even number `2*n` of alternating forward and
reflected sign blocks.  This is the per-depth calculation in the obstruction. -/
theorem reflected_blocks_runs (w : List Bool) (n : Nat) :
    runs (repeatWord (w ++ reflected w) n) = (2 * n) * runs w := by
  cases hw : summarize w with
  | none =>
      have he : w = [] := (summarize_none_iff w).mp hw
      subst w
      simp [reflected, repeatWord_nil, runs, summarize]
  | some s =>
      have hp : summarize (w ++ reflected w) = some (s.append s.reverse.negate) := by
        rw [summarize_append, summarize_reflected, hw]
        rfl
      cases n with
      | zero => simp [repeatWord, runs, summarize]
      | succ n =>
          have ho : (s.append s.reverse.negate).last ≠
              (s.append s.reverse.negate).first := by
            cases h : s.first <;> simp [Summary.append, Summary.negate,
              Summary.reverse, h]
          simp only [runs, summarize_repeat _ _ hp, hw]
          rw [Summary.repeat_runs_of_opposite _ _ ho, Summary.reflected_pair_runs]
          simp [Nat.mul_assoc, Nat.mul_comm]

/-- Joining `h` nonempty or empty depth blocks loses at most `h-1` runs. -/
theorem flatten_runs_lower (ws : List (List Bool)) :
    (ws.map runs).sum ≤ runs ws.flatten + (ws.length - 1) := by
  induction ws with
  | nil => simp [runs, summarize]
  | cons w ws ih =>
      cases ws with
      | nil => simp
      | cons v vs =>
          have hj := append_runs_lower w ((v :: vs).flatten)
          simp only [List.flatten_cons, List.map_cons, List.sum_cons,
            List.length_cons] at *
          omega

end AllThoseBigRamsey.BooleanAlgebra.SignRuns
