import AllThoseBigRamsey.BooleanAlgebra.SignRuns

/-!
# Compensated signed words

This file proves the finite word identity used to obtain intervals of
intrinsic Boolean oscillation values.  A sign is a Boolean, with `false`
positive.  An optional cut contributes a head word and an even weight;
later probe packets cancel that dependence, leaving only the number of
changes in the final bit word.  Those changes attain every value from
zero to the word length.

The finite words are evaluated by the existing `SignRuns.runs` function.
No existence of Boolean cuts, block embeddings, or atomless refinements
is assumed or formalized here.
-/

namespace AllThoseBigRamsey.BooleanAlgebra.CompensatedWords

open SignRuns

def bit (q : Bool) : Nat := if q then 1 else 0

def head (q : Bool) : List Bool :=
  if q then [false, true, false] else [false, false]

def packet (q : Bool) : List Bool := [false, !q, false]

private def loop (changes : Nat) : Summary := ⟨false, false, changes⟩

private theorem loop_append (a b : Nat) :
    (loop a).append (loop b) = loop (a + b) := by
  simp [loop, Summary.append, jump]

private theorem summarize_head (q : Bool) :
    summarize (head q) = some (loop (2 * bit q)) := by
  cases q <;> rfl

private theorem summarize_packet (q : Bool) :
    summarize (packet q) = some (loop (2 * bit (!q))) := by
  cases q <;> rfl

private theorem repeat_loop (c n : Nat) :
    (loop c).repeatNonempty n = loop ((n + 1) * c) := by
  induction n with
  | zero => simp [Summary.repeatNonempty]
  | succ n ih =>
      simp only [Summary.repeatNonempty, ih, loop_append]
      apply congrArg loop
      simp only [Nat.add_mul, Nat.one_mul]
      omega

private theorem summarize_repeat_loop (w : List Bool) (c n : Nat)
    (hw : summarize w = some (loop c)) :
    summarize (repeatWord w (n + 1)) = some (loop ((n + 1) * c)) := by
  rw [summarize_repeat w (loop c) hw n, repeat_loop]

private theorem summarize_loop_append (u v : List Bool) (a b : Nat)
    (hu : summarize u = some (loop a))
    (hv : summarize v = some (loop b)) :
    summarize (u ++ v) = some (loop (a + b)) := by
  rw [summarize_append, hu, hv]
  simp only [merge, loop_append]

private theorem summarize_loop_flatMap
    (blocks : α → List Bool) (cost : α → Nat)
    (hblocks : ∀ x, summarize (blocks x) = some (loop (cost x)))
    (xs : List α) (leadWord : List Bool) (a : Nat)
    (hprefix : summarize leadWord = some (loop a)) :
    summarize (leadWord ++ xs.flatMap blocks) =
      some (loop (a + (xs.map cost).sum)) := by
  induction xs generalizing leadWord a with
  | nil => simpa using hprefix
  | cons x xs ih =>
      have hfirst := summarize_loop_append leadWord (blocks x) a (cost x)
        hprefix (hblocks x)
      have hrest := ih (leadWord ++ blocks x) (a + cost x) hfirst
      simpa only [List.flatMap_cons, List.map_cons, List.sum_cons,
        List.append_assoc, Nat.add_assoc] using hrest

def headCost (p : Bool × Nat) : Nat := 2 * bit p.1

def packetCost (p : Bool × Nat) : Nat := (p.2 + 1) * (2 * bit (!p.1))

def optionalWeight (p : Bool × Nat) : Nat := 2 * p.2 * bit p.1

def compensation (p : Bool × Nat) : Nat := 2 * (p.2 + 1)

def heads (data : List (Bool × Nat)) : List Bool :=
  data.flatMap (fun p => head p.1)

def packets (data : List (Bool × Nat)) : List Bool :=
  data.flatMap (fun p => repeatWord (packet p.1) (p.2 + 1))

def wordPrefix (data : List (Bool × Nat)) : List Bool :=
  ([false] ++ heads data) ++ packets data

def compensatedWord (data : List (Bool × Nat)) : List Bool :=
  wordPrefix data ++ data.map Prod.fst

private theorem summarize_prefix (data : List (Bool × Nat)) :
    summarize (wordPrefix data) =
      some (loop ((data.map headCost).sum + (data.map packetCost).sum)) := by
  have hhead := summarize_loop_flatMap
    (fun p : Bool × Nat => head p.1) headCost
    (fun p => summarize_head p.1) data [false] 0 (by rfl)
  simp only [Nat.zero_add] at hhead
  exact summarize_loop_flatMap
    (fun p : Bool × Nat => repeatWord (packet p.1) (p.2 + 1)) packetCost
    (fun p => summarize_repeat_loop (packet p.1) (2 * bit (!p.1)) p.2
      (summarize_packet p.1)) data ([false] ++ heads data)
    (data.map headCost).sum hhead

/-- Changes from a preceding sign, without counting an initial run. -/
def changesFrom (previous : Bool) : List Bool → Nat
  | [] => 0
  | q :: qs => jump previous q + changesFrom q qs

private def lastFrom (previous : Bool) : List Bool → Bool
  | [] => previous
  | q :: qs => lastFrom q qs

private theorem summarize_cons (a : Bool) (qs : List Bool) :
    summarize (a :: qs) = some ⟨a, lastFrom a qs, changesFrom a qs⟩ := by
  induction qs generalizing a with
  | nil => rfl
  | cons q qs ih =>
      change merge (some ⟨a, a, 0⟩) (summarize (q :: qs)) = _
      rw [ih q]
      simp [merge, Summary.append, lastFrom, changesFrom, Nat.add_comm]

def theta (qs : List Bool) : Nat := changesFrom false qs

theorem initial_run_formula (qs : List Bool) :
    runs (false :: qs) = 1 + theta qs := by
  simp only [runs, summarize_cons, Summary.runs, theta]
  omega

theorem theta_eq_runs_sub_one (qs : List Bool) :
    theta qs = runs (false :: qs) - 1 := by
  rw [initial_run_formula]
  omega

private theorem runs_append_loop (u qs : List Bool) (c : Nat)
    (hu : summarize u = some (loop c)) :
    runs (u ++ qs) = c + runs (false :: qs) := by
  cases hqs : summarize qs with
  | none =>
      simp [runs, summarize_append, hu, summarize, hqs, merge, loop,
        Summary.runs]
  | some s =>
      simp [runs, summarize_append, hu, summarize, hqs, merge, loop,
        Summary.runs, Summary.append, Nat.add_assoc]

theorem compensation_balance (p : Bool × Nat) :
    headCost p + packetCost p + optionalWeight p = compensation p := by
  obtain ⟨q, k⟩ := p
  cases q <;>
    simp [headCost, packetCost, optionalWeight, compensation, bit,
      Nat.mul_add, Nat.add_mul, Nat.mul_comm] <;> omega

private theorem sum_compensation_balance (data : List (Bool × Nat)) :
    (data.map headCost).sum + (data.map packetCost).sum +
        (data.map optionalWeight).sum = (data.map compensation).sum := by
  induction data with
  | nil => simp
  | cons p ps ih =>
      have hp := compensation_balance p
      simp only [List.map_cons, List.sum_cons]
      omega

/-- The optional even weights are cancelled by the probe packets.
All remaining variability is the final seam-change count `theta`. -/
theorem compensated_word_formula (data : List (Bool × Nat)) :
    runs (compensatedWord data) + (data.map optionalWeight).sum =
      1 + (data.map compensation).sum + theta (data.map Prod.fst) := by
  have hruns := runs_append_loop (wordPrefix data) (data.map Prod.fst)
    ((data.map headCost).sum + (data.map packetCost).sum)
    (summarize_prefix data)
  rw [initial_run_formula] at hruns
  have hbalance := sum_compensation_balance data
  change runs (wordPrefix data ++ data.map Prod.fst) + _ = _
  omega

/-- Recover signs from their successive change bits. -/
def integrate (previous : Bool) : List Bool → List Bool
  | [] => []
  | e :: es => (previous ^^ e) :: integrate (previous ^^ e) es

private theorem jump_xor (a e : Bool) : jump a (a ^^ e) = bit e := by
  cases a <;> cases e <;> rfl

theorem integrate_length (previous : Bool) (es : List Bool) :
    (integrate previous es).length = es.length := by
  induction es generalizing previous with
  | nil => rfl
  | cons e es ih => simp only [integrate, List.length_cons, ih]

theorem changesFrom_integrate (previous : Bool) (es : List Bool) :
    changesFrom previous (integrate previous es) = (es.map bit).sum := by
  induction es generalizing previous with
  | nil => rfl
  | cons e es ih =>
      simp only [integrate, changesFrom, jump_xor, ih, List.map_cons,
        List.sum_cons]

/-- A final word of length `m` can contribute any chosen number of new
runs between zero and `m`. -/
theorem theta_reaches (m j : Nat) (hj : j ≤ m) :
    ∃ qs : List Bool, qs.length = m ∧ theta qs = j := by
  let es := List.replicate j true ++ List.replicate (m - j) false
  refine ⟨integrate false es, ?_, ?_⟩
  · rw [integrate_length]
    simp only [es, List.length_append, List.length_replicate]
    omega
  · simp [theta, changesFrom_integrate, es, bit]

/-- With the even defect parameters fixed, the compensated values contain
the entire interval of length `ks.length + 1` above the same constant. -/
theorem compensated_interval (ks : List Nat) (j : Nat) (hj : j ≤ ks.length) :
    ∃ qs : List Bool, qs.length = ks.length ∧
      runs (compensatedWord (qs.zip ks)) +
          ((qs.zip ks).map optionalWeight).sum =
        1 + (ks.map (fun k => 2 * (k + 1))).sum + j := by
  obtain ⟨qs, hlength, htheta⟩ := theta_reaches ks.length j hj
  have hfst := List.map_fst_zip (l₁ := qs) (l₂ := ks) (by omega)
  have hsnd := List.map_snd_zip (l₁ := qs) (l₂ := ks) (by omega)
  have hcost : (qs.zip ks).map compensation =
      ks.map (fun k => 2 * (k + 1)) := by
    change (qs.zip ks).map (fun p => 2 * (p.2 + 1)) = _
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map (fun k => 2 * (k + 1))) hsnd
  refine ⟨qs, hlength, ?_⟩
  simpa only [hfst, hcost, htheta] using compensated_word_formula (qs.zip ks)

end AllThoseBigRamsey.BooleanAlgebra.CompensatedWords
