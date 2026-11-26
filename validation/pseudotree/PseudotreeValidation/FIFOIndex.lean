import PseudotreeValidation.SparseLex

/-!
# Breadth-first labels of the sparse FIFO tree

The stage of a ternary label is its heap index, with children 3s+1,
3s+2, 3s+3. This removes queue bookkeeping from later lifting proofs.
All statements concern the actual Sparse.stage / Sparse.code construction.
-/

namespace AllThoseBigRamsey.Pseudotree.Sparse.FIFO

def labelStage (w : Word) : Nat :=
  w.foldl (fun n a => 3*n+1+rank a) 0

@[simp] theorem labelStage_nil : labelStage [] = 0 := rfl

@[simp] theorem labelStage_snoc (w : Word) (a : TernaryLetter) :
    labelStage (w ++ [a]) = 3 * labelStage w + 1 + rank a := by
  simp [labelStage, List.foldl_append]

theorem rank_lt_three (a : TernaryLetter) : rank a < 3 := by
  cases a <;> decide

private theorem rank_inj {a b : TernaryLetter} (h : rank a = rank b) : a = b := by
  cases a <;> cases b <;> simp_all [rank]

def depthStart : Nat → Nat
  | 0 => 0
  | n+1 => 3 * depthStart n + 1

theorem depthStart_mono {n m : Nat} (h : n ≤ m) :
    depthStart n ≤ depthStart m := by
  induction m, h using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ m h ih =>
    simp only [depthStart]
    omega

/-- All labels at depth k are processed before every label at depth k+1. -/
theorem labelStage_bounds (w : Word) :
    depthStart w.length ≤ labelStage w ∧ labelStage w < depthStart (w.length+1) := by
  suffices h : ∀ w : Word, depthStart w.reverse.length ≤ labelStage w.reverse ∧
      labelStage w.reverse < depthStart (w.reverse.length+1) by
    simpa only [List.reverse_reverse] using h w.reverse
  intro w
  induction w with
  | nil => decide
  | cons a w ih =>
    simp only [List.reverse_cons, List.length_append, List.length_singleton,
      labelStage_snoc, depthStart]
    have ha := rank_lt_three a
    have hi := ih.2
    change labelStage w.reverse < 3 * depthStart w.reverse.length + 1 at hi
    omega

theorem labelStage_lt_of_length_lt {s t : Word} (h : s.length < t.length) :
    labelStage s < labelStage t :=
  (labelStage_bounds s).2.trans_le
    ((depthStart_mono (Nat.succ_le_of_lt h)).trans (labelStage_bounds t).1)

theorem labelStage_injective : Function.Injective labelStage := by
  intro s t heq
  have hlen : s.length = t.length := by
    rcases Nat.lt_trichotomy s.length t.length with h | h | h
    · exact False.elim ((Nat.ne_of_lt (labelStage_lt_of_length_lt h)) heq)
    · exact h
    · exact False.elim ((Nat.ne_of_lt (labelStage_lt_of_length_lt h)) heq.symm)
  have hh : ∀ u v : Word, u.length = v.length →
      labelStage u.reverse = labelStage v.reverse → u = v := by
    intro u
    induction u with
    | nil =>
      intro v hv _
      exact (List.length_eq_zero_iff.mp (by simpa using hv.symm)).symm
    | cons a u ih =>
      intro v hv hs
      cases v with
      | nil => simp at hv
      | cons b v =>
        simp only [List.reverse_cons, labelStage_snoc] at hs
        have ha := rank_lt_three a
        have hb := rank_lt_three b
        have hab : a = b := rank_inj (by omega)
        have huv : labelStage u.reverse = labelStage v.reverse := by omega
        rw [hab, ih v (by simpa using hv) huv]
  have h := hh s.reverse t.reverse (by simpa using hlen) (by simpa using heq)
  simpa only [List.reverse_reverse] using congrArg List.reverse h

theorem labelStage_surjective : Function.Surjective labelStage := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · exact ⟨[], hz.symm⟩
    · let k := (n-1)/3
      have hk : k < n := by dsimp [k]; omega
      obtain ⟨w, hw⟩ := ih k hk
      let r := (n-1)%3
      let a : TernaryLetter := if r = 0 then .zero else if r = 1 then .one else .two
      have hr : r < 3 := Nat.mod_lt _ (by decide)
      have ha : rank a = r := by
        by_cases h0 : r = 0
        · simp [a, h0, rank]
        · by_cases h1 : r = 1
          · simp [a, h0, h1, rank]
          · have h2 : r = 2 := by omega
            simp [a, h0, h1, h2, rank]
      refine ⟨w ++ [a], ?_⟩
      rw [labelStage_snoc, hw, ha]
      dsimp [k, r]
      omega

/-- The live slot before a stage, and the three literal successor slots. -/
def queueHead (n : Nat) : Word := (stage n).active.head!

def slotSuffix : TernaryLetter → Word
  | .zero => [.zero, .zero, .zero]
  | .one => [.zero, .two, .one]
  | .two => [.two, .two, .two]

@[simp] theorem slotSuffix_length (a : TernaryLetter) : (slotSuffix a).length = 3 := by
  cases a <;> rfl

theorem slotSuffix_noOne {a : TernaryLetter} (ha : a ≠ .one) :
    .one ∉ slotSuffix a := by
  cases a <;> simp_all [slotSuffix]

theorem slotSuffix_injective : Function.Injective slotSuffix := by
  intro a b h
  cases a <;> cases b <;> simp_all [slotSuffix]

@[simp] theorem queueHead_length (n : Nat) : (queueHead n).length = 3*n := by
  obtain ⟨u, rest, ha, hlen, _⟩ := active_head_exists n
  simpa [queueHead, ha, List.head!] using hlen

theorem code_eq_queueHead (n : Nat) :
    code n = queueHead n ++ [.zero, .two] := rfl

theorem queueHead_prefix_code (n : Nat) : (queueHead n).IsPrefix (code n) :=
  ⟨[.zero, .two], (code_eq_queueHead n).symm⟩

/-- Direct consequence of the checked exact FIFO child schedule. -/
theorem child_code (n : Nat) (a : TernaryLetter) :
    ∃ b : Word, .one ∉ b ∧
      code (3*n+1+rank a) = queueHead n ++ slotSuffix a ++ b := by
  obtain ⟨u, rest, ha, _, _⟩ := active_head_exists n
  obtain ⟨b, hb, heq⟩ := child_binary_code n (rank a) (rank_lt_three a) ha
  refine ⟨b, hb, ?_⟩
  cases a <;> simpa [rank, queueHead, ha, List.head!, newSlots, slotSuffix] using heq

theorem child_head (n : Nat) (a : TernaryLetter) :
    ∃ b : Word, .one ∉ b ∧
      queueHead (3*n+1+rank a) = queueHead n ++ slotSuffix a ++ b := by
  let m := 3*n+1+rank a
  obtain ⟨b, hb, heq⟩ := child_code n a
  change code m = queueHead n ++ slotSuffix a ++ b at heq
  have hs : (queueHead n ++ slotSuffix a).IsPrefix (code m) := ⟨b, heq.symm⟩
  have hlen : (queueHead n ++ slotSuffix a).length ≤ (queueHead m).length := by
    simp only [List.length_append, slotSuffix_length, queueHead_length]
    dsimp [m]
    omega
  obtain ⟨p, hp⟩ := List.prefix_of_prefix_length_le hs (queueHead_prefix_code m) hlen
  have hfull : (queueHead n ++ slotSuffix a) ++ (p ++ [.zero, .two]) =
      (queueHead n ++ slotSuffix a) ++ b := by
    rw [← List.append_assoc, hp, ← code_eq_queueHead, heq]
  have htail : p ++ [.zero, .two] = b := List.append_cancel_left hfull
  refine ⟨p, ?_, hp.symm⟩
  intro h
  exact hb (htail ▸ List.mem_append_left _ h)

/-- The two maps used by the manuscript's FIFO serialization. -/
def U (t : Word) : Word := queueHead (labelStage t)
def H (t : Word) : Word := code (labelStage t)

@[simp] theorem U_length (t : Word) : (U t).length = 3 * labelStage t :=
  queueHead_length _

@[simp] theorem H_length (t : Word) : (H t).length = 3 * labelStage t + 2 :=
  code_length _

theorem H_eq_U (t : Word) : H t = U t ++ [.zero, .two] := rfl

theorem U_prefix_H (t : Word) : (U t).IsPrefix (H t) :=
  queueHead_prefix_code _

theorem H_inTree (t : Word) : InTree (H t) := ⟨labelStage t, List.prefix_rfl⟩

theorem U_inTree (t : Word) : InTree (U t) :=
  inTree_prefix (H_inTree t) (U_prefix_H t)

theorem H_inSparse (t : Word) : InSparse (H t) :=
  (inSparse_iff_code _).mpr ⟨labelStage t, rfl⟩

theorem H_injective : Function.Injective H := by
  intro s t h
  exact labelStage_injective (code_injective h)

theorem H_surjective_sparse {w : Word} (hw : InSparse w) : ∃ t, H t = w := by
  obtain ⟨n, hn⟩ := (inSparse_iff_code w).mp hw
  obtain ⟨t, ht⟩ := labelStage_surjective n
  exact ⟨t, by rw [H, ht, hn]⟩

theorem U_child (t : Word) (a : TernaryLetter) :
    ∃ b, .one ∉ b ∧ U (t ++ [a]) = U t ++ slotSuffix a ++ b := by
  unfold U
  rw [labelStage_snoc]
  exact child_head (labelStage t) a

/-- Every binary label extension stays on the same actual geometric ray. -/
theorem U_descendant (t v : Word) :
    ∃ b : Word, U (t ++ v) = U t ++ b ∧ (.one ∉ v → .one ∉ b) := by
  induction v generalizing t with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons a v ih =>
    obtain ⟨p, hp, hpa⟩ := U_child t a
    obtain ⟨q, hq, hqbin⟩ := ih (t ++ [a])
    refine ⟨slotSuffix a ++ p ++ q, ?_, ?_⟩
    · calc
        U (t ++ a :: v) = U ((t ++ [a]) ++ v) := by simp [List.append_assoc]
        _ = U (t ++ [a]) ++ q := hq
        _ = U t ++ (slotSuffix a ++ p ++ q) := by simp [hpa, List.append_assoc]
    · intro h
      have ha : a ≠ .one := by intro he; subst a; exact h (by simp)
      have hv : .one ∉ v := fun hm => h (List.mem_cons_of_mem _ hm)
      simp [slotSuffix_noOne ha, hp, hqbin hv]

theorem H_descendant (t v : Word) :
    ∃ b : Word, H (t ++ v) = U t ++ b ∧ (.one ∉ v → .one ∉ b) := by
  obtain ⟨p, hp, hbin⟩ := U_descendant t v
  refine ⟨p ++ [.zero, .two], ?_, ?_⟩
  · simp only [H_eq_U, hp, List.append_assoc]
  · intro h
    simp [hbin h]

theorem U_branch (t : Word) (a : TernaryLetter) (v : Word) :
    ∃ b : Word, U (t ++ a :: v) = U t ++ slotSuffix a ++ b ∧
      (.one ∉ v → .one ∉ b) := by
  obtain ⟨p, hp, hpa⟩ := U_child t a
  obtain ⟨q, hq, hqbin⟩ := U_descendant (t ++ [a]) v
  refine ⟨p ++ q, ?_, ?_⟩
  · calc
      U (t ++ a :: v) = U ((t ++ [a]) ++ v) := by simp [List.append_assoc]
      _ = U (t ++ [a]) ++ q := hq
      _ = U t ++ slotSuffix a ++ (p ++ q) := by simp [hpa, List.append_assoc]
  · intro h
    simp [hp, hqbin h]

theorem H_branch (t : Word) (a : TernaryLetter) (v : Word) :
    ∃ b : Word, H (t ++ a :: v) = U t ++ slotSuffix a ++ b ∧
      (.one ∉ v → .one ∉ b) := by
  obtain ⟨p, hp, hbin⟩ := U_branch t a v
  refine ⟨p ++ [.zero, .two], ?_, ?_⟩
  · simp only [H_eq_U, hp, List.append_assoc]
  · intro h
    simp [hbin h]

theorem U_prefix_descendant (t v : Word) : (U t).IsPrefix (U (t ++ v)) := by
  obtain ⟨b, hb, _⟩ := U_descendant t v
  exact ⟨b, hb.symm⟩

theorem U_prefix_code_descendant (t v : Word) : (U t).IsPrefix (H (t ++ v)) :=
  (U_prefix_descendant t v).trans (U_prefix_H (t ++ v))

theorem U_branch_prefix (p : Word) (a : TernaryLetter) (v : Word) :
    (U p ++ slotSuffix a).IsPrefix (U (p ++ a :: v)) := by
  obtain ⟨b, hb, _⟩ := U_branch p a v
  exact ⟨b, hb.symm⟩

theorem H_branch_prefix (p : Word) (a : TernaryLetter) (v : Word) :
    (U p ++ slotSuffix a).IsPrefix (H (p ++ a :: v)) :=
  (U_branch_prefix p a v).trans (U_prefix_H _)

/-- The actual slots carry the lexicographic order of their labels. -/
theorem slots_lex (a b : TernaryLetter) (ha : a ≠ b) :
    lexLess (slotSuffix a) (slotSuffix b) = decide (rank a < rank b) := by
  cases a <;> cases b <;> simp_all [slotSuffix, lexLess, rank]

theorem slot_extensions_lex (p : Word) (a b : TernaryLetter) (ha : a ≠ b)
    (s t : Word) :
    lexLess (p ++ slotSuffix a ++ s) (p ++ slotSuffix b ++ t) =
      decide (rank a < rank b) := by
  simp only [List.append_assoc, lexLess_common_prefix]
  rw [lexLess_append_of_ne (by simp) (fun h => ha (slotSuffix_injective h))]
  exact slots_lex a b ha

theorem code_branches_lex (p : Word) (a b : TernaryLetter) (ha : a ≠ b)
    (s t : Word) :
    lexLess (H (p ++ a :: s)) (H (p ++ b :: t)) =
      lexLess (p ++ a :: s) (p ++ b :: t) := by
  obtain ⟨u, hu, _⟩ := H_branch p a s
  obtain ⟨v, hv, _⟩ := H_branch p b t
  rw [hu, hv, slot_extensions_lex _ _ _ ha, lexLess_common_prefix]
  have hr : rank a ≠ rank b := fun h => ha (rank_inj h)
  simp [lexLess, hr]

/-! Event geometry: source splits go to the first split of a stage,
other critical events to its coding node. -/

def eventLength (t : Word) (split : Bool) : Nat :=
  3 * labelStage t + if split then 0 else 2

def eventNode (t : Word) (split : Bool) : Word :=
  if split then U t else H t

@[simp] theorem eventNode_length (t : Word) (split : Bool) :
    (eventNode t split).length = eventLength t split := by
  cases split <;> simp [eventNode, eventLength]

theorem eventNode_critical (t : Word) (split : Bool) :
    eventNode t split = critical (eventLength t split) := by
  cases split
  · have hm : (3 * labelStage t + 2) % 3 = 2 := by omega
    have hd : (3 * labelStage t + 2) / 3 = labelStage t := by omega
    simpa [eventNode, eventLength, H, hd] using (critical_code _ hm).symm
  · have hm : (3 * labelStage t) % 3 = 0 := by omega
    have hd : (3 * labelStage t) / 3 = labelStage t := by omega
    simp [eventNode, eventLength, U, queueHead, critical, hm, hd]

theorem eventLength_strict_of_depth {s t : Word} (h : s.length < t.length)
    (a b : Bool) : eventLength s a < eventLength t b := by
  have hst := labelStage_lt_of_length_lt h
  cases a <;> cases b <;> simp [eventLength] <;> omega

/-- The sample for a waiting branch always exists at the critical length. -/
theorem sample_length {x t : Word} (h : x.length = t.length)
    (a : TernaryLetter) (split : Bool) :
    eventLength t split < (U (x ++ [a])).length := by
  have hl : t.length < (x ++ [a]).length := by simp [h]
  have hstage := labelStage_lt_of_length_lt hl
  cases split <;> simp only [eventLength, U_length, Bool.false_eq_true,
    if_false, if_true] <;> omega

def passingDigit (x t : Word) : TernaryLetter :=
  if lexLess x t then .zero else .two

def passingNode (x t : Word) (split : Bool) : Word :=
  (H (x ++ [passingDigit x t])).take (eventLength t split)

theorem passingNode_inTree (x t : Word) (split : Bool) :
    InTree (passingNode x t split) :=
  inTree_prefix (H_inTree _) (List.take_prefix _ _)

theorem passingNode_length {x t : Word} (h : x.length = t.length) (split : Bool) :
    (passingNode x t split).length = eventLength t split := by
  have hl := sample_length h (passingDigit x t) split
  have hle := (U_prefix_H (x ++ [passingDigit x t])).length_le
  rw [passingNode, List.length_take, Nat.min_eq_left (hl.le.trans hle)]

theorem passingNode_eq_head_take {x t : Word} (h : x.length = t.length)
    (split : Bool) :
    passingNode x t split =
      (U (x ++ [passingDigit x t])).take (eventLength t split) := by
  have hp := U_prefix_H (x ++ [passingDigit x t])
  have hl := sample_length h (passingDigit x t) split
  have heq := List.prefix_iff_eq_take.mp hp
  unfold passingNode
  rw [heq, List.take_take, Nat.min_eq_left hl.le]

theorem passingNode_prefix_descendant {x t : Word} (h : x.length = t.length)
    (split : Bool) (v : Word) :
    (passingNode x t split).IsPrefix
      (U ((x ++ [passingDigit x t]) ++ v)) := by
  rw [passingNode_eq_head_take h split]
  exact (List.take_prefix _ _).trans (U_prefix_descendant _ _)

private theorem equal_length_split {x t : Word} (hlen : x.length = t.length)
    (hne : x ≠ t) :
    ∃ p a b s v, x = p ++ a :: s ∧ t = p ++ b :: v ∧ a ≠ b := by
  induction x generalizing t with
  | nil => cases t <;> simp_all
  | cons a x ih =>
    cases t with
    | nil => simp at hlen
    | cons b t =>
      by_cases hab : a = b
      · subst b
        have hxt : x ≠ t := fun h => hne (congrArg (List.cons a) h)
        obtain ⟨p, c, d, s, v, hx, ht, hcd⟩ := ih (by simpa using hlen) hxt
        exact ⟨a :: p, c, d, s, v, by simp [hx], by simp [ht], hcd⟩
      · exact ⟨[], a, b, x, t, rfl, rfl, hab⟩

/-- Distinct same-depth labels are already separated at the active height.
This proves the noncritical-node comparison used in the lift formula. -/
theorem passingNode_geometry {x t : Word} (hlen : x.length = t.length)
    (hne : x ≠ t) (split : Bool) :
    passingNode x t split ≠ eventNode t split ∧
    lexLess (passingNode x t split) (eventNode t split) = lexLess x t := by
  obtain ⟨p, a, b, s, v, hx, ht, hab⟩ := equal_length_split hlen hne
  have hpt : p.length < t.length := by rw [ht]; simp
  have hstage := labelStage_lt_of_length_lt hpt
  have hbound : (U p ++ slotSuffix a).length ≤ eventLength t split := by
    cases split <;> simp [eventLength] <;> omega
  have hxs (d : TernaryLetter) :
      (U p ++ slotSuffix a).IsPrefix (H (x ++ [d])) := by
    rw [hx, List.append_assoc, List.cons_append]
    exact H_branch_prefix p a (s ++ [d])
  have hp₁ : (U p ++ slotSuffix a).IsPrefix (passingNode x t split) := by
    unfold passingNode
    exact List.prefix_of_prefix_length_le (hxs _) (List.take_prefix _ _)
      (by change (U p ++ slotSuffix a).length ≤ (passingNode x t split).length
          rw [passingNode_length hlen]; exact hbound)
  have hp₂ : (U p ++ slotSuffix b).IsPrefix (eventNode t split) := by
    have hpre : (U p ++ slotSuffix b).IsPrefix (U t) := by
      rw [ht]
      exact U_branch_prefix p b v
    cases split
    · exact hpre.trans (U_prefix_H t)
    · exact hpre
  constructor
  · intro heq
    have hp : (U p ++ slotSuffix a).IsPrefix (eventNode t split) := heq ▸ hp₁
    have hsame := (List.prefix_of_prefix_length_le hp hp₂ (by simp)).eq_of_length (by simp)
    exact hab (slotSuffix_injective (List.append_cancel_left hsame))
  · obtain ⟨q, hq⟩ := hp₁
    obtain ⟨r, hr⟩ := hp₂
    rw [← hq, ← hr, slot_extensions_lex _ _ _ hab, hx, ht, lexLess_common_prefix]
    have hne' : rank a ≠ rank b := fun heq => hab (rank_inj heq)
    simp [lexLess, hne']

/-- The very next digit on the sampled branch is the prescribed passing
digit, using the already checked unique-child rule of the sparse tree. -/
theorem passingEdge_prefix {x t : Word} (hlen : x.length = t.length)
    (hne : x ≠ t) (split : Bool) :
    (passingNode x t split ++ [passingDigit x t]).IsPrefix
      (U (x ++ [passingDigit x t])) := by
  let w := U (x ++ [passingDigit x t])
  let j := eventLength t split
  have hj : j < w.length := sample_length hlen _ _
  have htake : passingNode x t split = w.take j := passingNode_eq_head_take hlen split
  have hchild : InTree (passingNode x t split ++ [w[j]]) := by
    rw [htake, List.take_append_getElem hj]
    exact inTree_prefix (U_inTree _) (List.take_prefix _ _)
  have h := (critical_children j (passingNode x t split)
    (passingNode_inTree x t split) (passingNode_length hlen split) w[j]).mp hchild
  obtain ⟨hn, hlex⟩ := passingNode_geometry hlen hne split
  rw [← eventNode_critical t split] at h
  have ha : w[j] = passingDigit x t := by
    simpa [CriticalChildren, hn, direction, hlex, passingDigit] using h
  change (passingNode x t split ++ [passingDigit x t]).IsPrefix w
  rw [← ha, htake, List.take_append_getElem hj]
  exact List.take_prefix _ _

/-- Appending a binary tail to a label does not insert a ray change after
an earlier prefix of its image, once that prefix is beyond the last slot. -/
private theorem binary_suffix_of_prefix {p b q : Word} (hb : .one ∉ b)
    (hq : q.IsPrefix (p ++ b)) (hl : p.length ≤ q.length) :
    ∃ r, .one ∉ r ∧ p ++ b = q ++ r := by
  obtain ⟨r, hr⟩ := hq
  obtain ⟨v, hv⟩ := List.prefix_of_prefix_length_le (List.prefix_append p b)
    (show q.IsPrefix (p ++ b) from ⟨r, hr⟩) hl
  have hfull : p ++ (v ++ r) = p ++ b := by rw [← List.append_assoc, hv, hr]
  have heq := List.append_cancel_left hfull
  exact ⟨r, fun hm => hb (heq ▸ List.mem_append_right _ hm), hr.symm⟩

/-- Every later binary label continuation of a waiting branch preserves
the incoming binary digit and has binary padding throughout. -/
theorem passingEdge_binary {x t : Word} (hlen : x.length = t.length)
    (hne : x ≠ t) (split : Bool) (v : Word) (hv : .one ∉ v) :
    ∃ pad : Word, .one ∉ pad ∧
      H ((x ++ [passingDigit x t]) ++ v) =
        (passingNode x t split ++ [passingDigit x t]) ++ pad := by
  have hnonempty : x ≠ [] := by
    intro h
    have ht : t = [] := List.length_eq_zero_iff.mp (by simpa [h] using hlen.symm)
    exact hne (h.trans ht.symm)
  have hex : ∃ p a, x = p ++ [a] := by
    cases hrev : x.reverse with
    | nil => exact False.elim (hnonempty (by simpa using congrArg List.reverse hrev))
    | cons a p =>
      exact ⟨p.reverse, a, by simpa [List.reverse_cons] using congrArg List.reverse hrev⟩
  obtain ⟨p, a, hx⟩ := hex
  let d := passingDigit x t
  have hd : d ≠ .one := by unfold d passingDigit; split <;> decide
  have hpt : p.length < t.length := by rw [← hlen, hx]; simp
  have hstage := labelStage_lt_of_length_lt hpt
  have hbound : (U p ++ slotSuffix a).length ≤ eventLength t split := by
    cases split <;> simp [eventLength] <;> omega
  have hlabel : (x ++ [d]) ++ v = p ++ a :: d :: v := by simp [hx, List.append_assoc]
  obtain ⟨b, hb, hbb⟩ := H_branch p a (d :: v)
  have hbno := hbb (by simp [Ne.symm hd, hv])
  have hprefix : (passingNode x t split ++ [d]).IsPrefix (H ((x ++ [d]) ++ v)) :=
    (passingEdge_prefix hlen hne split).trans (U_prefix_code_descendant (x ++ [d]) v)
  rw [hlabel, hb] at hprefix ⊢
  apply binary_suffix_of_prefix hbno hprefix
  simp only [List.length_append, List.length_singleton, passingNode_length hlen split]
  simpa only [List.length_append] using hbound.trans (Nat.le_succ (eventLength t split))

end AllThoseBigRamsey.Pseudotree.Sparse.FIFO
