import PseudotreeValidation.FIFOIndex

/-! Assemble the local FIFO cone facts into the exact lift of one edge.
The source may be finite or infinite. The child is a prefix of a sampled
coding point, and the sample tail is always binary. -/
namespace AllThoseBigRamsey.Pseudotree.Sparse.FIFO

def sampleTail (x t : Word) : Word :=
  if x = t then [] else [passingDigit x t]

def liftedNode (x t : Word) (split : Bool) : Word :=
  if x = t then eventNode t split else passingNode x t split

theorem passingDigit_ne_one (x t : Word) : passingDigit x t ≠ .one := by
  unfold passingDigit
  split <;> decide

theorem sampleTail_binary (x t : Word) : .one ∉ sampleTail x t := by
  by_cases h : x = t
  · simp [sampleTail, h]
  · simp [sampleTail, h, Ne.symm (passingDigit_ne_one x t)]

theorem liftedNode_inTree (x t : Word) (split : Bool) :
    InTree (liftedNode x t split) := by
  by_cases h : x = t
  · rw [liftedNode, if_pos h]
    cases split
    · exact H_inTree _
    · exact U_inTree _
  · rw [liftedNode, if_neg h]
    exact passingNode_inTree _ _ _

theorem liftedNode_length {x t : Word} (h : x.length = t.length) (split : Bool) :
    (liftedNode x t split).length = eventLength t split := by
  by_cases heq : x = t
  · rw [liftedNode, if_pos heq, eventNode_length]
  · rw [liftedNode, if_neg heq, passingNode_length h]

theorem liftedNode_prefix_sample (x t : Word) (split : Bool) :
    (liftedNode x t split).IsPrefix (H (x ++ sampleTail x t)) := by
  by_cases heq : x = t
  · subst x
    cases split
    · simpa [liftedNode, sampleTail, eventNode] using (List.prefix_rfl : (H t).IsPrefix (H t))
    · simpa [liftedNode, sampleTail, eventNode] using U_prefix_H t
  · simp only [liftedNode, sampleTail, if_neg heq, passingNode]
    exact List.take_prefix _ _

/-- Truncating the endpoint of an edge after its initial digit preserves
that digit and does not create a 1 in binary padding. -/
theorem trim_edge {s v p : Word} {a : TernaryLetter}
    (hp : v.IsPrefix (s ++ a :: p)) (hl : s.length < v.length) :
    ∃ q : Word, v = s ++ a :: q ∧ (.one ∉ p → .one ∉ q) := by
  have hbase : (s ++ [a]).IsPrefix (s ++ a :: p) := ⟨p, by simp⟩
  have hpre := List.prefix_of_prefix_length_le hbase hp (by simp; omega)
  obtain ⟨q, hq⟩ := hpre
  obtain ⟨r, hr⟩ := hp
  have hq' : v = s ++ a :: q := by simpa using hq.symm
  have heq : s ++ a :: (q ++ r) = s ++ a :: p := by
    calc
      s ++ a :: (q ++ r) = (s ++ a :: q) ++ r := by simp [List.append_assoc]
      _ = s ++ a :: p := by rw [← hq', hr]
  have ht : q ++ r = p := (List.cons.inj (List.append_cancel_left heq)).2
  exact ⟨q, hq', fun h hm => h (ht ▸ List.mem_append_left _ hm)⟩

theorem activeEdge (t : Word) (a : TernaryLetter) (v : Word) (split : Bool)
    (ha : if split then a ≠ .one else a = .one) :
    ∃ p : Word, H (t ++ a :: v) = eventNode t split ++ a :: p ∧
      (a ≠ .one → .one ∉ v → .one ∉ p) := by
  obtain ⟨b, hb, hbin⟩ := H_branch t a v
  cases split with
  | false =>
    have heq : a = .one := by simpa using ha
    subst a
    refine ⟨b, ?_, fun h => (h rfl).elim⟩
    simpa [eventNode, H_eq_U, slotSuffix, List.append_assoc] using hb
  | true =>
    have hne : a ≠ .one := by simpa using ha
    cases a with
    | zero =>
      refine ⟨[.zero, .zero] ++ b, ?_, ?_⟩
      · simpa [eventNode, slotSuffix, List.append_assoc] using hb
      · intro _ h
        simp [hbin h]
    | one => exact (hne rfl).elim
    | two =>
      refine ⟨[.two, .two] ++ b, ?_, ?_⟩
      · simpa [eventNode, slotSuffix, List.append_assoc] using hb
      · intro _ h
        simp [hbin h]

/-- The local edge statement for the literal lift formula. Both active and
waiting vertices use the same sampling convention at the child level. -/
theorem liftedNode_step {x t y z v : Word} {a : TernaryLetter}
    (hx : x.length = t.length) (hy : y.length = z.length)
    (hform : y = x ++ a :: v) (hbin : a ≠ .one → .one ∉ v)
    (split split' : Bool)
    (hactive : x = t → if split then a ≠ .one else a = .one)
    (hpass : x ≠ t → a = passingDigit x t) :
    ∃ p : Word, liftedNode y z split' = liftedNode x t split ++ a :: p ∧
      (a ≠ .one → .one ∉ p) := by
  let tail := v ++ sampleTail y z
  have htail (ha : a ≠ .one) : .one ∉ tail := by
    simp [tail, hbin ha, sampleTail_binary]
  have heq : y ++ sampleTail y z = x ++ a :: tail := by
    simp [hform, tail, List.append_assoc]
  have hlen : t.length < z.length := by
    rw [← hx, ← hy, hform]
    simp
  have hl : (liftedNode x t split).length < (liftedNode y z split').length := by
    rw [liftedNode_length hx, liftedNode_length hy]
    exact eventLength_strict_of_depth hlen split split'
  have hfull : ∃ q : Word,
      H (y ++ sampleTail y z) = liftedNode x t split ++ a :: q ∧
        (a ≠ .one → .one ∉ q) := by
    by_cases h : x = t
    · obtain ⟨q, hq, hb⟩ := activeEdge x a tail split (hactive h)
      refine ⟨q, ?_, fun hn => hb hn (htail hn)⟩
      rw [heq, liftedNode, if_pos h, ← h]
      exact hq
    · have ha := hpass h
      have hne : a ≠ .one := ha ▸ passingDigit_ne_one x t
      obtain ⟨q, hq, h'⟩ := passingEdge_binary hx h split tail (htail hne)
      refine ⟨q, ?_, fun _ => hq⟩
      rw [heq, liftedNode, if_neg h, ha]
      simpa only [List.append_assoc, List.singleton_append] using h'
  obtain ⟨q, hq, hb⟩ := hfull
  have hpre := liftedNode_prefix_sample y z split'
  rw [hq] at hpre
  obtain ⟨p, hp, hpbin⟩ := trim_edge hpre hl
  exact ⟨p, hp, fun ha => hpbin (hb ha)⟩

end AllThoseBigRamsey.Pseudotree.Sparse.FIFO
