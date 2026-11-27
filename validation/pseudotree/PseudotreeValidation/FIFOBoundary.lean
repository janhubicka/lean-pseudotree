import PseudotreeValidation.FIFOEdges
import PseudotreeValidation.ReservoirGeometry

/-! A live queue slot admits a label cone, and finitely many such cones
can be synchronized at one label length. The proof uses the existing
exact FIFO schedule, without an extra queue-labelling invariant. -/
namespace AllThoseBigRamsey.Pseudotree.Sparse.FIFO

open LowerRealization (binary_prefix_between)

/-- All labels of the same depth carry the literal lexicographic order
to their serialized coding points. -/
theorem H_lex_sameLength {x y : Word} (hlen : x.length = y.length) :
    lexLess (H x) (H y) = lexLess x y := by
  by_cases heq : x = y
  · subst y
    simp
  · obtain ⟨p,a,b,s,t,hx,hy,hab⟩ := equal_length_split hlen heq
    rw [hx,hy]
    exact code_branches_lex p a b hab s t

/-- Every active queue slot is a binary prefix of the head of its
eventual processing stage, expressed in label coordinates. -/
theorem slot_has_label (d : Nat) (w : Word)
    (hw : InTree w) (hlen : w.length = 3*d) :
    ∃ t b : Word, .one ∉ b ∧ U t = w ++ b := by
  have hactive := (inTree_stage_level d w hlen).mp hw
  obtain ⟨m,hdm,_,b,hb,hcode⟩ := every_active_binary_coded d w hactive
  obtain ⟨t,ht⟩ := labelStage_surjective m
  have hc : H t = w ++ b := by rw [H,ht,hcode]
  have hpre : w.IsPrefix (H t) := ⟨b,hc.symm⟩
  have hU : w.IsPrefix (U t) := List.prefix_of_prefix_length_le
    hpre (U_prefix_H t) (by rw [hlen,U_length,ht]; omega)
  obtain ⟨c,hcbin,heq⟩ := binary_prefix_between hU (U_prefix_H t) ⟨b,hb,hc⟩
  exact ⟨t,c,hcbin,heq⟩

/-- All descendants of a chosen label cone stay in its original slot.
A binary suffix stays on the original ray. -/
theorem U_slot_descendant {w t b : Word}
    (hU : U t = w ++ b) (hb : .one ∉ b) (z : Word) :
    ∃ v : Word, U (t ++ z) = w ++ v ∧ (.one ∉ z → .one ∉ v) := by
  obtain ⟨p,hp,hpb⟩ := U_descendant t z
  exact ⟨b ++ p,by rw [hp,hU,List.append_assoc],
    fun hz => by simp [hb,hpb hz]⟩

theorem H_slot_descendant {w t b : Word}
    (hU : U t = w ++ b) (hb : .one ∉ b) (z : Word) :
    ∃ v : Word, H (t ++ z) = w ++ v ∧ (.one ∉ z → .one ∉ v) := by
  obtain ⟨p,hp,hpb⟩ := H_descendant t z
  exact ⟨b ++ p,by rw [hp,hU,List.append_assoc],
    fun hz => by simp [hb,hpb hz]⟩

/-- Pad a finite family of label roots to the same depth using only
binary digits. This preserves the prescribed geometric slots. -/
theorem synchronized_slot_labels {I : Type} [Fintype I] (d : Nat)
    (w : I → Word) (hw : ∀ i, InTree (w i)) (hl : ∀ i, (w i).length = 3*d) :
    ∃ k : Nat, ∃ p : I → Word,
      (∀ i, (p i).length = k) ∧
      ∀ i, ∃ b : Word, .one ∉ b ∧ U (p i) = w i ++ b := by
  classical
  choose t b hb ht using fun i => slot_has_label d (w i) (hw i) (hl i)
  let k := Finset.univ.sup (fun i => (t i).length)
  have hk (i : I) : (t i).length ≤ k :=
    Finset.le_sup (s := Finset.univ) (f := fun i => (t i).length) (Finset.mem_univ i)
  let p (i : I) := t i ++ List.replicate (k - (t i).length) TernaryLetter.zero
  refine ⟨k,p,?_,?_⟩
  · intro i
    simp only [p,List.length_append,List.length_replicate]
    exact Nat.add_sub_of_le (hk i)
  · intro i
    obtain ⟨v,hv,hvbin⟩ := U_slot_descendant (ht i) (hb i)
      (List.replicate (k - (t i).length) TernaryLetter.zero)
    exact ⟨v,hvbin (by simp),hv⟩

/-- Once the slot roots have equal length, their lexicographic order
reflects back to any synchronized labels whose heads extend them. -/
theorem slot_label_lex {w v x y : Word}
    (hlen : w.length = v.length) (hne : w ≠ v)
    (hxy : x.length = y.length)
    (hx : w.IsPrefix (U x)) (hy : v.IsPrefix (U y)) :
    lexLess x y = lexLess w v := by
  have hH := H_lex_sameLength hxy
  obtain ⟨s,hs⟩ := hx.trans (U_prefix_H x)
  obtain ⟨t,ht⟩ := hy.trans (U_prefix_H y)
  rw [← hs,← ht,lexLess_append_of_ne hlen hne] at hH
  exact hH.symm

/-- At the incoming boundary, a label with head in a prescribed slot
gives a sample of that slot. The retained level may be far beyond
the slot; binary padding remains binary. -/
theorem sample_in_slot {w x b : Word}
    (hx : U x = w ++ b) (hb : .one ∉ b) (t : Word) :
    ∃ v : Word, .one ∉ v ∧ H (x ++ sampleTail x t) = w ++ v := by
  obtain ⟨v,hv,hbin⟩ := H_slot_descendant hx hb (sampleTail x t)
  exact ⟨v,hbin (sampleTail_binary x t),hv⟩

end AllThoseBigRamsey.Pseudotree.Sparse.FIFO
