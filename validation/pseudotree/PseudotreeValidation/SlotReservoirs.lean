import PseudotreeValidation.FIFOBoundary
import PseudotreeValidation.SparseRecurrence
import PseudotreeValidation.CriticalSupport

/-! Rational reservoirs in the live slots. A pair of comparable code
descendants suffices: the interval between them is rational and remains
in the same binary cylinder. No full queue-ray isomorphism is needed
for this initialization. -/
namespace AllThoseBigRamsey.Pseudotree
open LowerGeometry RayEmbeddings RayMapModel

private theorem binary_letters_exists (b : Sparse.Word) (hb : .one ∉ b) :
    ∃ v : List Bool, v.map binaryLetter = b := by
  induction b with
  | nil => exact ⟨[],rfl⟩
  | cons a b ih =>
    obtain ⟨v,hv⟩ := ih (fun h => hb (List.mem_cons_of_mem _ h))
    cases a with
    | zero => exact ⟨false::v,by simp [binaryLetter,hv]⟩
    | one => exact False.elim (hb (by simp))
    | two => exact ⟨true::v,by simp [binaryLetter,hv]⟩

private theorem binary_letters_noOne (b : List Bool) :
    .one ∉ b.map binaryLetter := by
  intro h
  obtain ⟨a,_,ha⟩ := List.mem_map.mp h
  cases a <;> simp [binaryLetter] at ha

/-- A literal binary continuation is on the ray of its initial word. -/
theorem stem_binary_append (w b : Sparse.Word) (hb : .one ∉ b) :
    RayTree.rayStem (toBlocks (w ++ b)) = RayTree.rayStem (toBlocks w) := by
  obtain ⟨v,rfl⟩ := binary_letters_exists b hb
  let x := toBlocks w
  let stem := RayTree.rayStem x
  let a := RayTree.rayValue x
  have hx : RayTree.onRay stem a = x := RayTree.onRay_stem_value x
  have hw : w = rayRoot stem ++ a.word.map binaryLetter := by
    rw [← fromBlocks_toBlocks w]
    change fromBlocks x = _
    rw [← hx,fromBlocks_onRay]
  have he : w ++ v.map binaryLetter =
      fromBlocks (RayTree.onRay stem ⟨a.word ++ v⟩) := by
    rw [hw,fromBlocks_onRay]
    simp only [List.map_append,List.append_assoc]
  rw [he,toBlocks_fromBlocks,RayTree.rayStem_onRay]

/-- Two endpoints in a binary cylinder have their entire order interval
in that cylinder, not merely in the larger ternary cone. -/
theorem binary_cylinder_convex {w b c : Sparse.Word} {z : TernaryModel}
    (hb : .one ∉ b) (hc : .one ∉ c)
    (hlo : toBlocks (w ++ b) ≤ z) (hhi : z ≤ toBlocks (w ++ c)) :
    ∃ d : Sparse.Word, .one ∉ d ∧ fromBlocks z = w ++ d := by
  obtain ⟨bs,rfl⟩ := binary_letters_exists b hb
  obtain ⟨cs,rfl⟩ := binary_letters_exists c hc
  let x := toBlocks w
  let stem := RayTree.rayStem x
  let a := RayTree.rayValue x
  have hx : RayTree.onRay stem a = x := RayTree.onRay_stem_value x
  have hw : w = rayRoot stem ++ a.word.map binaryLetter := by
    rw [← fromBlocks_toBlocks w]
    change fromBlocks x = _
    rw [← hx,fromBlocks_onRay]
  have hends (v : List Bool) : toBlocks (w ++ v.map binaryLetter) =
      RayTree.onRay stem ⟨a.word ++ v⟩ := by
    apply wordEquiv.symm.injective
    change fromBlocks (toBlocks (w ++ v.map binaryLetter)) =
      fromBlocks (RayTree.onRay stem ⟨a.word ++ v⟩)
    rw [fromBlocks_toBlocks,hw,fromBlocks_onRay]
    simp only [List.map_append,List.append_assoc]
  rw [hends bs] at hlo
  rw [hends cs] at hhi
  have h₁ := RayTree.stem_length_mono hlo
  have h₂ := RayTree.stem_length_mono hhi
  simp only [RayTree.rayStem_onRay] at h₁ h₂
  have hstem : RayTree.rayStem z = stem := by
    have he := RayTree.stem_eq_of_le_of_length_eq hlo (by
      rw [RayTree.rayStem_onRay]; exact le_antisymm h₁ h₂)
    simpa only [RayTree.rayStem_onRay] using he.symm
  let v := RayTree.rayValue z
  have hz : RayTree.onRay stem v = z := by
    rw [← hstem]
    exact RayTree.onRay_stem_value z
  rw [← hz,RayTree.onRay_le_iff] at hlo hhi
  have hlo' : binaryLE (a.word ++ bs) v.word = true := hlo
  have hhi' : binaryLE v.word (a.word ++ cs) = true := hhi
  obtain ⟨tail,htail⟩ := binary_prefix_of_between a.word bs cs v.word hlo' hhi'
  refine ⟨tail.map binaryLetter,binary_letters_noOne tail,?_⟩
  rw [← hz,fromBlocks_onRay,← htail,List.map_append,← List.append_assoc,← hw]

namespace Sparse.FIFO

/-- The rational reservoir in each actual live queue slot. -/
theorem slot_rayCopy (d : Nat) (w : Sparse.Word) (hw : Sparse.InTree w)
    (hlen : w.length = 3*d) :
    ∃ Q : RayCopy,
      (∀ q, Sparse.InSparse (fromBlocks (Q q))) ∧
      ∀ q, ∃ b : Sparse.Word, .one ∉ b ∧ fromBlocks (Q q) = w ++ b := by
  obtain ⟨t,b,hb,hU⟩ := slot_has_label d w hw hlen
  obtain ⟨s,hs,hsbin⟩ := H_slot_descendant hU hb []
  obtain ⟨v,hv,hvbin⟩ := H_slot_descendant hU hb [TernaryLetter.zero]
  have hs' : H t = w ++ s := by simpa using hs
  have hv' : H (t ++ [.zero]) = w ++ v := hv
  have hsno := hsbin (by simp)
  have hvno := hvbin (by simp)
  let y := SparseModel.ofWord (H t) (H_inSparse t)
  let z := SparseModel.ofWord (H (t ++ [.zero])) (H_inSparse _)
  have hyz : y < z := by
    have hp := Sparse.code_upper_child (labelStage t)
    have he : H (t ++ [.zero]) = Sparse.code (3*labelStage t+1) := by simp [H,rank]
    apply lt_iff_le_not_ge.mpr
    refine ⟨(SparseModel.word_le_iff y z).mp ?_,?_⟩
    · simpa only [y,z,SparseModel.word_ofWord,H, labelStage_snoc,rank,Nat.add_zero] using hp.1
    · intro h
      apply hp.2
      simpa only [y,z,SparseModel.word_ofWord,H,labelStage_snoc,rank,Nat.add_zero] using
        (SparseModel.word_le_iff z y).mpr h
  letI := intervalLinearOrder SparseModel.predecessors_comparable y z
  obtain ⟨e⟩ := interval_orderIso_rat SparseModel.predecessors_comparable hyz
  let E : ℚ ↪o SparseModel := e.toOrderEmbedding.trans (OrderEmbedding.subtype _)
  let F : ℚ ↪o TernaryModel := E.trans (OrderEmbedding.subtype _)
  have hwords (q : ℚ) : ∃ p : Sparse.Word, .one ∉ p ∧ fromBlocks (F q) = w ++ p := by
    apply binary_cylinder_convex hsno hvno
    · rw [← hs']
      exact (e q).property.1.le
    · rw [← hv']
      exact (e q).property.2.le
  let Q : RayCopy := ⟨F,RayTree.rayStem (toBlocks w),fun q => by
    obtain ⟨p,hp,he⟩ := hwords q
    have h := congrArg toBlocks he
    rw [toBlocks_fromBlocks] at h
    rw [h,stem_binary_append w p hp]⟩
  exact ⟨Q,fun q => (E q).property,hwords⟩

end Sparse.FIFO

namespace LowerGeometry.RayCopy

/-- Transport a rational reservoir under a ray-preserving map. It lies
on a single ray because all its words have binary tails after w. -/
theorem mapped_slot (Q : RayCopy) (f : RayStrongMap) (w : Word)
    (hw : ∀ q, ∃ b : Word, Binary b ∧ fromBlocks (Q q) = (w ++ b).map toLetter) :
    ∃ R : RayCopy,
      (∀ q, R q = RayMapModel.embedding f (Q q)) ∧
      ∀ q, ∃ b : Word, Binary b ∧ fromBlocks (R q) = (f.map w ++ b).map toLetter := by
  let E := Q.embedding.trans (embeddingOrderEmbedding (RayMapModel.embedding f))
  have htail (q : ℚ) : ∃ b : Word, Binary b ∧
      fromBlocks (E q) = (f.map w ++ b).map toLetter := by
    obtain ⟨b,hb,hword⟩ := hw q
    obtain ⟨p,hp,he⟩ := f.maps_binary_ray w b hb
    refine ⟨p,hp,?_⟩
    change fromBlocks (RayMapModel.embedding f (Q q)) = _
    rw [show Q q = toBlocks (fromBlocks (Q q)) from (toBlocks_fromBlocks _).symm,
      RayMapModel.embedding_apply_word,fromBlocks_toBlocks,hword]
    simp [act,List.map_map,Function.comp_def,he]
  let R : RayCopy := ⟨E,RayTree.rayStem (toBlocks ((f.map w).map toLetter)),fun q => by
    obtain ⟨b,hb,he⟩ := htail q
    have hb' : TernaryLetter.one ∉ b.map toLetter :=
      fun hm => ((noOne_map b).mpr hb) _ hm rfl
    rw [List.map_append] at he
    have he' := congrArg toBlocks he
    rw [toBlocks_fromBlocks] at he'
    rw [he',stem_binary_append _ _ hb']⟩
  exact ⟨R,fun _ => rfl,htail⟩

end LowerGeometry.RayCopy
end AllThoseBigRamsey.Pseudotree
