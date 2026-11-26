import PseudotreeValidation.RevisedSparseModel
import PseudotreeValidation.SlotReservoirs

/-! The only order-sensitive input to the reservoir construction is
the chart from the ambient meet-tree to literal words. A chart fixes
the sparse queue and its lexicographic passing rule. Its ray
operations take place in the actual ambient order, not in the order
of queue labels. -/
namespace AllThoseBigRamsey.Pseudotree
open LowerGeometry
open scoped FirstOrder

structure ReservoirChart where
  decode : TernaryModel → Sparse.Word
  encode : Sparse.Word → TernaryModel
  encode_decode : ∀ z, encode (decode z) = z
  decode_encode : ∀ w, decode (encode w) = w
  ray_prefix_binary : ∀ (Q : RayCopy) (p : Sparse.Word) (q : ℚ),
    (rayRoot Q.stem).length ≤ p.length → p.IsPrefix (decode (Q q)) →
      ∃ b : Sparse.Word, .one ∉ b ∧ decode (Q q) = p ++ b
  common_prefix : ∀ (Q : RayCopy) (L : Nat), (rayRoot Q.stem).length ≤ L →
    ∃ R : RayCopy, R.stem = Q.stem ∧ Set.range R.embedding ⊆ Set.range Q.embedding ∧
      ∃ p : Sparse.Word, p.length = L ∧ ∀ q, p.IsPrefix (decode (R q))
  sparse_split : ∀ (Q : RayCopy),
    (∀ q, Sparse.InSparse (decode (Q q))) →
    ∀ p : Sparse.Word, (∀ q, p.IsPrefix (decode (Q q))) →
      (rayRoot Q.stem).length ≤ p.length →
      ∃ v : Sparse.Word, ∃ Q0 Q2 : RayCopy,
        p.IsPrefix v ∧ Q0.stem = Q.stem ∧ Q2.stem = Q.stem ∧
        Set.range Q0.embedding ⊆ Set.range Q.embedding ∧
        Set.range Q2.embedding ⊆ Set.range Q.embedding ∧
        (∀ q, ∃ b : Sparse.Word, .one ∉ b ∧ decode (Q0 q) = v ++ .zero :: b) ∧
        (∀ q, ∃ b : Sparse.Word, .one ∉ b ∧ decode (Q2 q) = v ++ .two :: b)
  opposite_continuation : ∀ (Q : RayCopy) (f : TernaryModel ↪[language] TernaryModel),
    Set.range Q.embedding ⊆ Set.range f → ∀ q : ℚ,
      ∃ R : RayCopy, Set.range R.embedding ⊆ Set.range f ∧
        ∀ t, Q q < R t ∧ (decode (Q q) ++ [.one]).IsPrefix (decode (R t))

def ReservoirChart.original : ReservoirChart where
  decode := fromBlocks
  encode := toBlocks
  encode_decode := toBlocks_fromBlocks
  decode_encode := fromBlocks_toBlocks
  ray_prefix_binary := LowerRealization.ray_prefix_binary
  common_prefix := RayCopy.common_prefix
  sparse_split := RayCopy.sparse_split
  opposite_continuation := RayCopy.opposite_continuation

namespace RevisedConvention

@[simp] theorem mirror_singleton (a : TernaryLetter) :
    mirror [a] = [mirrorLetter a] := rfl

@[simp] theorem mirror_cons (a : TernaryLetter) (s : Sparse.Word) :
    mirror (a::s) = mirrorLetter a :: mirror s := rfl

@[simp] theorem mirrorLetter_one_iff (a : TernaryLetter) :
    mirrorLetter a = .one ↔ a = .one := by cases a <;> decide

theorem mirror_prefix {s t : Sparse.Word} (h : s.IsPrefix t) :
    (mirror s).IsPrefix (mirror t) :=
  h.map mirrorLetter

theorem mirror_prefix_iff (s t : Sparse.Word) :
    (mirror s).IsPrefix (mirror t) ↔ s.IsPrefix t :=
  ⟨fun h => by simpa only [mirror_twice] using mirror_prefix h,mirror_prefix⟩

theorem mirror_binary {s : Sparse.Word} (h : .one ∉ s) :
    .one ∉ mirror s := by
  intro hm
  obtain ⟨a,ha,he⟩ := List.mem_map.mp hm
  exact h ((mirrorLetter_one_iff a).mp he ▸ ha)

theorem revised_ray_prefix_binary (Q : RayCopy) (p : Sparse.Word) (q : ℚ)
    (hr : (rayRoot Q.stem).length ≤ p.length)
    (hp : p.IsPrefix (revisedFromBlocks (Q q))) :
    ∃ b : Sparse.Word, .one ∉ b ∧ revisedFromBlocks (Q q) = p ++ b := by
  have hp' : (mirror p).IsPrefix (fromBlocks (Q q)) := by
    simpa only [revisedFromBlocks,mirror_twice] using mirror_prefix hp
  obtain ⟨b,hb,he⟩ := LowerRealization.ray_prefix_binary Q (mirror p) q
    (by simpa only [mirror_length] using hr) hp'
  refine ⟨mirror b,mirror_binary hb,?_⟩
  simpa only [revisedFromBlocks,mirror_append,mirror_twice] using congrArg mirror he

theorem revised_common_prefix (Q : RayCopy) (L : Nat)
    (hL : (rayRoot Q.stem).length ≤ L) :
    ∃ R : RayCopy, R.stem = Q.stem ∧ Set.range R.embedding ⊆ Set.range Q.embedding ∧
      ∃ p : Sparse.Word, p.length = L ∧ ∀ q, p.IsPrefix (revisedFromBlocks (R q)) := by
  obtain ⟨R,hstem,hsub,p,hplen,hp⟩ := Q.common_prefix L hL
  exact ⟨R,hstem,hsub,mirror p,by simpa only [mirror_length] using hplen,
    fun q => mirror_prefix (hp q)⟩

/-- Every literal sparse code followed by another on the same ambient
ray is prefix-incomparable, also after reflecting the coordinate
alphabet. This is exactly the only sparse-specific input to splitting. -/
theorem reflected_prefix_antichain (Q : RayCopy)
    (hs : ∀ q, Sparse.InSparse (revisedFromBlocks (Q q)))
    {a b : ℚ} (hp : (fromBlocks (Q a)).IsPrefix (fromBlocks (Q b))) : a = b := by
  obtain ⟨n,hn⟩ := (Sparse.inSparse_iff_code _).mp (hs a)
  obtain ⟨m,hm⟩ := (Sparse.inSparse_iff_code _).mp (hs b)
  by_cases he : n = m
  · apply Q.embedding.injective
    apply revisedWordEquiv.symm.injective
    exact hn.trans (he ▸ hm.symm)
  · have hpre : (Sparse.code n).IsPrefix (Sparse.code m) := by
      rw [← hn,← hm]
      exact mirror_prefix hp
    have h1 := Sparse.code_prefix_one hpre he
    rw [← hn,← hm] at h1
    have h1' : (fromBlocks (Q a) ++ [TernaryLetter.one]).IsPrefix (fromBlocks (Q b)) := by
      simpa only [revisedFromBlocks,mirror_append,mirror_singleton,mirror_twice,mirrorLetter]
        using mirror_prefix h1
    have hlen : (rayRoot Q.stem).length ≤ (fromBlocks (Q a)).length := by
      rw [Q.fromBlocks_eq,List.length_append]
      omega
    obtain ⟨d,hd,heq⟩ := LowerRealization.ray_prefix_binary Q (fromBlocks (Q a)) b hlen hp
    rw [heq] at h1'
    exact False.elim (hd (((List.prefix_append_right_inj _).mp h1').subset (by simp)))

/-- The same geometric split with the two binary output cones
exchanged. No change to literal queue positions or passing digits. -/
theorem revised_sparse_split (Q : RayCopy)
    (hs : ∀ q, Sparse.InSparse (revisedFromBlocks (Q q))) (p : Sparse.Word)
    (hp : ∀ q, p.IsPrefix (revisedFromBlocks (Q q)))
    (hr : (rayRoot Q.stem).length ≤ p.length) :
    ∃ v : Sparse.Word, ∃ Q0 Q2 : RayCopy,
      p.IsPrefix v ∧ Q0.stem = Q.stem ∧ Q2.stem = Q.stem ∧
      Set.range Q0.embedding ⊆ Set.range Q.embedding ∧
      Set.range Q2.embedding ⊆ Set.range Q.embedding ∧
      (∀ q, ∃ b : Sparse.Word, .one ∉ b ∧ revisedFromBlocks (Q0 q) = v ++ .zero :: b) ∧
      (∀ q, ∃ b : Sparse.Word, .one ∉ b ∧ revisedFromBlocks (Q2 q) = v ++ .two :: b) := by
  have hp' (q : ℚ) : (mirror p).IsPrefix (fromBlocks (Q q)) := by
    simpa only [revisedFromBlocks,mirror_twice] using mirror_prefix (hp q)
  obtain ⟨v,Q0,Q2,hv,h0stem,h2stem,h0range,h2range,h0,h2⟩ :=
    Q.split_of_prefix_antichain (fun h => reflected_prefix_antichain Q hs h)
      (mirror p) hp' (by simpa only [mirror_length] using hr)
  refine ⟨mirror v,Q2,Q0,?_,h2stem,h0stem,h2range,h0range,?_,?_⟩
  · simpa only [mirror_twice] using mirror_prefix hv
  · intro q
    obtain ⟨b,hb,he⟩ := h2 q
    exact ⟨mirror b,mirror_binary hb,by
      simpa only [revisedFromBlocks,mirror_append,mirror_cons,mirrorLetter] using congrArg mirror he⟩
  · intro q
    obtain ⟨b,hb,he⟩ := h0 q
    exact ⟨mirror b,mirror_binary hb,by
      simpa only [revisedFromBlocks,mirror_append,mirror_cons,mirrorLetter] using congrArg mirror he⟩

theorem revised_opposite_continuation (Q : RayCopy)
    (f : TernaryModel ↪[language] TernaryModel)
    (hQ : Set.range Q.embedding ⊆ Set.range f) (q : ℚ) :
    ∃ R : RayCopy, Set.range R.embedding ⊆ Set.range f ∧
      ∀ t, Q q < R t ∧
        (revisedFromBlocks (Q q) ++ [TernaryLetter.one]).IsPrefix (revisedFromBlocks (R t)) := by
  obtain ⟨R,hR,h⟩ := Q.opposite_continuation f hQ q
  refine ⟨R,hR,fun t => ⟨(h t).1,?_⟩⟩
  simpa only [revisedFromBlocks,mirror_append,mirror_singleton,mirrorLetter] using mirror_prefix (h t).2

/-- Literal revised chart, with all ray geometry discharged. -/
def revisedChart : ReservoirChart where
  decode := revisedFromBlocks
  encode := revisedToBlocks
  encode_decode := revisedToBlocks_revisedFromBlocks
  decode_encode := revisedFromBlocks_revisedToBlocks
  ray_prefix_binary := revised_ray_prefix_binary
  common_prefix := revised_common_prefix
  sparse_split := revised_sparse_split
  opposite_continuation := revised_opposite_continuation

end RevisedConvention
end AllThoseBigRamsey.Pseudotree
