import PseudotreeValidation.LowerSplit
import PseudotreeValidation.LowerTurn
import PseudotreeValidation.SparseLex

/-! Shared geometric facts extracted from the old finite-chain realization
proof. The transition and iteration are now in ChartReservoir. -/
namespace AllThoseBigRamsey.Pseudotree.LowerRealization
open LowerGeometry
open scoped FirstOrder

private theorem binary_no_one (s : List Bool) : TernaryLetter.one ∉ s.map binaryLetter := by
  intro h
  obtain ⟨b, _, hb⟩ := List.mem_map.mp h
  cases b <;> simp [binaryLetter] at hb

/-- Beyond its ray root, every prefix of a ray point leaves only binary
letters to the point. -/
theorem ray_prefix_binary (Q : RayCopy) (p : List TernaryLetter) (q : ℚ)
    (hroot : (rayRoot Q.stem).length ≤ p.length)
    (hp : p <+: fromBlocks (Q q)) :
    ∃ b : List TernaryLetter, .one ∉ b ∧ fromBlocks (Q q) = p ++ b := by
  have hprefix := hp
  obtain ⟨b, hb⟩ := hp
  have hr : rayRoot Q.stem <+: p := List.prefix_of_prefix_length_le
    (by rw [Q.fromBlocks_eq]; exact List.prefix_append _ _) hprefix hroot
  obtain ⟨a, ha⟩ := hr
  have heq : a ++ b = (Q.coordinates q).word.map binaryLetter := by
    rw [← ha, Q.fromBlocks_eq, List.append_assoc] at hb
    exact List.append_cancel_left hb
  refine ⟨b, ?_, hb.symm⟩
  intro h
  have hnot := binary_no_one (Q.coordinates q).word
  apply hnot
  rw [← heq]
  exact List.mem_append_right a h

/-- A prefix of a binary extension is itself a binary extension. -/
theorem binary_prefix_between {p v w : List TernaryLetter}
    (hpv : p <+: v) (hvw : v <+: w)
    (hw : ∃ b : List TernaryLetter, .one ∉ b ∧ w = p ++ b) :
    ∃ b : List TernaryLetter, .one ∉ b ∧ v = p ++ b := by
  obtain ⟨b, hb⟩ := hpv
  obtain ⟨c, hc, rfl⟩ := hw
  have hbc : b <+: c := by
    rw [← hb] at hvw
    exact (List.prefix_append_right_inj p).mp hvw
  exact ⟨b, fun h => hc (hbc.subset h), hb.symm⟩

theorem inTree_of_sparse {w : List TernaryLetter} (hw : Sparse.InSparse w) :
    Sparse.InTree w := by
  obtain ⟨n, rfl⟩ := (Sparse.inSparse_iff_code w).mp hw
  exact ⟨n, List.prefix_refl _⟩

/-- Two occupied children locate the actual critical fork, rather than an
abstract branching point. -/
theorem fork_critical {v : List TernaryLetter}
    (h0 : Sparse.InTree (v ++ [.zero])) (h2 : Sparse.InTree (v ++ [.two])) :
    v = Sparse.critical v.length := by
  have hv := Sparse.inTree_prefix h0 (List.prefix_append _ _)
  have hc0 := (Sparse.critical_children v.length v hv rfl .zero).mp h0
  have hc2 := (Sparse.critical_children v.length v hv rfl .two).mp h2
  by_cases h : v = Sparse.critical v.length
  · exact h
  · simp only [Sparse.CriticalChildren, h, ↓reduceIte] at hc0 hc2
    have hbad := hc0.trans hc2.symm
    contradiction

theorem finite_common_prefix {I : Type} [Fintype I] (Q : I → RayCopy) (k : Nat) :
    ∃ L : Nat, k < L ∧ ∃ R : I → RayCopy, ∃ p : I → List TernaryLetter,
      (∀ i, (R i).stem = (Q i).stem) ∧
      (∀ i, Set.range (R i).embedding ⊆ Set.range (Q i).embedding) ∧
      (∀ i, (p i).length = L) ∧
      (∀ i q, p i <+: fromBlocks (R i q)) ∧
      (∀ i, (rayRoot (R i).stem).length < L) := by
  classical
  let L := k + 1 + Finset.univ.sup (fun i : I => (rayRoot (Q i).stem).length)
  have hroot (i : I) : (rayRoot (Q i).stem).length < L := by
    have hle := Finset.le_sup (s := Finset.univ)
      (f := fun i : I => (rayRoot (Q i).stem).length) (Finset.mem_univ i)
    omega
  have hchoice : ∀ i : I, ∃ R : RayCopy, R.stem = (Q i).stem ∧
      Set.range R.embedding ⊆ Set.range (Q i).embedding ∧
      ∃ p : List TernaryLetter, p.length = L ∧ ∀ q, p <+: fromBlocks (R q) :=
    fun i => (Q i).common_prefix L (hroot i).le
  choose R hstem hsub p hlen hp using hchoice
  exact ⟨L, by omega, R, p, hstem, hsub, hlen, hp, fun i => by rw [hstem]; exact hroot i⟩


end AllThoseBigRamsey.Pseudotree.LowerRealization
