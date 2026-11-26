import PseudotreeValidation.CriticalPullback

/-! The depth of a whole-gadget approximation is witnessed by its final
coding level. This verifies the strict version of A.2(3) used in the
manuscript, rather than merely the non-strict upstream interface. -/
namespace AllThoseBigRamsey.Pseudotree.CriticalCopies
open RayEmbeddings
open SparseNormalization (critical critical_length)

theorem image_length_le_top (X : CriticalMap) {n : Nat} (hn : 0 < n)
    (u : Prefix n) :
    (X.map u.val).length ≤ X.level (3*n-1) := by
  rw [← level_eq_length X u.val]
  apply X.level_strict.monotone
  have h := u.property
  omega

theorem top_mem (X : CriticalMap) {n : Nat} (hn : 0 < n) :
    X.map (criticalNode (3*n-1)) ∈ finiteRange (system.finiteApprox n X) := by
  change X.map (criticalNode (3*n-1)) ∈ Set.range (restriction n X)
  exact ⟨⟨criticalNode (3*n-1),by simp; omega⟩,rfl⟩

theorem prefix_zero_empty (X : CriticalMap) :
    finiteRange (system.finiteApprox 0 X) = ∅ := by
  ext w
  constructor
  · rintro ⟨u,_⟩
    have h := u.property
    change u.val.val.length < 3*0 at h
    omega
  · intro h
    exact False.elim h

/-- Nonempty finite approximations have a nonzero depth, whose top
coding level is exactly the final coding level of the approximation. -/
theorem depth_top (X Y : CriticalMap) {n d : Nat} (hn : 0 < n)
    (hd : finitization.HasDepth (approx n X) Y d) :
    0 < d ∧ X.level (3*n-1) = Y.level (3*d-1) := by
  have hsub := hd.1
  change finiteRange (system.finiteApprox n X) ⊆
    finiteRange (system.finiteApprox d Y) at hsub
  obtain ⟨v,hv⟩ := hsub (top_mem X hn)
  let j := v.val.val.length
  have hj : j < 3*d := v.property
  have hdpos : 0 < d := by omega
  have hv' : Y.map v.val = X.map (criticalNode (3*n-1)) := hv
  have hl : Y.level j = X.level (3*n-1) :=
    (level_eq_length Y v.val).trans (congrArg List.length hv')
  have hphase : j % 3 = 2 := by
    apply (Y.phase j).mp
    change Y.level j % 3 = 2
    rw [hl]
    exact (X.phase (3*n-1)).mpr (by omega)
  have htop : j = 3*d-1 := by
    by_contra hne
    have hj' : j < 3*(d-1) := by omega
    have hsm : finiteRange (system.finiteApprox n X) ⊆
        finiteRange (system.finiteApprox (d-1) Y) := by
      change Set.range (restriction n X) ⊆ Set.range (restriction (d-1) Y)
      rintro w ⟨u,rfl⟩
      obtain ⟨z,hz⟩ := hsub (show X.map u.val ∈
        finiteRange (system.finiteApprox n X) from ⟨u,rfl⟩)
      have hz' : Y.map z.val = X.map u.val := hz
      have hle : z.val.val.length ≤ j := by
        apply Y.level_strict.le_iff_le.mp
        rw [level_eq_length Y z.val, hz', hl]
        exact image_length_le_top X hn u
      exact ⟨⟨z.val,by have := hle; omega⟩,hz'⟩
    exact (hd.2 (d-1) (by omega)) hsm
  exact ⟨hdpos,by rw [← htop]; exact hl.symm⟩

/-- Strict initial-segment version of the manuscript's A.2(3). -/
theorem strict_prefix_leFin {n m k : Nat}
    {a : system.Approx n} {b : system.Approx m} {c : system.Approx k}
    (hnm : n < m) (hab : system.IsInitial a b)
    (hbc : leFin ⟨m,b⟩ ⟨k,c⟩) :
    ∃ j < k, ∃ d : system.Approx j,
      system.IsInitial d c ∧ leFin ⟨n,a⟩ ⟨j,d⟩ := by
  obtain ⟨_,X,hXa,hXb⟩ := hab
  obtain ⟨Y,hYc⟩ := system.approx_surjective k c
  have haEq : system.finiteApprox n X = ⟨n,a⟩ := Sigma.ext rfl (heq_of_eq hXa)
  have hbEq : system.finiteApprox m X = ⟨m,b⟩ := Sigma.ext rfl (heq_of_eq hXb)
  have hcEq : system.finiteApprox k Y = ⟨k,c⟩ := Sigma.ext rfl (heq_of_eq hYc)
  have hsubB : finiteRange (system.finiteApprox m X) ⊆
      finiteRange (system.finiteApprox k Y) := by
    rw [hbEq,hcEq]
    exact hbc
  have hm : 0 < m := by omega
  obtain ⟨v,hv⟩ := hsubB (top_mem X hm)
  have hk : 0 < k := by
    have h := v.property
    change v.val.val.length < 3*k at h
    omega
  by_cases hn : n = 0
  · subst n
    refine ⟨0,hk,approx 0 Y,?_,?_⟩
    · rw [← hYc]
      exact system.isInitial_of_point (Nat.zero_le _) Y
    · change finiteRange (⟨0,a⟩ : system.FiniteApprox) ⊆
        finiteRange (system.finiteApprox 0 Y)
      rw [← haEq,prefix_zero_empty X]
      exact Set.empty_subset _
  · have hnpos : 0 < n := by omega
    have hsubA := (prefixRange_mono X hnm.le).trans hsubB
    obtain ⟨j,hj⟩ := (finitization.exists_hasDepth_iff (approx n X) Y).mpr ⟨k,hsubA⟩
    have hjk : j ≤ k := by
      by_contra h
      exact (hj.2 k (by omega)) hsubA
    have hjlt : j < k := by
      by_contra h
      have heq : j = k := by omega
      obtain ⟨_,hdepth⟩ := depth_top X Y hnpos hj
      have hstrict : X.level (3*n-1) < X.level (3*m-1) :=
        X.level_strict (by omega)
      have hv' : Y.map v.val = X.map (criticalNode (3*m-1)) := hv
      have hle : X.level (3*m-1) ≤ Y.level (3*k-1) := by
        change (X.map (criticalNode (3*m-1))).length ≤ _
        rw [← hv']
        exact image_length_le_top Y hk v
      rw [heq] at hdepth
      omega
    refine ⟨j,hjlt,approx j Y,?_,?_⟩
    · rw [← hYc]
      exact system.isInitial_of_point hjlt.le Y
    · rw [← haEq]
      exact hj.1

end AllThoseBigRamsey.Pseudotree.CriticalCopies
