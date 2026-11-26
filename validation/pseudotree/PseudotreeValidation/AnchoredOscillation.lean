import PseudotreeValidation.GenericIncomparables

/-! Anchored oscillation: two distinct cones are independently end-extensible.
No homogeneity or model identification is needed for this geometric lemma. -/
namespace AllThoseBigRamsey.Pseudotree

namespace Oscillation

private theorem extend_left_increases (X : List Bool → Prop) (hext : EndExtensions X)
    {s t : List Bool} (hs : X s)
    (hlast : lastFrom none (differenceWord s t) ≠ some true) :
    ∃ s', X s' ∧ oscillation s' t = oscillation s t + 1 := by
  obtain ⟨u, hu, hsu⟩ := hext s hs t.length
  let s' := s ++ List.replicate t.length false ++ u
  have hn : 0 < trueCount u := by simpa [trueCount] using List.count_pos_iff.mpr hu
  have hd : differenceWord s' t =
      differenceWord s t ++ List.replicate (trueCount u) true :=
    differenceWord_extend_left s t u t.length (by omega)
  refine ⟨s', hsu, ?_⟩
  simp only [oscillation, hd, runCountFrom_append]
  rw [runCountFrom_replicate _ true _ hn hlast]

/-- Unlike the one-family lemma, this does not exchange the family of a
coordinate. One extends whichever side is opposite to the final run. -/
theorem two_family_step (X Y : List Bool → Prop)
    (hX : EndExtensions X) (hY : EndExtensions Y)
    {s t : List Bool} (hs : X s) (ht : Y t) :
    ∃ s' t', X s' ∧ Y t' ∧ oscillation s' t' = oscillation s t + 1 := by
  by_cases hlast : lastFrom none (differenceWord s t) = some true
  · have h : lastFrom none (differenceWord t s) ≠ some true := by
      rw [differenceWord_swap s t]
      have hh := lastFrom_not none (differenceWord s t)
      simp only [Option.map_none] at hh
      rw [hh, hlast]
      decide
    obtain ⟨t', ht', he⟩ := extend_left_increases Y hY ht h
    refine ⟨s,t',hs,ht',?_⟩
    calc
      oscillation s t' = oscillation t' s := oscillation_symm t' s
      _ = oscillation t s + 1 := he
      _ = oscillation s t + 1 := congrArg (fun n => n+1) (oscillation_symm s t)
  · obtain ⟨s', hs', he⟩ := extend_left_increases X hX hs hlast
    exact ⟨s',t,hs',ht,he⟩

theorem two_family_tail (X Y : List Bool → Prop)
    (hneX : ∃ s, X s) (hneY : ∃ t, Y t)
    (hX : EndExtensions X) (hY : EndExtensions Y) :
    ∃ k₀ : Nat, ∀ k ≥ k₀, ∃ s t, X s ∧ Y t ∧ oscillation s t = k := by
  obtain ⟨s,hs⟩ := hneX
  obtain ⟨t,ht⟩ := hneY
  refine ⟨oscillation s t,?_⟩
  have h (n : Nat) : ∃ u v, X u ∧ Y v ∧ oscillation u v = oscillation s t + n := by
    induction n with
    | zero => exact ⟨s,t,hs,ht,by simp⟩
    | succ n ih =>
      obtain ⟨u,v,hu,hv,he⟩ := ih
      obtain ⟨u',v',hu',hv',he'⟩ := two_family_step X Y hX hY hu hv
      exact ⟨u',v',hu',hv',by omega⟩
  intro k hk
  obtain ⟨u,v,hu,hv,he⟩ := h (k - oscillation s t)
  exact ⟨u,v,hu,hv,by omega⟩

end Oscillation

namespace FiniteOscillation

theorem two_family_tail (X Y : Finset Nat → Prop)
    (hneX : ∃ s, X s) (hneY : ∃ t, Y t)
    (hX : ∀ s, X s → ∀ N, ∃ t, X t ∧ s ⊂ t ∧ ∀ i ∈ t, i ∉ s → N < i)
    (hY : ∀ s, Y s → ∀ N, ∃ t, Y t ∧ s ⊂ t ∧ ∀ i ∈ t, i ∉ s → N < i) :
    ∃ k₀ : Nat, ∀ k ≥ k₀, ∃ s t, X s ∧ Y t ∧ osc s t = k := by
  obtain ⟨s,hs⟩ := hneX
  obtain ⟨t,ht⟩ := hneY
  obtain ⟨k₀,h⟩ := Oscillation.two_family_tail
    (fun w => X (support w)) (fun w => Y (support w))
    ⟨wordOf s,by simpa using hs⟩ ⟨wordOf t,by simpa using ht⟩
    (word_endExtensions X hX) (word_endExtensions Y hY)
  refine ⟨k₀,fun k hk => ?_⟩
  obtain ⟨u,v,hu,hv,he⟩ := h k hk
  exact ⟨support u,support v,hu,hv,by simpa only [osc_support] using he⟩

end FiniteOscillation

namespace Profiles.System

variable {M : Type*} [SemilatticeInf M] (E : System M)

/-- The cone at a with representative v, restricted to S. -/
def cone (_E : System M) (S : Set M) (a v : M) : Set M := {x | x ∈ S ∧ a < x ⊓ v}

theorem cone_upward {S : Set M} {a v x y : M}
    (hx : x ∈ E.cone S a v) (hy : y ∈ S) (hxy : x ≤ y) :
    y ∈ E.cone S a v :=
  ⟨hy,hx.2.trans_le (inf_le_inf_right v hxy)⟩

/-- Each nonempty cone inherits all the richness properties. -/
theorem cone_rich {S : Set M} (hS : E.RichSubset S)
    {a v : M} (hv : v ∈ S) (hav : a < v) :
    E.RichSubset (E.cone S a v) where
  nonempty := ⟨v,hv,by simpa using hav⟩
  above := by
    intro y hy
    obtain ⟨w,hw,hyw⟩ := hS.above y hy.1
    exact ⟨w,E.cone_upward hy hw hyw.le,hyw⟩
  intervals := by
    intro y w hy hw hyw
    apply (hS.intervals hy.1 hw.1 hyw).mono
    intro x hx
    exact ⟨E.cone_upward hy hx.1 hx.2.1.le,hx.2⟩
  branching := by
    intro x b hx hb hxb
    obtain ⟨z,hz,hxz,hmeet⟩ := hS.branching hx.1 hb.1 hxb
    exact ⟨z,E.cone_upward hx hz hxz.le,hxz,hmeet⟩

/-- Moving upward in distinct cones preserves their exact common meet. -/
theorem cone_cross_meet {S : Set M} {a v w x y : M}
    (hvw : v ⊓ w = a) (hx : x ∈ E.cone S a v)
    (hy : y ∈ E.cone S a w) : x ⊓ y = a := by
  let p := x ⊓ v
  let q := y ⊓ w
  have hp : a < p := hx.2
  have hq : a < q := hy.2
  have hpv : p ≤ v := inf_le_right
  have hqw : q ≤ w := inf_le_right
  have hpx : p ≤ x := inf_le_left
  have hqy : q ≤ y := inf_le_left
  have hpq : p ⊓ q = a := by
    apply le_antisymm
    · exact (inf_le_inf hpv hqw).trans_eq hvw
    · exact le_inf hp.le hq.le
  have hxq : x ⊓ q = a :=
    (E.inf_eq_of_above_branch hpx (by rw [hpq]; exact hp)).trans hpq
  have hqx : q ⊓ x = a := by simpa [inf_comm] using hxq
  have hyx : y ⊓ x = a :=
    (E.inf_eq_of_above_branch hqy (by rw [hqx]; exact hq)).trans hqx
  simpa [inf_comm] using hyx

/-- Oscillations of points with a prescribed meet contain a final segment. -/
theorem anchored_oscillations {S : Set M} (hS : E.RichSubset S) {a : M}
    (ha : a ∈ S) :
    ∃ k₀ : Nat, ∀ k ≥ k₀, ∃ x y, x ∈ S ∧ y ∈ S ∧ a < x ∧ a < y ∧
      x ⊓ y = a ∧ FiniteOscillation.osc (E.profile x) (E.profile y) = k := by
  obtain ⟨v,hv,hav⟩ := hS.above a ha
  obtain ⟨w,hw,haw,hwv⟩ := hS.branching ha hv hav
  let X := E.cone S a v
  let Y := E.cone S a w
  have hX : E.RichSubset X := E.cone_rich hS hv hav
  have hY : E.RichSubset Y := E.cone_rich hS hw haw
  obtain ⟨k₀,h⟩ := FiniteOscillation.two_family_tail
    (E.Repeated X) (E.Repeated Y)
    (E.repeated_nonempty hX) (E.repeated_nonempty hY)
    (fun _ hs N => E.repeated_endExtension hX hs N)
    (fun _ hs N => E.repeated_endExtension hY hs N)
  refine ⟨k₀,fun k hk => ?_⟩
  obtain ⟨s,t,hs,ht,hst⟩ := h k hk
  obtain ⟨u,hu,x,hx,hux,hus,hxs⟩ := hs
  obtain ⟨z,hz,y,hy,hzy,hzt,hyt⟩ := ht
  exact ⟨x,y,hx.1,hy.1,hx.2.trans_le inf_le_left,hy.2.trans_le inf_le_left,
    E.cone_cross_meet (by simpa [inf_comm] using hwv) hx hy,
    by simpa only [hxs,hyt] using hst⟩

end Profiles.System
end AllThoseBigRamsey.Pseudotree
