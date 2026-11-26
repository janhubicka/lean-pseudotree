import PseudotreeValidation.GeneralizedNormalization
import PseudotreeValidation.NormalizationLocal

/-! Projection geometry for generalized selected levels. These are the
same local inverse-prefix arguments as for chains, using the generalized
separation and binary-gap theorems in place of the spine condition. -/
namespace AllThoseBigRamsey.Pseudotree.GeneralizedNormalization

open RayEmbeddings LevelProjection
open DiaryNormalization (RawNode essential schedule rank schedule_rank
  schedule_strict schedule_mem schedule_index_le rank_lt length_mem_essential
  schedule_no_between)

/-- Prefix closure of the explicitly projected coding set. -/
noncomputable def nodes (C : Finset Word)  : Finset Word := by
  classical
  exact (codes C).biUnion (fun w => (Finset.range (w.length+1)).image (fun j => w.take j))

theorem mem_nodes_iff {C : Finset Word} {s : Word} :
    s ∈ nodes C ↔ ∃ w ∈ C, ∃ j, j ≤ rank (selected C) w.length ∧
      project (schedule (selected C)) w j = s := by
  classical
  constructor
  · intro hs
    obtain ⟨u, hu, hs⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    have hj' : j ≤ rank (selected C) w.length := by
      simpa only [Finset.mem_range, code, project_length, Nat.lt_succ_iff] using hj
    exact ⟨w, hw, j, hj', (project_take _ _ hj').symm⟩
  · rintro ⟨w, hw, j, hj, rfl⟩
    refine Finset.mem_biUnion.mpr ⟨_, Finset.mem_image.mpr ⟨w, hw, rfl⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨j, by simpa [code] using hj, by simpa only [code] using project_take _ _ hj⟩

theorem mem_nodes_iff_domain {C : Finset Word} {s : Word} (hC : C.Nonempty) :
    s ∈ nodes C ↔ Domain (C : Set Word) (schedule (selected C)) s := by
  constructor
  · intro hs
    obtain ⟨w, hw, j, hj, rfl⟩ := mem_nodes_iff.mp hs
    apply domain_project hw
    have h := (schedule_strict (selected_nonempty hC)).monotone hj
    simpa only [schedule_rank (essential_subset_selected C (length_mem_essential hw))] using h
  · rintro ⟨w, hw, hlen, heq⟩
    refine mem_nodes_iff.mpr ⟨w, hw, s.length, ?_, heq⟩
    exact schedule_index_le (selected_nonempty hC)
      (essential_subset_selected C (length_mem_essential hw)) hlen

theorem nodes_root {C : Finset Word} (hC : C.Nonempty) : [] ∈ nodes C := by
  apply (mem_nodes_iff_domain hC).mpr
  obtain ⟨w, hw⟩ := hC
  exact domain_root ⟨w, hw, root_bound ⟨w, hw⟩ hw⟩

theorem nodes_prefix_closed {C : Finset Word} {s : Word} (hs : s ∈ nodes C)
    {j : Nat} (hj : j ≤ s.length) : s.take j ∈ nodes C := by
  obtain ⟨w, hw, i, hi, rfl⟩ := mem_nodes_iff.mp hs
  have hj' : j ≤ i := by simpa using hj
  rw [project_take _ _ hj']
  exact mem_nodes_iff.mpr ⟨w, hw, j, le_trans hj' hi, rfl⟩

theorem codes_subset_nodes (C : Finset Word)  : codes C ⊆ nodes C := by
  classical
  intro w hw
  change w ∈ C.image (fun x => project (schedule (selected C)) x (rank (selected C) x.length)) at hw
  obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hw
  rw [← heq]
  exact mem_nodes_iff.mpr ⟨x, hx, _, le_rfl, rfl⟩

theorem nodes_bounded {C : Finset Word} {s : Word} (hs : s ∈ nodes C) :
    s.length < (selected C).card := by
  obtain ⟨w, hw, i, hi, rfl⟩ := mem_nodes_iff.mp hs
  simp only [project_length]
  exact lt_of_le_of_lt hi (rank_lt (essential_subset_selected C (length_mem_essential hw)))

theorem project_of_node {C : Finset Word} {s : Word} (hC : C.Nonempty)
    (hs : s ∈ nodes C) :
    project (schedule (selected C))
      (inverse (C : Set Word) (schedule (selected C)) s) s.length = s := by
  obtain ⟨w, hw, hlen, heq⟩ := (mem_nodes_iff_domain hC).mp hs
  rw [inverse_eq (schedule_strict (selected_nonempty hC))
    (separates C) hw hlen heq]
  have h := project_eq_of_take_eq (schedule_strict (selected_nonempty hC))
    (s := w.take (schedule (selected C) s.length)) (t := w) (j := s.length)
    (by simp)
  exact h.trans heq

theorem inverse_length {C : Finset Word} {s : Word} (hC : C.Nonempty)
    (hs : s ∈ nodes C) :
    (inverse (C : Set Word) (schedule (selected C)) s).length =
      schedule (selected C) s.length := by
  obtain ⟨w, hw, hlen, heq⟩ := (mem_nodes_iff_domain hC).mp hs
  rw [inverse_eq (schedule_strict (selected_nonempty hC))
    (separates C) hw hlen heq, List.length_take, Nat.min_eq_left hlen]

theorem inverse_rawNode {C : Finset Word} {s : Word} (hC : C.Nonempty)
    (hs : s ∈ nodes C) : RawNode C (inverse (C : Set Word) (schedule (selected C)) s) := by
  obtain ⟨w, hw, hlen, heq⟩ := (mem_nodes_iff_domain hC).mp hs
  refine ⟨w, hw, ?_⟩
  rw [inverse_eq (schedule_strict (selected_nonempty hC))
    (separates C) hw hlen heq]
  exact List.take_prefix _ _

theorem project_of_rawNode {C : Finset Word} {w : Word} (hC : C.Nonempty)
    (hw : RawNode C w) {j : Nat} (hlen : w.length = schedule (selected C) j) :
    project (schedule (selected C)) w j ∈ nodes C ∧
      inverse (C : Set Word) (schedule (selected C))
        (project (schedule (selected C)) w j) = w := by
  obtain ⟨c, hc, hp⟩ := hw
  have hcj : schedule (selected C) j ≤ c.length := by
    simpa only [← hlen] using hp.length_le
  have ht : c.take (schedule (selected C) j) = w := by
    simpa only [hlen] using (List.prefix_iff_eq_take.mp hp).symm
  have heq := project_eq_of_take_eq (schedule_strict (selected_nonempty hC))
    (s := c) (t := w) (j := j) (by rw [ht, ← hlen, List.take_length])
  constructor
  · rw [← heq]
    exact (mem_nodes_iff_domain hC).mpr (domain_project hc hcj)
  · rw [← heq, inverse_project (schedule_strict (selected_nonempty hC))
      (separates C) hc hcj, ht]

theorem inverse_injective {C : Finset Word} {s t : Word} (hC : C.Nonempty)
    (hs : s ∈ nodes C) (ht : t ∈ nodes C)
    (heq : inverse (C : Set Word) (schedule (selected C)) s =
      inverse (C : Set Word) (schedule (selected C)) t) : s = t := by
  have hlen := congrArg List.length heq
  rw [inverse_length hC hs, inverse_length hC ht] at hlen
  have hlen' := (schedule_strict (selected_nonempty hC)).injective hlen
  rw [← project_of_node hC hs, ← project_of_node hC ht, heq, hlen']

theorem code_iff_inverse {C : Finset Word} {s : Word} (hC : C.Nonempty)
    (hs : s ∈ nodes C) :
    s ∈ codes C ↔ inverse (C : Set Word) (schedule (selected C)) s ∈ C := by
  classical
  constructor
  · intro hc
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hc
    rw [← heq, code, inverse_project (schedule_strict (selected_nonempty hC))
      (separates C) hw
      (schedule_rank (essential_subset_selected C (length_mem_essential hw))).le,
      schedule_rank (essential_subset_selected C (length_mem_essential hw)), List.take_length]
    exact hw
  · intro hc
    let w := inverse (C : Set Word) (schedule (selected C)) s
    have hw : w ∈ C := hc
    have hlen : rank (selected C) w.length = s.length := by
      apply (schedule_strict (selected_nonempty hC)).injective
      rw [schedule_rank (essential_subset_selected C (length_mem_essential hw))]
      exact inverse_length hC hs
    exact Finset.mem_image.mpr ⟨w, hw, by unfold code; rw [hlen]; exact project_of_node hC hs⟩

/-- Compression retains precisely the actual children of each prefix in the
finite coding tree. Empty stretches have one descendant and add no branch. -/
theorem child_iff_rawChild {C : Finset Word} {s : Word} (hC : C.Nonempty)
    (hs : s ∈ nodes C) (a : Fin 3) :
    child s a ∈ nodes C ↔
      RawNode C (child (inverse (C : Set Word) (schedule (selected C)) s) a) := by
  let K := schedule (selected C)
  have hK : StrictMono K := schedule_strict (selected_nonempty hC)
  have hsep := separates C
  constructor
  · intro hchild
    obtain ⟨w, hw, hlen, heq⟩ := (mem_nodes_iff_domain hC).mp hchild
    have heq' : project K w (s.length+1) = s ++ [a] := by simpa only [child,
      List.length_append, List.length_singleton] using heq
    have hlen' : K (s.length+1) ≤ w.length := by simpa [K, child] using hlen
    have hj : K s.length < w.length := lt_of_lt_of_le (hK (Nat.lt_succ_self _)) hlen'
    have hp : project K w s.length = s := by
      have h := congrArg (List.take s.length) heq
      simpa only [child, project_take _ _ (by simp : s.length ≤ (s ++ [a]).length),
        List.take_left] using h
    have ha : w[K s.length] = a := by
      have h' : [w[K s.length]] = [a] := List.append_cancel_left (by
        simpa only [child, List.length_append, List.length_singleton, project_succ, hp,
          List.getElem?_eq_getElem hj, Option.getD_some] using heq')
      exact List.singleton_inj.mp h'
    refine ⟨w, hw, ?_⟩
    rw [inverse_eq hK hsep hw hj.le hp]
    change (w.take (K s.length) ++ [a]).IsPrefix w
    rw [← ha, List.take_append_getElem hj]
    exact List.take_prefix _ _
  · rintro ⟨w, hw, tail, htail⟩
    let p := inverse (C : Set Word) K s
    have hplen : p.length = K s.length := inverse_length hC hs
    have htail' : w = p ++ a :: tail := by simpa [p, child] using htail.symm
    have hlength : K s.length < w.length := by
      rw [htail']
      simp only [List.length_append, List.length_cons]
      omega
    have hjrank : s.length < rank (selected C) w.length := hK.lt_iff_lt.mp (by
      simpa only [K, schedule_rank (essential_subset_selected C (length_mem_essential hw))]
        using hlength)
    have hnext : K (s.length+1) ≤ w.length := by
      have h := hK.monotone (Nat.succ_le_of_lt hjrank)
      simpa only [K, schedule_rank (essential_subset_selected C (length_mem_essential hw))] using h
    have htake : w.take (K s.length) = p := by rw [← hplen, htail']; simp
    have hp : project K w s.length = s :=
      (project_eq_of_take_eq hK (by rw [htake, ← hplen, List.take_length])).trans
        (project_of_node hC hs)
    have ha : w[K s.length]?.getD 0 = a := by rw [← hplen, htail']; simp
    apply (mem_nodes_iff_domain hC).mpr
    refine ⟨w, hw, ?_, ?_⟩
    · simpa [child, K] using hnext
    · have heq : project K w (s.length+1) = s ++ [a] := by rw [project_succ, hp, ha]
      simpa only [child, List.length_append, List.length_singleton] using heq

theorem inverse_lt_iff {C : Finset Word} {s t : Word} (hC : C.Nonempty)
    (hs : s ∈ nodes C) (ht : t ∈ nodes C) :
    inverse (C : Set Word) (schedule (selected C)) s <
      inverse (C : Set Word) (schedule (selected C)) t ↔ s < t := by
  have hfs : (rayMap hC).map s = inverse (C : Set Word) (schedule (selected C)) s :=
    PrefixRayMap.completion_agrees _ _ ((mem_nodes_iff_domain hC).mp hs)
  have hft : (rayMap hC).map t = inverse (C : Set Word) (schedule (selected C)) t :=
    PrefixRayMap.completion_agrees _ _ ((mem_nodes_iff_domain hC).mp ht)
  rw [← hfs, ← hft]
  exact (DiaryNormalization.rayMap_strictMono _).lt_iff_lt


theorem codes_card {C : Finset Word} (hC : C.Nonempty) : (codes C).card = C.card := by
  classical
  exact Finset.card_image_of_injOn (code_injective hC)

theorem nodes_image (f : RayStrongMap) (C : Finset Word) :
    nodes (C.image f.map) = nodes C := by
  unfold nodes
  rw [codes_image]

/-! Consecutive retained levels really are consecutive steps of the
deterministic recursion. This fact is needed for the new restriction on
consecutive type-(d) events. -/

theorem first_le_reached {C : Finset Word} {p q : Nat}
    (hf : First C p) (hq : Reached C q) : p ≤ q := by
  induction hq with
  | first h => exact hf.2 _ h.1
  | next _ h ih => exact ih.trans h.1.le

private theorem next_no_reached_between (C : Finset Word) (q : Nat) :
    ∀ p, Reached C p → Next C p q →
      ∀ t, Reached C t → p < t → t < q → False := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro p hp hpq t ht
    induction ht with
    | first hf =>
      intro hpt _
      exact (Nat.not_lt_of_ge (first_le_reached hf hp)) hpt
    | @next r t hr hrt ihr =>
      intro hpt htq
      rcases lt_trichotomy r p with hrp | heq | hpr
      · exact ih t htq r hr hrt p hp hrp hpt
      · subst r
        exact (Nat.ne_of_lt htq) (next_unique hrt hpq)
      · exact ihr hpr (hrt.1.trans htq)

theorem adjacent_next {C : Finset Word} {p q : Nat}
    (hp : p ∈ selected C) (hq : q ∈ selected C) (hpq : p < q)
    (hgap : ∀ k ∈ selected C, p < k → k < q → False) :
    Next C p q := by
  have hreach := mem_selected_iff.mp hp
  have h := mem_selected_iff.mp hq
  cases h with
  | first hf => exact False.elim ((Nat.not_lt_of_ge (first_le_reached hf hreach)) hpq)
  | @next r q hr hn =>
    rcases lt_trichotomy r p with hrp | heq | hpr
    · exact False.elim (next_no_reached_between C q r hr hn p hreach hrp hpq)
    · simpa only [heq] using hn
    · exact False.elim (hgap r (mem_selected_iff.mpr hr) hpr hn.1)

theorem initial_essential {C : Finset Word} (hC : C.Nonempty) :
    schedule (selected C) 0 ∈ essential C := by
  have hL := selected_nonempty hC
  obtain ⟨p, hp⟩ := first_exists hC
  have hpL := essential_subset_selected C hp.1
  have hle := (schedule_strict hL).monotone (Nat.zero_le (rank (selected C) p))
  rw [schedule_rank hpL] at hle
  have hzero : schedule (selected C) 0 ∈ selected C :=
    schedule_mem (Finset.card_pos.mpr hL)
  have hge := first_le_reached hp (mem_selected_iff.mp hzero)
  rw [le_antisymm hle hge]
  exact hp.1

theorem nonessential_event {C : Finset Word} {j : Nat}
    (hj : j ∈ selected C) (he : j ∉ essential C) :
    ∃ w ∈ C, w[j]? = some 1 := by
  have h := mem_selected_iff.mp hj
  cases h with
  | first hf => exact False.elim (he hf.1)
  | next _ hn =>
    obtain ⟨w, hw, _, hone⟩ := hn.2.1.resolve_left he
    exact ⟨w, hw, hone⟩

end AllThoseBigRamsey.Pseudotree.GeneralizedNormalization
