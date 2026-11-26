import PseudotreeValidation.DiaryRecoveryNaturality

/-!
# Generalized diary normalization

The selected levels of an arbitrary finite word set are generated from the
least essential level by repeatedly taking the least later essential level or
the first eligible 1-event on any live branch. Unlike chain normalization,
alternating events on different branches can produce arbitrarily many extra
levels. We reuse the existing projection, essential-level transport, and
binary-padding lemmas.

The inductive reachability definition is the increasing recursion in the
manuscript, not an existential choice of a diary or a Ramsey assumption.
-/

namespace AllThoseBigRamsey.Pseudotree.GeneralizedNormalization

open RayEmbeddings LevelProjection
open DiaryNormalization (essential essential_nonempty essential_le length_mem_essential
  fork_mem_essential schedule rank schedule_rank schedule_strict schedule_mem
  schedule_index_lt schedule_no_between rank_lt)
open DiaryRecovery (essential_image map_get level_interval one_edge_origin rank_image project_image)

def First (C : Finset Word) (p : Nat) : Prop :=
  p ∈ essential C ∧ ∀ k ∈ essential C, p ≤ k

/-- A candidate later event is essential, or is a 1 on a branch whose digit
at the preceding retained level was binary. In the latter case p < q
ensures that the digit at p exists. -/
def Candidate (C : Finset Word) (p q : Nat) : Prop :=
  q ∈ essential C ∨ ∃ w ∈ C, w[p]? ≠ some 1 ∧ w[q]? = some 1

def Next (C : Finset Word) (p q : Nat) : Prop :=
  p < q ∧ Candidate C p q ∧
    ∀ j, p < j → j < q → ¬ Candidate C p j

theorem first_exists {C : Finset Word} (hC : C.Nonempty) :
    ∃ p, First C p := by
  classical
  have hex : ∃ p, p ∈ essential C := essential_nonempty hC
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro k hk
  by_contra h
  exact Nat.find_min hex (Nat.lt_of_not_ge h) hk

theorem next_exists {C : Finset Word} {p k : Nat}
    (hpk : p < k) (hk : Candidate C p k) :
    ∃ q, Next C p q ∧ q ≤ k := by
  classical
  have hex : ∃ q, p < q ∧ Candidate C p q := ⟨k, hpk, hk⟩
  refine ⟨Nat.find hex, ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩, ?_⟩
  · intro j hpj hj hcan
    exact Nat.find_min hex hj ⟨hpj, hcan⟩
  · by_contra h
    exact Nat.find_min hex (Nat.lt_of_not_ge h) ⟨hpk, hk⟩

theorem next_unique {C : Finset Word} {p q r : Nat}
    (hq : Next C p q) (hr : Next C p r) : q = r := by
  rcases lt_trichotomy q r with h | h | h
  · exact False.elim (hr.2.2 q hq.1 h hq.2.1)
  · exact h
  · exact False.elim (hq.2.2 r hr.1 h hr.2.1)

theorem candidate_le {C : Finset Word} {p q : Nat} (h : Candidate C p q) :
    q ≤ C.sup List.length := by
  rcases h with h | ⟨w, hw, _, hone⟩
  · exact essential_le h
  · exact (List.getElem?_eq_some_iff.mp hone).1.le.trans (Finset.le_sup hw)

/-- The levels reached by the deterministic increasing recursion. -/
inductive Reached (C : Finset Word) : Nat → Prop
  | first {p : Nat} : First C p → Reached C p
  | next {p q : Nat} : Reached C p → Next C p q → Reached C q

theorem reached_le {C : Finset Word} {q : Nat} (h : Reached C q) :
    q ≤ C.sup List.length := by
  cases h with
  | first h => exact essential_le h.1
  | next _ h => exact candidate_le h.2.1

/-- Since every step increases and is bounded by the maximum coding length,
the recursion is finite. No bound by the number of coding points is used. -/
noncomputable def selected (C : Finset Word) : Finset Nat := by
  classical
  exact (Finset.range (C.sup List.length + 1)).filter (Reached C)

theorem mem_selected_iff {C : Finset Word} {k : Nat} :
    k ∈ selected C ↔ Reached C k := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (reached_le h)), h⟩

/-- From any reached level one reaches every later essential level. -/
private theorem reach_target (C : Finset Word) (k : Nat) (hk : k ∈ essential C)
    (d : Nat) : ∀ p, k - p = d → p ≤ k → Reached C p → Reached C k := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro p hd hp hreach
    by_cases heq : p = k
    · simpa only [heq] using hreach
    · have hpk : p < k := by omega
      obtain ⟨q, hn, hq⟩ := next_exists hpk (Or.inl hk)
      have hpq := hn.1
      exact ih (k - q) (by omega) q rfl hq (Reached.next hreach hn)

theorem essential_subset_selected (C : Finset Word) : essential C ⊆ selected C := by
  intro k hk
  obtain ⟨p, hp⟩ := first_exists (show C.Nonempty from by
    by_contra hn
    have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    subst C
    simp [essential, DiaryNormalization.ForkAt] at hk)
  exact mem_selected_iff.mpr
    (reach_target C k hk (k-p) p rfl (hp.2 k hk) (Reached.first hp))

theorem selected_nonempty {C : Finset Word} (hC : C.Nonempty) :
    (selected C).Nonempty :=
  (essential_nonempty hC).mono (essential_subset_selected C)

/-- The next event is minimal among *all* eligible branches, so skipped
1s are legal only on branches already entered by a 1. -/
theorem selected_gap_one {C : Finset Word} {w : Word} {p q j : Nat}
    (hw : w ∈ C) (hp : p ∈ selected C)
    (hgap : ∀ k ∈ selected C, p < k → k < q → False)
    (hpj : p < j) (hjq : j < q) (hone : w[j]? = some 1) :
    w[p]? = some 1 := by
  by_contra hstart
  obtain ⟨r, hr, hrj⟩ := next_exists hpj (Or.inr ⟨w, hw, hstart, hone⟩)
  have hrmem := mem_selected_iff.mpr (Reached.next (mem_selected_iff.mp hp) hr)
  exact hgap r hrmem hr.1 (hrj.trans_lt hjq)

theorem separates (C : Finset Word) : Separates (C : Set Word) (schedule (selected C)) := by
  intro s hs t ht k hks hkt hpre hne
  have hk : k ∈ selected C := essential_subset_selected C
    (fork_mem_essential ⟨s, hs, t, ht, hks, hkt, hpre, hne⟩)
  exact ⟨rank (selected C) k, schedule_rank hk⟩

theorem binaryGaps {C : Finset Word} (hC : C.Nonempty) :
    BinaryGaps (C : Set Word) (schedule (selected C)) := by
  intro w hw i hlen hstart j hij hji hone
  have hL := selected_nonempty hC
  have hend := essential_subset_selected C (length_mem_essential hw)
  have hii : i < (selected C).card :=
    lt_trans (Nat.lt_succ_self i) (schedule_index_lt hL hend hlen)
  have hp : schedule (selected C) i ∈ selected C := schedule_mem hii
  exact hstart (selected_gap_one hw hp
    (fun l hl hlo hhi => schedule_no_between hL hl hlo hhi) hij hji hone)

theorem root_bound {C : Finset Word} (hC : C.Nonempty) {w : Word} (hw : w ∈ C) :
    schedule (selected C) 0 ≤ w.length := by
  have hm := (schedule_strict (selected_nonempty hC)).monotone
    (Nat.zero_le (rank (selected C) w.length))
  simpa only [schedule_rank (essential_subset_selected C (length_mem_essential hw))] using hm

/-- The literal normalized code attached to each original point. -/
noncomputable def code (C : Finset Word) (w : Word) : Word :=
  project (schedule (selected C)) w (rank (selected C) w.length)

noncomputable def codes (C : Finset Word) : Finset Word := by
  classical
  exact C.image (code C)

/-- The projection inverse is an actual ray-preserving map. The existing
completion theorem supplies values off the projected prefix domain. -/
noncomputable def rayMap {C : Finset Word} (hC : C.Nonempty) : RayStrongMap :=
  (prefixRayMap (schedule_strict (selected_nonempty hC)) (separates C)
    (binaryGaps hC)
    (by obtain ⟨w, hw⟩ := hC; exact ⟨w, hw, root_bound ⟨w, hw⟩ hw⟩)).completion

theorem rayMap_code {C : Finset Word} (hC : C.Nonempty) {w : Word} (hw : w ∈ C) :
    (rayMap hC).map (code C w) = w := by
  apply completion_project
  · exact hw
  · exact schedule_rank (essential_subset_selected C (length_mem_essential hw))

theorem code_injective {C : Finset Word} (hC : C.Nonempty) :
    Set.InjOn (code C) (C : Set Word) := by
  intro s hs t ht heq
  have h := congrArg (rayMap hC).map heq
  simpa only [rayMap_code hC hs, rayMap_code hC ht] using h

theorem rayMap_codes {C : Finset Word} (hC : C.Nonempty) :
    (codes C).image (rayMap hC).map = C := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
    simpa only [rayMap_code hC hx] using hx
  · intro hw
    exact Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨w, hw, rfl⟩, rayMap_code hC hw⟩

/-! Naturality: the key difference from the old chain proof is that the
eligible branch is allowed to change at each step. -/

theorem first_map (f : RayStrongMap) {C : Finset Word} {p : Nat} (h : First C p) :
    First (C.image f.map) (f.level p) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [essential_image]
    exact Finset.mem_image.mpr ⟨p, h.1, rfl⟩
  · intro k hk
    rw [essential_image] at hk
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
    exact (show StrictMono f.level from fun _ _ h => f.level_strict h).monotone (h.2 q hq)

theorem first_preimage (f : RayStrongMap) {C : Finset Word} {j : Nat}
    (h : First (C.image f.map) j) :
    ∃ p, First C p ∧ j = f.level p := by
  classical
  have hj := h.1
  rw [essential_image] at hj
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
  refine ⟨p, ⟨hp, ?_⟩, rfl⟩
  intro k hk
  have h' := h.2 (f.level k) (by
    rw [essential_image]
    exact Finset.mem_image.mpr ⟨k, hk, rfl⟩)
  exact (show StrictMono f.level from fun _ _ h => f.level_strict h).le_iff_le.mp h'

theorem candidate_map (f : RayStrongMap) {C : Finset Word} {p q : Nat}
    (hpq : p < q) (h : Candidate C p q) :
    Candidate (C.image f.map) (f.level p) (f.level q) := by
  classical
  rcases h with h | ⟨w, hw, hstart, hone⟩
  · left
    rw [essential_image]
    exact Finset.mem_image.mpr ⟨q, h, rfl⟩
  · have hq : q < w.length := (List.getElem?_eq_some_iff.mp hone).1
    right
    refine ⟨f.map w, Finset.mem_image.mpr ⟨w, hw, rfl⟩, ?_, ?_⟩
    · rw [map_get f w p (hpq.trans hq)]
      exact hstart
    · rw [map_get f w q hq]
      exact hone

/-- A candidate in the target, even inside padding, originates at a
candidate source level no later than it. -/
theorem candidate_preimage_le (f : RayStrongMap) {C : Finset Word} {p j : Nat}
    (hpj : f.level p < j) (h : Candidate (C.image f.map) (f.level p) j) :
    ∃ q, p < q ∧ Candidate C p q ∧ f.level q ≤ j := by
  classical
  rcases h with h | ⟨w', hw', hstart, hone⟩
  · rw [essential_image] at h
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
    exact ⟨q, (show StrictMono f.level from fun _ _ h => f.level_strict h).lt_iff_lt.mp hpj,
      Or.inl hq, le_rfl⟩
  · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hw'
    have hjlen : j < f.level w.length := by
      simpa only [f.length_map] using (List.getElem?_eq_some_iff.mp hone).1
    obtain ⟨i, hpi, hil, hlow, hhigh⟩ := level_interval f hpj.le hjlen
    have hnot : w[p]? ≠ some 1 := by
      simpa only [map_get f w p (lt_of_le_of_lt hpi hil)] using hstart
    have hiOne := one_edge_origin f w hil hlow hhigh hone
    have hpi' : p < i := by
      rcases hpi.eq_or_lt with heq | hlt
      · exact False.elim (hnot (heq ▸ hiOne))
      · exact hlt
    exact ⟨i, hpi', Or.inr ⟨w, hw, hnot, hiOne⟩, hlow⟩

theorem next_map (f : RayStrongMap) {C : Finset Word} {p q : Nat}
    (h : Next C p q) : Next (C.image f.map) (f.level p) (f.level q) := by
  refine ⟨f.level_strict h.1, candidate_map f h.1 h.2.1, ?_⟩
  intro j hpj hjq hc
  obtain ⟨k, hpk, hc', hkj⟩ := candidate_preimage_le f hpj hc
  have hkq := (show StrictMono f.level from fun _ _ h => f.level_strict h).lt_iff_lt.mp
    (hkj.trans_lt hjq)
  exact h.2.2 k hpk hkq hc'

theorem next_preimage (f : RayStrongMap) {C : Finset Word} {p j : Nat}
    (h : Next (C.image f.map) (f.level p) j) :
    ∃ q, Next C p q ∧ j = f.level q := by
  obtain ⟨k, hpk, hc, _⟩ := candidate_preimage_le f h.1 h.2.1
  obtain ⟨q, hq, _⟩ := next_exists hpk hc
  exact ⟨q, hq, next_unique h (next_map f hq)⟩

theorem reached_map (f : RayStrongMap) {C : Finset Word} {p : Nat} (h : Reached C p) :
    Reached (C.image f.map) (f.level p) := by
  induction h with
  | first h => exact Reached.first (first_map f h)
  | next _ h ih => exact Reached.next ih (next_map f h)

theorem reached_preimage (f : RayStrongMap) {C : Finset Word} {j : Nat}
    (h : Reached (C.image f.map) j) :
    ∃ p, Reached C p ∧ j = f.level p := by
  induction h with
  | first h =>
    obtain ⟨p, hp, heq⟩ := first_preimage f h
    exact ⟨p, Reached.first hp, heq⟩
  | next _ h ih =>
    obtain ⟨p, hp, heq⟩ := ih
    rw [heq] at h
    obtain ⟨q, hq, heq'⟩ := next_preimage f h
    exact ⟨q, Reached.next hp hq, heq'⟩

/-- The selected level set is natural for all finite sets, without a
distinguished branch, chain hypothesis, or sparse-tree hypothesis. -/
theorem selected_image (f : RayStrongMap) (C : Finset Word) :
    selected (C.image f.map) = (selected C).image f.level := by
  classical
  ext j
  rw [mem_selected_iff, Finset.mem_image]
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := reached_preimage f h
    exact ⟨p, mem_selected_iff.mpr hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact reached_map f (mem_selected_iff.mp hp)

/-- Labelled hereditary normalization: it applies also to every finite subset
of the coding image of a diary, since the subset is arbitrary. -/
theorem code_image (f : RayStrongMap) (C : Finset Word) {w : Word} (hw : w ∈ C) :
    code (C.image f.map) (f.map w) = code C w := by
  classical
  have hf : StrictMono f.level := fun _ _ h => f.level_strict h
  unfold code
  rw [selected_image, f.length_map, rank_image _ _ hf]
  exact project_image f (selected C) (selected_nonempty ⟨w, hw⟩) w
    (essential_subset_selected C (length_mem_essential hw)) _ le_rfl

theorem codes_image (f : RayStrongMap) (C : Finset Word) :
    codes (C.image f.map) = codes C := by
  classical
  unfold codes
  rw [Finset.image_image]
  apply Finset.image_congr
  intro w hw
  exact code_image f C hw

end AllThoseBigRamsey.Pseudotree.GeneralizedNormalization
