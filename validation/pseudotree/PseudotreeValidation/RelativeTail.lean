import PseudotreeValidation.CriticalPullback

/-! A common interface for gluing a prescribed critical prefix to a
critical tail. Neither FIFO labels nor reservoir choices occur in the
interface. The incoming edge is a separate, explicit local condition. -/
namespace AllThoseBigRamsey.Pseudotree.CriticalCopies
open RayEmbeddings
open SparseNormalization (critical)

structure RelativeTail {h : Nat} (e : FiniteCritical h) where
  map : Node → Word
  level : Nat → Nat
  after : e.level (h-1) < level h
  strict : ∀ {i j}, h ≤ i → i < j → level i < level j
  length_map : ∀ u : Node, h ≤ u.val.length → (map u).length = level u.val.length
  tree : ∀ u : Node, h ≤ u.val.length → SparseNormalization.Tree (map u)
  critical_image : ∀ j, h ≤ j → map (criticalNode j) = critical (level j)
  phase : ∀ j, h ≤ j → (level j % 3 = 2 ↔ j % 3 = 2)
  step : ∀ s a (hs : SparseNormalization.Tree (s ++ [a])), h ≤ s.length →
    ∃ p : Word, map ⟨s ++ [a],hs⟩ = map (parentNode s a hs) ++ a :: p ∧
      (a ≠ 1 → Binary p)
  boundary : ∀ s a (hs : SparseNormalization.Tree (s ++ [a])), (s ++ [a]).length = h →
    ∃ p : Word, map ⟨s ++ [a],hs⟩ = e.map (parentNode s a hs) ++ a :: p ∧
      (a ≠ 1 → Binary p)

namespace RelativeTail

def joined {e : FiniteCritical h} (T : RelativeTail e) (u : Node) : Word :=
  if u.val.length < h then e.map u else T.map u

def schedule {e : FiniteCritical h} (T : RelativeTail e) (j : Nat) : Nat :=
  if j < h then e.level j else T.level j

theorem joined_length {e : FiniteCritical h} (T : RelativeTail e) (u : Node) :
    (T.joined u).length = T.schedule u.val.length := by
  by_cases hu : u.val.length < h
  · simpa only [joined,schedule,if_pos hu] using e.length_map u hu
  · simpa only [joined,schedule,if_neg hu] using T.length_map u (by omega)

theorem schedule_strict {e : FiniteCritical h} (T : RelativeTail e) (hh : 0 < h) :
    StrictMono T.schedule := by
  intro i j hij
  by_cases hj : j < h
  · simpa only [schedule,if_pos (hij.trans hj),if_pos hj] using e.level_strict hij hj
  · by_cases hi : i < h
    · simp only [schedule,if_pos hi,if_neg hj]
      have hlo : e.level i ≤ e.level (h-1) := by
        rcases lt_or_eq_of_le (show i ≤ h-1 by omega) with hlt | heq
        · exact (e.level_strict hlt (by omega)).le
        · subst i
          exact le_rfl
      have hhi : T.level h ≤ T.level j := by
        rcases lt_or_eq_of_le (show h ≤ j by omega) with hlt | heq
        · exact (T.strict le_rfl hlt).le
        · subst j
          exact le_rfl
      exact hlo.trans_lt (T.after.trans_le hhi)
    · simpa only [schedule,if_neg hi,if_neg hj] using T.strict (by omega : h ≤ i) hij

/-- Glue the actual prefix and tail. All phase and ray constraints,
including the crossing edge, are checked locally. -/
def assemble {e : FiniteCritical h} (T : RelativeTail e) (hh : 0 < h) : CriticalMap where
  map := T.joined
  level_strict := by
    intro i j hij
    change (T.joined (criticalNode i)).length < (T.joined (criticalNode j)).length
    rw [joined_length,joined_length,criticalNode_length,criticalNode_length]
    exact T.schedule_strict hh hij
  length_map := by
    intro u
    rw [joined_length,joined_length,criticalNode_length]
  step := by
    intro s a hs
    let v : Node := ⟨s ++ [a],hs⟩
    let u : Node := parentNode s a hs
    have hv : v.val.length = s.length+1 := by simp [v]
    have hu : u.val.length = s.length := rfl
    change ∃ p : Word, T.joined v = T.joined u ++ a :: p ∧ (a ≠ 1 → Binary p)
    by_cases hchild : v.val.length < h
    · have hparent : u.val.length < h := by omega
      simpa only [joined,if_pos hchild,if_pos hparent] using e.step s a hs hchild
    · by_cases hparent : u.val.length < h
      · have hbound : v.val.length = h := by omega
        simpa only [joined,if_neg hchild,if_pos hparent] using T.boundary s a hs hbound
      · simpa only [joined,if_neg hchild,if_neg hparent] using T.step s a hs (by omega)
  maps_tree := by
    intro u
    by_cases hu : u.val.length < h
    · simpa only [joined,if_pos hu] using e.maps_tree u hu
    · simpa only [joined,if_neg hu] using T.tree u (by omega)
  critical_image := by
    intro j
    rw [joined_length,criticalNode_length]
    by_cases hj : j < h
    · simpa only [joined,criticalNode_length,schedule,if_pos hj,FiniteCritical.level] using
        e.critical_image j hj
    · simpa only [joined,criticalNode_length,schedule,if_neg hj] using T.critical_image j (by omega)
  phase := by
    intro j
    rw [joined_length,criticalNode_length]
    by_cases hj : j < h
    · simpa only [schedule,if_pos hj,FiniteCritical.level] using e.phase j hj
    · simpa only [schedule,if_neg hj] using T.phase j (by omega)

theorem assemble_extends {e : FiniteCritical h} (T : RelativeTail e) (hh : 0 < h) :
    Extends (T.assemble hh) e := by
  intro u hu
  change T.joined u = e.map u
  exact if_pos hu

theorem assemble_tail {e : FiniteCritical h} (T : RelativeTail e) (hh : 0 < h)
    (u : Node) (hu : h ≤ u.val.length) :
    (T.assemble hh).map u = T.map u := by
  change T.joined u = T.map u
  exact if_neg (Nat.not_lt_of_ge hu)

end RelativeTail
end AllThoseBigRamsey.Pseudotree.CriticalCopies
