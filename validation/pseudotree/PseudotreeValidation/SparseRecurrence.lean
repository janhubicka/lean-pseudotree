import PseudotreeValidation.ReservoirTransitions
import PseudotreeValidation.GeneralizedNormalization

/-! Run the rational-reservoir construction through all levels of the
actual sparse tree. The resulting critical self-map realizes the coding
set in an arbitrary reduct self-copy and preserves all normalized types. -/

namespace AllThoseBigRamsey.Pseudotree.Reservoir
open RayEmbeddings RayMapModel
open SparseNormalization (Tree Point critical critical_length point_at_level tree_children)
open scoped FirstOrder

def sparseSource : Source where
  nodes := {w | Tree w}
  codes := {w | Point w}
  root_mem := by
    change Tree []
    have h := (CriticalCopies.criticalNode 0).property
    have hz : critical 0 = [] := List.length_eq_zero_iff.mp (critical_length 0)
    simpa only [CriticalCopies.criticalNode, hz] using h
  prefix_closed := by
    intro w hw j _
    exact SparseNormalization.tree_prefix hw (List.take_prefix _ _)
  kind := fun j => if j % 3 = 2 then .code else .split
  critical := critical
  rule := by
    intro j
    refine ⟨(CriticalCopies.criticalNode j).property, critical_length j, ?_, ?_⟩
    · intro w hw hlen
      change Point w ↔ w = critical j ∧
        (if j % 3 = 2 then PaperKind.code else PaperKind.split).coded = true
      rw [point_at_level hlen]
      by_cases hm : j % 3 = 2 <;> simp [hm, PaperKind.coded]
    · intro w hw hlen a
      change Tree (child w a) ↔
        localChild (critical j) (if j % 3 = 2 then PaperKind.code else PaperKind.split).special w a
      rw [tree_children j w hw hlen a]
      by_cases hm : j % 3 = 2 <;> by_cases hc : w = critical j <;>
        simp only [localChild, hm, hc, if_true, if_false, PaperKind.special]

/-- An infinite critical map into any prescribed sparse reduct copy. No
homogeneity or Ramsey property of the diary expansion is assumed. -/
theorem recurrence (f : Target)
    (hsparse : ∀ x ∈ Set.range f, Sparse.InSparse (fromBlocks x)) :
    ∃ X : CriticalCopies.CriticalMap, ∀ w, Point w →
      DiaryChains.model ((CriticalCopies.total X).map w) ∈ Set.range f := by
  classical
  let D := sparseSource
  let targets : Word → Target := fun _ => f
  have ht : SparseTargets targets := fun _ x hx => hsparse x hx
  let P0 := Classical.choice (initial D targets)
  let pick (j : Nat) (P : Layer D targets j) : Step P :=
    Classical.choice (exists_step P ht (fun _ _ _ => rfl))
  let P := layerSequence D targets P0 pick
  let S (j : Nat) : Step (P j) := pick j (P j)
  let levels (j : Nat) := (S j).level
  have hlevels : StrictMono levels :=
    strictMono_nat_of_lt_succ (fun j => (S j).upper.trans_le (S (j+1)).lower)
  let e : CriticalCopies.Node → Word := fun s =>
    ((S s.val.length).roots ⟨s.val, s.property, rfl⟩).map toFin
  have eat (j : Nat) (u : Level D j) :
      e ⟨u.val, u.property.1⟩ = ((S j).roots u).map toFin := by
    rcases u with ⟨u, hu, hlen⟩
    subst j
    rfl
  have elength (s : CriticalCopies.Node) : (e s).length = levels s.val.length :=
    (List.length_map _).trans ((S s.val.length).root_length ⟨s.val,s.property,rfl⟩)
  have estep : ∀ s a (ha : Tree (s ++ [a])), ∃ b : Word,
      e ⟨s ++ [a],ha⟩ = e (CriticalCopies.parentNode s a ha) ++ a :: b ∧
        (a ≠ 1 → Binary b) := by
    intro s a ha
    let u : Level D s.length :=
      ⟨s, SparseNormalization.tree_prefix ha (List.prefix_append s [a]), rfl⟩
    let v : Level D (s.length+1) := childNode u a ha
    obtain ⟨b,hb,hb_binary⟩ := (S s.length).edge u a ha
    obtain ⟨c,hc_binary,hc⟩ := (S (s.length+1)).root_binary v
    have hroots : (S (s.length+1)).roots v =
        (S s.length).roots u ++ toLetter a :: (b ++ c) := by
      rw [hc]
      change (S s.length).next.prefixes (childNode u a ha) ++ c = _
      rw [hb]
      simp only [List.append_assoc, List.cons_append]
    refine ⟨(b ++ c).map toFin, ?_, ?_⟩
    · change e ⟨v.val,v.property.1⟩ =
        e ⟨u.val,u.property.1⟩ ++ a :: (b ++ c).map toFin
      rw [eat (s.length+1) v, eat s.length u, hroots]
      simp only [List.map_append, List.map_cons, toFin_toLetter]
    · intro ha1
      apply (binary_map _).mpr
      intro x hx hx1
      have hnot : TernaryLetter.one ∉ b ++ c := by
        simp only [List.mem_append, not_or]
        exact ⟨hb_binary ha1, hc_binary⟩
      exact hnot (hx1 ▸ hx)
  have ecritical (j : Nat) :
      e (CriticalCopies.criticalNode j) = critical (levels j) := by
    change e ⟨(criticalAt D j).val, (criticalAt D j).property.1⟩ = _
    rw [eat j (criticalAt D j), (S j).critical]
    rfl
  have ecritLength (j : Nat) :
      (e (CriticalCopies.criticalNode j)).length = levels j := by
    rw [elength, CriticalCopies.criticalNode_length]
  let X : CriticalCopies.CriticalMap := {
    map := e
    level_strict := by
      intro i j hij
      change (e (CriticalCopies.criticalNode i)).length <
        (e (CriticalCopies.criticalNode j)).length
      rw [ecritLength, ecritLength]
      exact hlevels hij
    length_map := by
      intro s
      rw [elength, ecritLength]
    step := estep
    maps_tree := by
      intro s
      change Sparse.InTree ((e s).map toLetter)
      simpa only [e, List.map_map, Function.comp_def, toLetter_toFin,
        List.map_id_fun', id_eq] using (S s.val.length).root_tree ⟨s.val,s.property,rfl⟩
    critical_image := by
      intro j
      rw [ecritLength]
      exact ecritical j
    phase := by
      intro j
      rw [ecritLength]
      have h := (S j).phase
      change levels j % 3 = 2 ↔ (if j % 3 = 2 then PaperKind.code else PaperKind.split) ≠ .split at h
      by_cases hm : j % 3 = 2 <;> simpa [hm] using h }
  refine ⟨X, ?_⟩
  intro w hw
  let u : CriticalCopies.Node := ⟨w, SparseNormalization.point_tree hw⟩
  rw [show (CriticalCopies.total X).map w = e u from CriticalCopies.total_agrees X u]
  change toBlocks ((((S w.length).roots ⟨w,u.property,rfl⟩).map toFin).map toLetter) ∈ Set.range f
  simpa only [List.map_map, Function.comp_def, toLetter_toFin, List.map_id_fun', id_eq] using
    (S w.length).coding ⟨w,u.property,rfl⟩ hw

/-- Recurrence of all finite normalized types simultaneously. This is the
literal code-set formulation, before packaging the expansion language. -/
theorem recurrent_code_sets (f : Target)
    (hsparse : ∀ x ∈ Set.range f, Sparse.InSparse (fromBlocks x)) :
    ∃ X : CriticalCopies.CriticalMap,
      (∀ w, Point w → DiaryChains.model ((CriticalCopies.total X).map w) ∈ Set.range f) ∧
      ∀ C : Finset Word,
        GeneralizedNormalization.codes (C.image (CriticalCopies.total X).map) =
          GeneralizedNormalization.codes C := by
  obtain ⟨X,hX⟩ := recurrence f hsparse
  exact ⟨X,hX,GeneralizedNormalization.codes_image (CriticalCopies.total X)⟩

end AllThoseBigRamsey.Pseudotree.Reservoir
