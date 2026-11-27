import PseudotreeValidation.ChartReservoir

/-! The original-coordinate specialization of the single chart-independent
reservoir construction. Relative critical-copy amalgamation uses these
abbreviations; the proof of the transitions is not duplicated. -/
namespace AllThoseBigRamsey.Pseudotree.Reservoir
open RayEmbeddings RayMapModel
open scoped FirstOrder

abbrev SparseTargets (f : Word → Target) : Prop :=
  ChartReservoir.SparseTargets ReservoirChart.original f

abbrev Layer (D : Source) (f : Word → Target) (j : Nat) :=
  ChartReservoir.Layer ReservoirChart.original D f j

abbrev Step {D : Source} {f : Word → Target} {j : Nat} (P : Layer D f j) :=
  ChartReservoir.Step P

theorem initial (D : Source) (f : Word → Target) :
    Nonempty (Layer D f 0) :=
  ChartReservoir.initial ReservoirChart.original D f

theorem exists_step {D : Source} {f : Word → Target} {j : Nat}
    (P : Layer D f j) (hsparse : SparseTargets f)
    (stable : ∀ (u : Level D j) a, child u.val a ∈ D.nodes →
      f (child u.val a) = f u.val) : Nonempty (Step P) :=
  ChartReservoir.exists_step P hsparse stable

noncomputable def layerSequence (D : Source) (f : Word → Target)
    (P0 : Layer D f 0) (pick : ∀ j, (P : Layer D f j) → Step P) :
    (j : Nat) → Layer D f j :=
  ChartReservoir.layerSequence ReservoirChart.original D f P0 pick

end AllThoseBigRamsey.Pseudotree.Reservoir
