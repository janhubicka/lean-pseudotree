import Std

/-!
# Transport of the native endpoint Ramsey theorem

The concrete application identifies occurrences of a fixed expanded Boolean
algebra with occurrences of its finite Devlin endpoint structure.  Endpoint
self-embeddings lift to Boolean self-embeddings, and this identification is
equivariant.  The first theorem proves the resulting IRT transfer.

The remaining theorems prove finite iteration for occurrence families acted on
by a common composition operation.  The final factorization uses a palette
indexed by the chosen types, expressing the upper bound of one color per type.

All source Ramsey properties, occurrence equivalences, and action laws are
explicit hypotheses.  This file does not axiomatize or prove Devlin's theorem,
nor does it prove the concrete interval representation or ambient recurrence.
-/

namespace AllThoseBigRamsey.BooleanAlgebra.DevlinTransfer

/-- Two presentations of the same family of finite occurrences. -/
structure OccurrenceEquiv (X : Type u) (Y : Type v) where
  toTarget : X → Y
  toSource : Y → X
  target_source : ∀ y, toTarget (toSource y) = y
  source_target : ∀ x, toSource (toTarget x) = x

def Homogeneous (act : E → X → X) (c : X → C) (e : E) : Prop :=
  ∀ x y, c (act e x) = c (act e y)

def HasIRT (act : E → X → X) : Prop :=
  ∀ (r : Nat) (c : X → Fin r), ∃ e, Homogeneous act c e

/-- An equivariant occurrence equivalence transports a source IRT statement.
The source and target spaces of self-embeddings need not be identical. -/
theorem transfer_irt
    (sourceAct : E → X → X) (targetAct : F → Y → Y)
    (occ : OccurrenceEquiv X Y) (lift : E → F)
    (equivariant : ∀ e x,
      occ.toTarget (sourceAct e x) = targetAct (lift e) (occ.toTarget x))
    (sourceIRT : HasIRT sourceAct) : HasIRT targetAct := by
  intro r c
  obtain ⟨e, he⟩ := sourceIRT r (fun x => c (occ.toTarget x))
  refine ⟨lift e, ?_⟩
  intro y z
  have h := he (occ.toSource y) (occ.toSource z)
  simpa only [equivariant, occ.target_source] using h

/-- A further self-embedding preserves homogeneity already obtained. -/
theorem homogeneous_comp
    (act : E → X → X) (comp : E → E → E)
    (act_comp : ∀ e f x, act (comp e f) x = act e (act f x))
    (c : X → C) (e f : E) (h : Homogeneous act c e) :
    Homogeneous act c (comp e f) := by
  intro x y
  simpa only [act_comp] using h (act f x) (act f y)

/-- Finite iteration of one-type IRT for a common family of self-embeddings.
Only the explicitly stated action-of-composition law is needed. -/
theorem finite_family
    (Occurrence : I → Type u) (act : ∀ i, E → Occurrence i → Occurrence i)
    (unit : E) (comp : E → E → E)
    (act_comp : ∀ i e f x, act i (comp e f) x = act i e (act i f x))
    (localIRT : ∀ i, HasIRT (act i))
    (types : List I) (r : Nat) (c : ∀ i, Occurrence i → Fin r) :
    ∃ e, ∀ i, i ∈ types → Homogeneous (act i) (c i) e := by
  induction types generalizing c with
  | nil => exact ⟨unit, by simp⟩
  | cons i types ih =>
      obtain ⟨e, he⟩ := localIRT i r (c i)
      obtain ⟨f, hf⟩ := ih (fun j x => c j (act j e x))
      refine ⟨comp e f, ?_⟩
      intro j hj
      rcases List.mem_cons.mp hj with hji | hj
      · subst j
        exact homogeneous_comp (act i) comp (act_comp i) (c i) e f he
      · intro x y
        have h := hf j hj x y
        simpa only [act_comp] using h

/-- A finite family of `n` nonempty occurrence types admits a coloring which
factors through its type index after one self-embedding.  Thus at most `n`
palette values remain on their union in the concrete application. -/
theorem finite_family_factorization
    (n : Nat) (Occurrence : Fin n → Type u)
    (act : ∀ i, E → Occurrence i → Occurrence i)
    (unit : E) (comp : E → E → E)
    (act_comp : ∀ i e f x, act i (comp e f) x = act i e (act i f x))
    (localIRT : ∀ i, HasIRT (act i))
    (representative : ∀ i, Occurrence i)
    (r : Nat) (c : ∀ i, Occurrence i → Fin r) :
    ∃ (e : E) (palette : Fin n → Fin r),
      ∀ i x, c i (act i e x) = palette i := by
  obtain ⟨e, he⟩ := finite_family Occurrence act unit comp act_comp localIRT
    (List.finRange n) r c
  refine ⟨e, (fun i => c i (act i e (representative i))), ?_⟩
  intro i x
  exact he i (by simp) x (representative i)

end AllThoseBigRamsey.BooleanAlgebra.DevlinTransfer
