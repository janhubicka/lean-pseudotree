import AllThoseBigRamsey.BooleanAlgebra.Boundary

/-!
# Finite support and germ states

An interval cell has a nonempty finite set of atom labels occurring in it,
together with its left and right limiting labels.  The support is represented
by a list, with all semantic conditions expressed through membership, so its
order and repetitions carry no mathematical meaning.

The results prove that quotienting the atom labels preserves valid states,
local splits and terminal states.  In particular the data restrict coherently
to Boolean subalgebras.  No infinite realization or Ramsey assertion is assumed.
-/

namespace AllThoseBigRamsey.BooleanAlgebra

structure Frontier (α : Type u) where
  left : α
  support : List α
  right : α

namespace Frontier

def Valid (p : Frontier α) : Prop := p.left ∈ p.support ∧ p.right ∈ p.support

def coarsen (f : α → β) (p : Frontier α) : Frontier β :=
  ⟨f p.left, p.support.map f, f p.right⟩

def Split (p l r : Frontier α) : Prop :=
  p.left = l.left ∧ p.right = r.right ∧
    ∀ a, a ∈ p.support ↔ a ∈ l.support ∨ a ∈ r.support

def Terminal (p : Frontier α) : Prop := ∀ a, a ∈ p.support → a = p.left

theorem coarsen_id (p : Frontier α) : coarsen id p = p := by
  cases p
  simp [coarsen]

theorem coarsen_comp (f : α → β) (g : β → γ) (p : Frontier α) :
    coarsen g (coarsen f p) = coarsen (fun a => g (f a)) p := by
  simp [coarsen, List.map_map]

theorem valid_coarsen (f : α → β) (p : Frontier α) (hp : p.Valid) :
    (coarsen f p).Valid := by
  rcases hp with ⟨hl, hr⟩
  exact ⟨List.mem_map.mpr ⟨p.left, hl, rfl⟩,
    List.mem_map.mpr ⟨p.right, hr, rfl⟩⟩

theorem split_coarsen (f : α → β) (p l r : Frontier α) (h : Split p l r) :
    Split (coarsen f p) (coarsen f l) (coarsen f r) := by
  rcases h with ⟨hl, hr, hs⟩
  refine ⟨congrArg f hl, congrArg f hr, ?_⟩
  intro b
  constructor
  · intro hb
    rcases List.mem_map.mp hb with ⟨a, ha, hab⟩
    rcases (hs a).mp ha with ha | ha
    · exact Or.inl (List.mem_map.mpr ⟨a, ha, hab⟩)
    · exact Or.inr (List.mem_map.mpr ⟨a, ha, hab⟩)
  · intro hb
    rcases hb with hb | hb
    · rcases List.mem_map.mp hb with ⟨a, ha, hab⟩
      exact List.mem_map.mpr ⟨a, (hs a).mpr (Or.inl ha), hab⟩
    · rcases List.mem_map.mp hb with ⟨a, ha, hab⟩
      exact List.mem_map.mpr ⟨a, (hs a).mpr (Or.inr ha), hab⟩

theorem terminal_coarsen (f : α → β) (p : Frontier α) (hp : p.Terminal) :
    (coarsen f p).Terminal := by
  intro b hb
  rcases List.mem_map.mp hb with ⟨a, ha, hab⟩
  calc
    b = f a := hab.symm
    _ = f p.left := congrArg f (hp a ha)

theorem terminal_germs (p : Frontier α) (hv : p.Valid) (ht : p.Terminal) :
    p.right = p.left := ht p.right hv.2

/-- The cut introduced by splitting a cell is read from the facing germs. -/
def cut [DecidableEq α] (l r : Frontier α) : Option (Event α) :=
  coarsenEvent id (l.right, r.left)

theorem cut_coarsen [DecidableEq α] [DecidableEq β]
    (f : α → β) (l r : Frontier α) :
    (cut l r).bind (coarsenEvent f) = cut (coarsen f l) (coarsen f r) := by
  by_cases h : l.right = r.left
  · simp [cut, coarsen, coarsenEvent, h]
  · by_cases hf : f l.right = f r.left
    · simp [cut, coarsen, coarsenEvent, h, hf]
    · simp [cut, coarsen, coarsenEvent, h, hf]

end Frontier
end AllThoseBigRamsey.BooleanAlgebra
