import Std

/-!
# Boundary events under Boolean atom quotients

A directed event `(a,b)` records the atom immediately before and immediately
after a cut.  Coarsening the atom labels deletes the event precisely when the
two labels become equal.  These elementary identities are the functorial core
of the proposed Boolean diary; they do not assert a Ramsey theorem.
-/

namespace AllThoseBigRamsey.BooleanAlgebra

abbrev Event (α : Type u) := α × α

def coarsenEvent [DecidableEq β] (f : α → β) (e : Event α) : Option (Event β) :=
  if f e.1 = f e.2 then none else some (f e.1, f e.2)

def coarsenWord [DecidableEq β] (f : α → β) (w : List (Event α)) : List (Event β) :=
  w.filterMap (coarsenEvent f)

theorem coarsenEvent_comp [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : β → γ) (e : Event α) :
    (coarsenEvent f e).bind (coarsenEvent g) =
      coarsenEvent (fun a => g (f a)) e := by
  by_cases h : f e.1 = f e.2
  · simp [coarsenEvent, h]
  · simp [coarsenEvent, h]

theorem coarsenWord_comp [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : β → γ) (w : List (Event α)) :
    coarsenWord g (coarsenWord f w) =
      coarsenWord (fun a => g (f a)) w := by
  induction w with
  | nil => rfl
  | cons e w ih =>
      simp only [coarsenWord, List.filterMap_cons] at *
      have hc := coarsenEvent_comp f g e
      cases he : coarsenEvent f e with
      | none =>
          simp only [he, Option.bind_none] at hc
          simp [← hc, ih]
      | some e' =>
          simp only [he, Option.bind_some] at hc
          simp [List.filterMap_cons, ← hc, ih]

theorem coarsenEvent_none_iff [DecidableEq β] (f : α → β) (e : Event α) :
    coarsenEvent f e = none ↔ f e.1 = f e.2 := by
  simp [coarsenEvent]

theorem coarsenEvent_some_iff [DecidableEq β] (f : α → β)
    (e : Event α) (d : Event β) :
    coarsenEvent f e = some d ↔
      f e.1 ≠ f e.2 ∧ d = (f e.1, f e.2) := by
  by_cases h : f e.1 = f e.2
  · simp [coarsenEvent, h]
  · simp [coarsenEvent, h, eq_comm]

/-- Boundary events of a finite sequence, with `a` its first label. -/
def boundaryFrom [DecidableEq α] (a : α) : List α → List (Event α)
  | [] => []
  | b :: w =>
      if a = b then boundaryFrom b w else (a,b) :: boundaryFrom b w

/-- Changing the labels and then extracting boundaries is the same as
extracting boundaries and deleting the events collapsed by the quotient. -/
theorem boundaryFrom_coarsen [DecidableEq α] [DecidableEq β]
    (f : α → β) (a : α) (w : List α) :
    coarsenWord f (boundaryFrom a w) = boundaryFrom (f a) (w.map f) := by
  induction w generalizing a with
  | nil => rfl
  | cons b w ih =>
      have ihb := ih b
      simp only [coarsenWord] at ihb
      by_cases hab : a = b
      · subst b
        simp [boundaryFrom, ih]
      · by_cases hfab : f a = f b
        · simp [boundaryFrom, hab, coarsenWord, coarsenEvent, hfab,
            ihb]
        · simp [boundaryFrom, hab, coarsenWord, coarsenEvent, hfab,
            ihb]

/-- Every recorded event is a genuine transition. -/
theorem boundaryFrom_ne [DecidableEq α] (a : α) (w : List α)
    (e : Event α) (h : e ∈ boundaryFrom a w) : e.1 ≠ e.2 := by
  induction w generalizing a with
  | nil => simp [boundaryFrom] at h
  | cons b w ih =>
      by_cases hab : a = b
      · simp only [boundaryFrom, hab, ↓reduceIte] at h
        exact ih b h
      · simp only [boundaryFrom, hab, ↓reduceIte, List.mem_cons] at h
        rcases h with h | h
        · subst e
          exact hab
        · exact ih b h

end AllThoseBigRamsey.BooleanAlgebra
