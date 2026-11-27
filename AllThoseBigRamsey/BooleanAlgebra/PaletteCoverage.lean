import Std

/-!
# Palette lower bounds from completion of witnesses

The finite counting step in the relative Boolean-front obstruction is:
if every one of `q` values occurs in some realized palette, each palette
contains at most `M` values, and `d` palettes suffice, then `q ≤ d * M`.
The last theorem transports this bound through an explicit completion
relation from witnesses to actual occurrences.  Recurrence and Boolean
completion are hypotheses; no infinite Ramsey or recurrence axiom is added.
-/

namespace AllThoseBigRamsey.BooleanAlgebra.PaletteCoverage

private theorem nodup_length_le (xs ys : List α)
    (hx : xs.Nodup) (hsub : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
      obtain ⟨ha, hxs⟩ := List.nodup_cons.mp hx
      have hay : a ∈ ys := hsub (by simp)
      obtain ⟨left, right, rfl⟩ := List.append_of_mem hay
      have hsub' : xs ⊆ left ++ right := by
        intro x hx
        have hxa : x ≠ a := by
          intro h
          exact ha (h ▸ hx)
        have hmem := hsub (List.mem_cons_of_mem a hx)
        rcases List.mem_append.mp hmem with hl | hr
        · exact List.mem_append.mpr (Or.inl hl)
        · rcases List.mem_cons.mp hr with h | h
          · exact False.elim (hxa h)
          · exact List.mem_append.mpr (Or.inr h)
      have hbound := ih (left ++ right) hxs hsub'
      simp only [List.length_append, List.length_cons] at *
      omega

theorem flatten_length_le (palettes : List (List α)) (M : Nat)
    (hsize : ∀ p ∈ palettes, p.length ≤ M) :
    palettes.flatten.length ≤ palettes.length * M := by
  induction palettes with
  | nil => simp
  | cons p ps ih =>
      have hp := hsize p (by simp)
      have hps := ih (fun q hq => hsize q (by simp [hq]))
      simp only [List.flatten_cons, List.length_append, List.length_cons,
        Nat.add_mul, Nat.one_mul]
      omega

/-- Coverage of distinct values forces a lower bound on the number of
palettes.  In an application, `palettes` enumerates the distinct realized
colours.  The inequality also holds for lists with repeated palettes.
-/
theorem palette_cover_bound
    (values : List α) (palettes : List (List α)) (M : Nat)
    (hvalues : values.Nodup)
    (hcover : ∀ a ∈ values, ∃ p ∈ palettes, a ∈ p)
    (hsize : ∀ p ∈ palettes, p.length ≤ M) :
    values.length ≤ palettes.length * M := by
  have hsub : values ⊆ palettes.flatten := by
    intro a ha
    exact List.mem_flatten.mpr (hcover a ha)
  exact Nat.le_trans (nodup_length_le values palettes.flatten hvalues hsub)
    (flatten_length_le palettes M hsize)

/-- A recurrent value is completed to an admissible occurrence; its value
appears in that occurrence's palette.  Thus no list of small palettes can
cover all admissible occurrences unless it meets the quantitative bound.
-/
theorem completed_occurrences_palette_bound
    (values : List α) (colours : List (List α)) (M : Nat)
    (evaluate : Witness → α) (palette : Occurrence → List α)
    (admissible : Occurrence → Prop)
    (hvalues : values.Nodup)
    (hrecur : ∀ a ∈ values, ∃ w, evaluate w = a)
    (hcomplete : ∀ w, ∃ o, admissible o ∧ evaluate w ∈ palette o)
    (hcolours : ∀ o, admissible o → palette o ∈ colours)
    (hsize : ∀ p ∈ colours, p.length ≤ M) :
    values.length ≤ colours.length * M := by
  apply palette_cover_bound values colours M hvalues ?_ hsize
  intro a ha
  obtain ⟨w, hw⟩ := hrecur a ha
  obtain ⟨o, ho, hwo⟩ := hcomplete w
  exact ⟨palette o, hcolours o ho, hw ▸ hwo⟩

end AllThoseBigRamsey.BooleanAlgebra.PaletteCoverage
