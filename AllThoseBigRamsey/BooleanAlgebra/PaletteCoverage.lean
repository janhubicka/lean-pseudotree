import Std

/-!
# Palette lower bounds from completion of witnesses

The finite counting step in the relative Boolean-front obstruction is:
if every one of `q` values occurs in some realized palette, each palette
contains at most `M` values, and `d` palettes suffice, then `q ≤ d * M`.
The last theorem transports this bound through an explicit completion
relation from witnesses to actual occurrences.  Recurrence and Boolean
completion are hypotheses; no infinite Ramsey or recurrence axiom is added.

For an avoiding finite Boolean queue leaf, a completed witness may occur in
one of finitely many translated slices. The final two theorems allow an
arbitrary indexed family of maps on palette entries and prove the extra
factor given by the number of such maps. Injectivity of the maps is not
needed. In the Boolean application they are subtraction by the finitely
many offsets associated with the old finite algebra.
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

/-- A finite family of images of small palettes covers at most the product
of the numbers of maps and palettes and the palette-size bound. The maps
may be arbitrary, and repeated indices or palettes only weaken the bound.
-/
theorem shifted_palette_cover_bound
    (values : List α) (palettes : List (List β)) (shifts : List Index)
    (M : Nat) (shift : Index → β → α)
    (hvalues : values.Nodup)
    (hcover : ∀ a ∈ values, ∃ i ∈ shifts, ∃ p ∈ palettes,
      ∃ b ∈ p, shift i b = a)
    (hsize : ∀ p ∈ palettes, p.length ≤ M) :
    values.length ≤ shifts.length * palettes.length * M := by
  let shiftedPalettes := shifts.flatMap fun i =>
    palettes.map fun p => p.map (shift i)
  have hcover' : ∀ a ∈ values, ∃ p ∈ shiftedPalettes, a ∈ p := by
    intro a ha
    obtain ⟨i, hi, p, hp, b, hb, hba⟩ := hcover a ha
    refine ⟨p.map (shift i), ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      exact ⟨i, hi, List.mem_map.mpr ⟨p, hp, rfl⟩⟩
    · exact List.mem_map.mpr ⟨b, hb, hba⟩
  have hsize' : ∀ p ∈ shiftedPalettes, p.length ≤ M := by
    intro p hp
    obtain ⟨i, _, hip⟩ := List.mem_flatMap.mp hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hip
    simpa using hsize q hq
  have hlength : shiftedPalettes.length = shifts.length * palettes.length := by
    have hlengthAll : ∀ js : List Index,
        (js.flatMap fun i => palettes.map fun p => p.map (shift i)).length =
          js.length * palettes.length := by
      intro js
      induction js with
      | nil => simp
      | cons i is ih =>
          simp only [List.flatMap_cons, List.length_append, List.length_map,
            List.length_cons, Nat.add_mul, Nat.one_mul]
          omega
    exact hlengthAll shifts
  have hbound := palette_cover_bound values shiftedPalettes M
    hvalues hcover' hsize'
  simpa only [hlength] using hbound

/-- Transport the shifted-palette estimate through explicit recurrence and
completion hypotheses. A completed occurrence contains a palette entry
which maps to the witness value under one of the finitely listed maps.
No queue, unavoidability, or infinite recurrence statement is assumed by
the library beyond the displayed hypotheses.
-/
theorem completed_occurrences_shifted_palette_bound
    (values : List α) (colours : List (List β)) (shifts : List Index)
    (M : Nat) (shift : Index → β → α)
    (evaluate : Witness → α) (palette : Occurrence → List β)
    (admissible : Occurrence → Prop)
    (hvalues : values.Nodup)
    (hrecur : ∀ a ∈ values, ∃ w, evaluate w = a)
    (hcomplete : ∀ w, ∃ o, admissible o ∧
      ∃ i ∈ shifts, ∃ b ∈ palette o, shift i b = evaluate w)
    (hcolours : ∀ o, admissible o → palette o ∈ colours)
    (hsize : ∀ p ∈ colours, p.length ≤ M) :
    values.length ≤ shifts.length * colours.length * M := by
  apply shifted_palette_cover_bound values colours shifts M shift hvalues ?_ hsize
  intro a ha
  obtain ⟨w, hw⟩ := hrecur a ha
  obtain ⟨o, ho, i, hi, b, hb, hbw⟩ := hcomplete w
  exact ⟨i, hi, palette o, hcolours o ho, b, hb, hbw.trans hw⟩

end AllThoseBigRamsey.BooleanAlgebra.PaletteCoverage
