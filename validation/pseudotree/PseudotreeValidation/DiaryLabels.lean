import PseudotreeValidation.DiaryRestriction

/-!
# Label recovery from the length order and the diary relation

A diary relation in the manuscript names the unlabelled normalized
code set, on the increasing enumeration of a finite meet-closed
substructure. The order of code lengths is preserved by normalization.
Thus the unlabelled relation and the length order together determine
the labelled normalized map. This proof needs neither reconstruction
nor any Ramsey-space axiom.
-/
namespace AllThoseBigRamsey.Pseudotree
open RayEmbeddings
open SparseNormalization (Point point_unique_length)
open GeneralizedNormalization (code codes rayMap rayMap_code)

namespace GeneralizedNormalization

/-- The projection may shorten words but never changes their length
order. This is a consequence of the already checked inverse map. -/
theorem code_length_lt_iff {C : Finset Word} (hC : C.Nonempty)
    {s t : Word} (hs : s ∈ C) (ht : t ∈ C) :
    (code C s).length < (code C t).length ↔ s.length < t.length := by
  let g := rayMap hC
  have hmono : StrictMono g.level := fun _ _ h => g.level_strict h
  have h₁ : g.level (code C s).length = s.length := by
    have hm : g.map (code C s) = s := rayMap_code hC hs
    rw [← g.length_map,hm]
  have h₂ : g.level (code C t).length = t.length := by
    have hm : g.map (code C t) = t := rayMap_code hC ht
    rw [← g.length_map,hm]
  rw [← h₁,← h₂]
  exact hmono.lt_iff_lt.symm

/-- Uniqueness of two length-order-preserving enumerations of one finite
code set, indexed by a finite subset of the actual coding points.
The strong induction works on source lengths, so no choice of a
linear order on the reduct is necessary. -/
theorem ordered_image_unique {C : Finset Word} (hC : ∀ w ∈ C, Point w)
    (a b : Word → Word)
    (ha : ∀ s ∈ C, ∀ t ∈ C, s.length < t.length → (a s).length < (a t).length)
    (hb : ∀ s ∈ C, ∀ t ∈ C, s.length < t.length → (b s).length < (b t).length)
    (he : C.image a = C.image b) : ∀ w ∈ C, a w = b w := by
  classical
  have h : ∀ n : Nat, ∀ w ∈ C, w.length = n → a w = b w := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw hlen
      have hbw : b w ∈ C.image a := by
        rw [he]
        exact Finset.mem_image.mpr ⟨w,hw,rfl⟩
      have haw : a w ∈ C.image b := by
        rw [← he]
        exact Finset.mem_image.mpr ⟨w,hw,rfl⟩
      obtain ⟨v,hv,hve⟩ := Finset.mem_image.mp hbw
      obtain ⟨u,hu,hue⟩ := Finset.mem_image.mp haw
      have hvge : w.length ≤ v.length := by
        by_contra hh
        have hlt : v.length < w.length := by omega
        have hv' := ih v.length (by omega) v hv rfl
        have hlt' := hb v hv w hw hlt
        rw [← hv',hve] at hlt'
        exact (lt_irrefl _ hlt')
      have huge : w.length ≤ u.length := by
        by_contra hh
        have hlt : u.length < w.length := by omega
        have hu' := ih u.length (by omega) u hu rfl
        have hlt' := ha u hu w hw hlt
        rw [hu',hue] at hlt'
        exact (lt_irrefl _ hlt')
      have hle : (a w).length ≤ (b w).length := by
        rcases lt_or_eq_of_le hvge with hlt | heq
        · rw [← hve]
          exact (ha w hw v hv hlt).le
        · have heq' := point_unique_length (hC w hw) (hC v hv) heq
          exact le_of_eq (congrArg List.length ((congrArg a heq').trans hve))
      have hge : (b w).length ≤ (a w).length := by
        rcases lt_or_eq_of_le huge with hlt | heq
        · rw [← hue]
          exact (hb w hw u hu hlt).le
        · have heq' := point_unique_length (hC w hw) (hC u hu) heq
          exact le_of_eq (congrArg List.length ((congrArg b heq').trans hue))
      have hvl : w.length = v.length := by
        by_contra hne
        have hlt : w.length < v.length := by omega
        have hh := ha w hw v hv hlt
        rw [hve] at hh
        omega
      have hwv := point_unique_length (hC w hw) (hC v hv) hvl
      exact (congrArg a hwv).trans hve
  exact fun w hw => h w.length w hw rfl

/-- On any finite set of actual coding points, the unlabelled diary and
the length order recover the labelled relation. -/
theorem labelled_of_codes (f : Word → Word) {C : Finset Word}
    (hC : ∀ w ∈ C, Point w)
    (horder : ∀ s ∈ C, ∀ t ∈ C, s.length < t.length → (f s).length < (f t).length)
    (he : codes (C.image f) = codes C) :
    ∀ w ∈ C, code (C.image f) (f w) = code C w := by
  classical
  intro w hw
  have hne : C.Nonempty := ⟨w,hw⟩
  let a := code (C.image f) ∘ f
  let b := code C
  have ha (s : Word) (hs : s ∈ C) (t : Word) (ht : t ∈ C)
      (hlt : s.length < t.length) : (a s).length < (a t).length :=
    (code_length_lt_iff (hne.image f) (Finset.mem_image.mpr ⟨s,hs,rfl⟩)
      (Finset.mem_image.mpr ⟨t,ht,rfl⟩)).mpr (horder s hs t ht hlt)
  have hb (s : Word) (hs : s ∈ C) (t : Word) (ht : t ∈ C)
      (hlt : s.length < t.length) : (b s).length < (b t).length :=
    (code_length_lt_iff hne hs ht).mpr hlt
  have hab : C.image a = C.image b := by
    simpa only [a,b,codes,Finset.image_image] using he
  exact ordered_image_unique hC a b ha hb hab w hw

end GeneralizedNormalization

namespace CodingRelations

/-- Exactly the two new relation families of the manuscript suffice
for the arbitrary labelled finite-set condition: length order, and
the named diaries of nonempty meet-closed sets. -/
theorem labelled_of_named_diaries (f : Word → Word)
    (horder : ∀ s t, Point s → Point t → s.length < t.length →
      (f s).length < (f t).length)
    (hdiary : ∀ C : Finset Word, C.Nonempty → (∀ w ∈ C, Point w) → Closed C →
      codes (C.image f) = codes C) :
    ∀ C : Finset Word, (∀ w ∈ C, Point w) → ∀ w ∈ C,
      code (C.image f) (f w) = code C w := by
  apply labelled_of_closed f
  intro C hne hC hcl
  exact GeneralizedNormalization.labelled_of_codes f hC
    (fun s hs t ht hlt => horder s t (hC s hs) (hC t ht) hlt)
    (hdiary C hne hC hcl)

end CodingRelations
end AllThoseBigRamsey.Pseudotree
