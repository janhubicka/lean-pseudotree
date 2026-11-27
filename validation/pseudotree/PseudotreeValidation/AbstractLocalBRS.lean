import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.ModelTheory.Basic

/-!
# Abstract generalized big Ramsey structures

An action of reduct self-embeddings on occurrences of one fixed finite
pattern. Multiplication is composition, and the right factor restricts
the current copy. The type map is the induced expansion (with the finite
carrier fixed); its codomain consists precisely of realized types.
All results are independent of pseudotree geometry and hold for any
language, including functional reducts.

The three clauses of Proposition local-brs are proved here:
precompactness and exact finite degree; recurrence and native IRT;
minimality of unavoidable partitions in *each* reduct copy.
-/
namespace AllThoseBigRamsey.Pseudotree.AbstractLocalBRS

structure Occurrences (S X : Type*) where
  one : S
  mul : S → S → S
  act : S → X → X
  one_act : ∀ x, act one x = x
  mul_act : ∀ f g x, act (mul f g) x = act f (act g x)

variable {S X T : Type} (O : Occurrences S X) (τ : X → T)

/-- Every realized type occurs inside every reduct self-copy. -/
def Unavoidable : Prop := ∀ f : S, ∀ t : T, ∃ x : X, τ (O.act f x) = t

def Mono {C : Type} (χ : X → C) (t : T) (f : S) : Prop :=
  ∀ x y, τ (O.act f x) = t → τ (O.act f y) = t → χ (O.act f x) = χ (O.act f y)

/-- Colors are total on occurrences. Restricting to the selected type
is equivalent to coloring its fiber (see local_fiber). -/
def Local : Prop :=
  ∀ (C : Type) [Fintype C] (χ : X → C) (t : T) (f : S),
    ∃ g : S, Mono O τ χ t (O.mul f g)

def GeneralizedBRS : Prop := Unavoidable O τ ∧ Local O τ

theorem mono_mul {C : Type} {χ : X → C} {t : T} {f : S}
    (h : Mono O τ χ t f) (g : S) : Mono O τ χ t (O.mul f g) := by
  intro x y hx hy
  simp only [O.mul_act] at hx hy ⊢
  exact h _ _ hx hy

theorem mono_same_action {C : Type} {χ : X → C} {t : T} {f g : S}
    (h : ∀ x, O.act f x = O.act g x) (hf : Mono O τ χ t f) :
    Mono O τ χ t g := by
  intro x y hx hy
  rw [← h x,← h y] at hx hy ⊢
  exact hf x y hx hy

theorem local_fiber (hU : Unavoidable O τ) (hL : Local O τ)
    (C : Type) [Fintype C] (t : T) (χ : {x : X // τ x = t} → C) (f : S) :
    ∃ g : S, ∀ x y (hx : τ (O.act (O.mul f g) x) = t)
      (hy : τ (O.act (O.mul f g) y) = t),
      χ ⟨_,hx⟩ = χ ⟨_,hy⟩ := by
  classical
  obtain ⟨x,hx⟩ := hU O.one t
  let d := χ ⟨O.act O.one x,hx⟩
  let c (z : X) : C := if hz : τ z = t then χ ⟨z,hz⟩ else d
  obtain ⟨g,hg⟩ := hL C c t f
  refine ⟨g,fun x y hx hy => ?_⟩
  simpa only [c,dif_pos hx,dif_pos hy] using hg x y hx hy

/-- Finite simultaneous canonization: successive refinements retain
all the previously obtained homogeneous fibers. -/
theorem finite_family (h : Local O τ) (C : Type) [Fintype C] (χ : X → C)
    (F : List T) (f : S) : ∃ g : S, ∀ t ∈ F, Mono O τ χ t (O.mul f g) := by
  induction F generalizing f with
  | nil => exact ⟨O.one,by simp⟩
  | cons t F ih =>
    obtain ⟨g,hg⟩ := h C χ t f
    obtain ⟨k,hk⟩ := ih (O.mul f g)
    refine ⟨O.mul g k,fun u hu => ?_⟩
    have he : ∀ x, O.act (O.mul (O.mul f g) k) x =
        O.act (O.mul f (O.mul g k)) x := by
      intro x
      simp only [O.mul_act]
    rcases List.mem_cons.mp hu with heq | hm
    · subst u
      exact mono_same_action O τ he (mono_mul O τ hg k)
    · exact mono_same_action O τ he (hk u hm)

/-- A finite embedding-degree upper bound; no homogeneity of expansion
types is assumed in this definition. -/
def Bound (d : Nat) : Prop :=
  ∀ (C : Type) [Fintype C] (χ : X → C),
    ∃ f : S, ∃ P : Finset C, P.card ≤ d ∧ ∀ x, χ (O.act f x) ∈ P

def ExactDegree (d : Nat) : Prop := Bound O d ∧ ∀ k, k < d → ¬ Bound O k

theorem unavoidable_lower [Fintype T] (hU : Unavoidable O τ) {d : Nat}
    (hb : Bound O d) : Fintype.card T ≤ d := by
  classical
  obtain ⟨f,P,hP,hcover⟩ := hb T τ
  have h : (Finset.univ : Finset T) ⊆ P := by
    intro t _
    obtain ⟨x,hx⟩ := hU f t
    rw [← hx]
    exact hcover x
  have hc : Fintype.card T ≤ P.card := by simpa using Finset.card_le_card h
  exact hc.trans hP

/-- The exact finite degree forces local canonization inside *any*
specified reduct copy, by augmenting the coloring with its type. -/
theorem local_of_bound [Fintype T] (hU : Unavoidable O τ)
    (hb : Bound O (Fintype.card T)) : Local O τ := by
  classical
  intro C _ χ t f
  let c (x : X) : T × C := (τ (O.act f x),χ (O.act f x))
  obtain ⟨g,P,hP,hcover⟩ := hb (T × C) c
  have hsurj : P.image Prod.fst = (Finset.univ : Finset T) := by
    ext u
    constructor
    · intro _
      exact Finset.mem_univ _
    · intro _
      obtain ⟨x,hx⟩ := hU (O.mul f g) u
      exact Finset.mem_image.mpr ⟨c (O.act g x),hcover x,by
        simpa only [c,O.mul_act] using hx⟩
  have hcard : (P.image Prod.fst).card = P.card := by
    apply le_antisymm Finset.card_image_le
    rw [hsurj,Finset.card_univ]
    exact hP
  have hinj := Finset.injOn_of_card_image_eq hcard
  refine ⟨g,fun x y hx hy => ?_⟩
  have he : c (O.act g x) = c (O.act g y) := hinj (hcover x) (hcover y) (by
    simpa only [c,O.mul_act] using hx.trans hy.symm)
  simpa only [c,O.mul_act] using congrArg Prod.snd he

theorem bound_of_local [Fintype T] (hU : Unavoidable O τ) (hL : Local O τ) :
    Bound O (Fintype.card T) := by
  classical
  intro C _ χ
  obtain ⟨g,hg⟩ := finite_family O τ hL C χ (Finset.univ : Finset T).toList O.one
  let f := O.mul O.one g
  let x (t : T) : X := (hU f t).choose
  have hx (t : T) : τ (O.act f (x t)) = t := (hU f t).choose_spec
  let c (t : T) : C := χ (O.act f (x t))
  refine ⟨f,Finset.univ.image c,Finset.card_image_le.trans (by simp),fun y => ?_⟩
  let t := τ (O.act f y)
  have hm : Mono O τ χ t f := hg t (by simp)
  exact Finset.mem_image.mpr ⟨t,Finset.mem_univ _,(hm y (x t) rfl (hx t)).symm⟩

/-- Proposition (i): the standard finite-degree definition of a big
Ramsey expansion (unavoidable and attaining the exact embedding degree)
agrees with the local definition whenever the realized types are finite. -/
theorem precompact_iff [Fintype T] :
    GeneralizedBRS O τ ↔ Unavoidable O τ ∧ ExactDegree O (Fintype.card T) := by
  constructor
  · rintro ⟨hU,hL⟩
    refine ⟨hU,bound_of_local O τ hU hL,?_⟩
    intro k hk hb
    exact (not_le_of_gt hk) (unavoidable_lower O τ hU hb)
  · rintro ⟨hU,hb,_⟩
    exact ⟨hU,local_of_bound O τ hU hb⟩

/-- Good self-embeddings preserve every expansion relation, not
merely the fixed finite type. Only the induced action on this
pattern is needed in the following proof. -/
def Preserves (Good : S → Prop) : Prop :=
  ∀ f, Good f → ∀ x, τ (O.act f x) = τ x

def Recurrent (Good : S → Prop) : Prop := ∀ f, ∃ g, Good (O.mul f g)

def NativeIRT (Good : S → Prop) : Prop :=
  ∀ (C : Type) [Fintype C] (χ : X → C) (t : T), ∃ g, Good g ∧ Mono O τ χ t g

theorem recurrence_unavoidable (Good : S → Prop)
    (hs : Function.Surjective τ) (hp : Preserves O τ Good) (hr : Recurrent O Good) :
    Unavoidable O τ := by
  intro f t
  obtain ⟨g,hg⟩ := hr f
  obtain ⟨x,hx⟩ := hs t
  refine ⟨O.act g x,?_⟩
  rw [← O.mul_act,hp _ hg,hx]

/-- Proposition (ii), under recurrence. No finiteness of T is needed. -/
theorem recurrent_iff (Good : S → Prop)
    (hs : Function.Surjective τ) (hp : Preserves O τ Good) (hr : Recurrent O Good) :
    GeneralizedBRS O τ ↔ NativeIRT O τ Good := by
  constructor
  · rintro ⟨_,hL⟩
    intro C _ χ t
    obtain ⟨g,hg⟩ := hL C χ t O.one
    obtain ⟨k,hk⟩ := hr (O.mul O.one g)
    exact ⟨O.mul (O.mul O.one g) k,hk,mono_mul O τ hg k⟩
  · intro hI
    refine ⟨recurrence_unavoidable O τ Good hs hp hr,?_⟩
    intro C _ χ t f
    obtain ⟨g,hg⟩ := hr f
    let e := O.mul f g
    obtain ⟨k,hk,hmono⟩ := hI C (fun x => χ (O.act e x)) t
    refine ⟨O.mul g k,fun x y hx hy => ?_⟩
    have hx' : τ (O.act k x) = t := by
      rw [← hp e hg (O.act k x)]
      simpa only [e,O.mul_act] using hx
    have hy' : τ (O.act k y) = t := by
      rw [← hp e hg (O.act k y)]
      simpa only [e,O.mul_act] using hy
    simpa only [e,O.mul_act] using hmono x y hx' hy'

/-- A refinement is specified by arbitrary new labels on occurrences
inside the initial reduct copy f. Unavoidability is relative to that
copy, i.e. it must survive all further right factors. -/
def Minimal : Prop :=
  ∀ (f : S) (R : Type) (γ : X → R),
    (∀ x y, γ x = γ y → τ (O.act f x) = τ (O.act f y)) →
    (∀ g x, ∃ y, γ (O.act g y) = γ x) →
    ∀ x y, τ (O.act f x) = τ (O.act f y) → γ x = γ y

/-- Auxiliary relative local property, expressed on occurrences in
the initial copy rather than on ambient occurrences. This is the
natural representation of a coloring of a copy. -/
def RelativeLocal : Prop :=
  ∀ (C : Type) [Fintype C] (χ : X → C) (t : T) (f : S),
    ∃ g, ∀ x y, τ (O.act f (O.act g x)) = t →
      τ (O.act f (O.act g y)) = t → χ (O.act g x) = χ (O.act g y)

/-- For embeddings, left composition is injective. Hence the
ambient and relative versions of local canonization agree. -/
theorem relative_iff (hinj : ∀ f, Function.Injective (O.act f)) :
    Local O τ ↔ RelativeLocal O τ := by
  classical
  constructor
  · intro h C _ χ t f
    cases isEmpty_or_nonempty X with
    | inl hX =>
      letI := hX
      exact ⟨O.one,fun x => isEmptyElim x⟩
    | inr hX =>
      let c (z : X) : C :=
        if hz : ∃ x, O.act f x = z then χ hz.choose else χ hX.some
      have hc (x : X) : c (O.act f x) = χ x := by
        have he : ∃ y, O.act f y = O.act f x := ⟨x,rfl⟩
        rw [show c (O.act f x) = (if hz : ∃ y, O.act f y = O.act f x
          then χ hz.choose else χ hX.some) from rfl,dif_pos he,hinj f he.choose_spec]
      obtain ⟨g,hg⟩ := h C c t f
      refine ⟨g,fun x y hx hy => ?_⟩
      have he := hg x y (by simpa only [O.mul_act] using hx)
        (by simpa only [O.mul_act] using hy)
      simpa only [O.mul_act,hc] using he
  · intro h C _ χ t f
    obtain ⟨g,hg⟩ := h C (fun x => χ (O.act f x)) t f
    refine ⟨g,fun x y hx hy => ?_⟩
    simpa only [O.mul_act] using hg x y (by simpa only [O.mul_act] using hx)
      (by simpa only [O.mul_act] using hy)

/-- One direction of (iii): a split of a single type can be removed
by local two-color canonization. -/
theorem minimal_of_relative (h : RelativeLocal O τ) : Minimal O τ := by
  classical
  intro f R γ href hun x y hxy
  by_contra hne
  let χ (z : X) : Bool := decide (γ z = γ x)
  obtain ⟨g,hg⟩ := h Bool χ (τ (O.act f x)) f
  obtain ⟨a,ha⟩ := hun g x
  obtain ⟨b,hb⟩ := hun g y
  have hc := hg a b (href _ _ ha) ((href _ _ hb).trans hxy.symm)
  have h₀ : χ (O.act g a) = true := by simp [χ,ha]
  have h₁ : χ (O.act g b) = false := by simp [χ,hb,Ne.symm hne]
  rw [h₀,h₁] at hc
  contradiction

/-- Conversely, minimality relative to each copy forces binary
canonization there: otherwise the two colors of one type give a
proper refinement that survives every further self-copy. -/
theorem binary_of_minimal (hU : Unavoidable O τ) (hM : Minimal O τ)
    (p : X → Prop) (t : T) (f : S) :
    ∃ g, ∀ x y, τ (O.act (O.mul f g) x) = t →
      τ (O.act (O.mul f g) y) = t →
      (p (O.act (O.mul f g) x) ↔ p (O.act (O.mul f g) y)) := by
  classical
  by_contra h
  have hfail (g : S) : ∃ a b, τ (O.act (O.mul f g) a) = t ∧
      τ (O.act (O.mul f g) b) = t ∧
      ¬ (p (O.act (O.mul f g) a) ↔ p (O.act (O.mul f g) b)) := by
    by_contra hn
    apply h
    refine ⟨g,fun a b ha hb => ?_⟩
    by_contra hh
    exact hn ⟨a,b,ha,hb,hh⟩
  let γ (x : X) : T × Bool :=
    (τ (O.act f x),decide (τ (O.act f x) = t ∧ p (O.act f x)))
  have href (x y : X) (he : γ x = γ y) :
      τ (O.act f x) = τ (O.act f y) := congrArg Prod.fst he
  have hboth (g : S) :
      (∃ a, τ (O.act (O.mul f g) a) = t ∧ p (O.act (O.mul f g) a)) ∧
      (∃ b, τ (O.act (O.mul f g) b) = t ∧ ¬ p (O.act (O.mul f g) b)) := by
    obtain ⟨a,b,ha,hb,hab⟩ := hfail g
    by_cases hp : p (O.act (O.mul f g) a)
    · exact ⟨⟨a,ha,hp⟩,⟨b,hb,fun hq => hab ⟨fun _ => hq,fun _ => hp⟩⟩⟩
    · exact ⟨⟨b,hb,by
        by_contra hq
        exact hab ⟨fun ha => False.elim (hp ha),fun hb => False.elim (hq hb)⟩⟩,
        ⟨a,ha,hp⟩⟩
  have hun (g : S) (x : X) : ∃ y, γ (O.act g y) = γ x := by
    by_cases ht : τ (O.act f x) = t
    · by_cases hp : p (O.act f x)
      · obtain ⟨a,ha,hpa⟩ := (hboth g).1
        simp only [O.mul_act] at ha hpa
        exact ⟨a,by simp [γ,ht,hp,ha,hpa]⟩
      · obtain ⟨b,hb,hpb⟩ := (hboth g).2
        simp only [O.mul_act] at hb hpb
        exact ⟨b,by simp [γ,ht,hp,hb,hpb]⟩
    · obtain ⟨a,ha⟩ := hU (O.mul f g) (τ (O.act f x))
      simp only [O.mul_act] at ha
      exact ⟨a,by simp [γ,ha,ht]⟩
  obtain ⟨a,ha,hpa⟩ := (hboth O.one).1
  obtain ⟨b,hb,hpb⟩ := (hboth O.one).2
  simp only [O.mul_act,O.one_act] at ha hb hpa hpb
  have he := hM f (T × Bool) γ href hun a b (ha.trans hb.symm)
  have he' := congrArg Prod.snd he
  simp [γ,ha,hb,hpa,hpb] at he'

/-- Binary canonization implies arbitrary finite color canonization,
by induction on the palette and repeated deletion of a color. -/
theorem local_of_binary
    (hBin : ∀ (p : X → Prop) (t : T) (f : S), ∃ g, ∀ x y,
      τ (O.act (O.mul f g) x) = t → τ (O.act (O.mul f g) y) = t →
      (p (O.act (O.mul f g) x) ↔ p (O.act (O.mul f g) y))) :
    Local O τ := by
  classical
  intro C _ χ t f
  have haux (P : Finset C) (f : S)
      (hP : ∀ x, τ (O.act f x) = t → χ (O.act f x) ∈ P) :
      ∃ g, Mono O τ χ t (O.mul f g) := by
    induction P using Finset.induction_on generalizing f with
    | empty =>
      refine ⟨O.one,fun x y hx hy => ?_⟩
      simp only [O.mul_act,O.one_act] at hx
      exact False.elim (by simpa using hP x hx)
    | @insert c P hc ih =>
      obtain ⟨g,hg⟩ := hBin (fun x => χ x = c) t f
      let e := O.mul f g
      by_cases hhit : ∃ x, τ (O.act e x) = t ∧ χ (O.act e x) = c
      · obtain ⟨x,hx,hcx⟩ := hhit
        refine ⟨g,fun a b ha hb => ?_⟩
        exact ((hg x a hx ha).mp hcx).trans ((hg x b hx hb).mp hcx).symm
      · have hP' (x : X) (hx : τ (O.act e x) = t) : χ (O.act e x) ∈ P := by
          have hm := hP (O.act g x) (by simpa only [e,O.mul_act] using hx)
          have hm' : χ (O.act e x) ∈ insert c P := by simpa only [e,O.mul_act] using hm
          rcases Finset.mem_insert.mp hm' with heq | hm
          · exact False.elim (hhit ⟨x,hx,heq⟩)
          · exact hm
        obtain ⟨k,hk⟩ := ih e hP'
        refine ⟨O.mul g k,mono_same_action O τ (fun x => ?_) hk⟩
        simp only [e,O.mul_act]
  exact haux Finset.univ f (fun _ _ => Finset.mem_univ _)

/-- Proposition (iii). The injective action is automatic for
postcomposition by reduct embeddings. No finiteness or recurrence
of the expansion is required. -/
theorem minimal_iff (hinj : ∀ f, Function.Injective (O.act f))
    (hU : Unavoidable O τ) : GeneralizedBRS O τ ↔ Minimal O τ := by
  constructor
  · rintro ⟨_,hL⟩
    exact minimal_of_relative O τ ((relative_iff O τ hinj).mp hL)
  · intro hM
    exact ⟨hU,local_of_binary O τ (binary_of_minimal O τ hU hM)⟩

end AllThoseBigRamsey.Pseudotree.AbstractLocalBRS

section Native
open FirstOrder
open scoped FirstOrder

namespace AllThoseBigRamsey.Pseudotree.AbstractLocalBRS
variable {L : Language} {A K : Type} [L.Structure A] [L.Structure K]

/-- The action used by the paper: postcomposition of actual
first-order embeddings, in an arbitrary functional or relational language. -/
def embeddingOccurrences : Occurrences (K ↪[L] K) (A ↪[L] K) where
  one := FirstOrder.Language.Embedding.refl L K
  mul := fun f g => f.comp g
  act := fun f e => f.comp e
  one_act := by
    intro e
    apply FirstOrder.Language.Embedding.ext
    intro a
    rfl
  mul_act := by
    intro f g e
    apply FirstOrder.Language.Embedding.ext
    intro a
    rfl

theorem embedding_action_injective (f : K ↪[L] K) :
    Function.Injective ((embeddingOccurrences (A := A) (K := K)).act f) := by
  intro e g h
  apply FirstOrder.Language.Embedding.ext
  intro a
  apply f.injective
  exact congrArg (fun u : A ↪[L] K => u a) h

end AllThoseBigRamsey.Pseudotree.AbstractLocalBRS
end Native
