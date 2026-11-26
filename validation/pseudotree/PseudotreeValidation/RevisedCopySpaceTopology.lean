import PseudotreeValidation.RevisedExpandedCopyLanguage
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Constructions

/-! Literal native expanded-copy space and finite-coordinate control. -/
namespace AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion
open RayEmbeddings FirstOrder
open scoped FirstOrder
open RevisedConvention (RevisedSparseModel)
open CriticalCopies (CriticalMap system approx codingRange)
open SparseNormalization (Point)

local instance boolTopology : TopologicalSpace Bool := ⊥
local instance boolDiscrete : DiscreteTopology Bool := ⟨rfl⟩

noncomputable def characteristic (e : RevisedSparseModel ↪[expandedLanguage] RevisedSparseModel) :
    RevisedSparseModel → Bool := by
  classical
  exact fun x => decide (x ∈ Set.range e)

theorem characteristic_true (e : RevisedSparseModel ↪[expandedLanguage] RevisedSparseModel) (x : RevisedSparseModel) :
    characteristic e x = true ↔ x ∈ Set.range e := by
  classical
  simp [characteristic]

/-- The actual expanded-copy space with the subspace topology inherited
from the product of discrete two-point spaces. -/
abbrev CopySpace := ↥(Set.range characteristic)

noncomputable def toCopy (X : CriticalMap) : CopySpace :=
  ⟨characteristic (criticalEmbedding X),⟨criticalEmbedding X,rfl⟩⟩

theorem toCopy_true (X : CriticalMap) (x : RevisedSparseModel) :
    (toCopy X).val x = true ↔ word x ∈ codingRange X := by
  change characteristic (criticalEmbedding X) x = true ↔ _
  rw [characteristic_true,← range_coding]
  constructor
  · intro hx
    exact ⟨x,hx,rfl⟩
  · rintro ⟨y,hy,he⟩
    exact (word_injective he) ▸ hy

theorem toCopy_injective : Function.Injective toCopy := by
  intro X Y h
  apply CriticalCopies.codingRange_injective
  ext w
  by_cases hp : Point w
  · let x := ofPoint w hp
    have he := congrArg (fun c : CopySpace => c.val x) h
    rw [← show word x = w from word_ofPoint w hp,← toCopy_true,← toCopy_true,he]
  · exact ⟨fun hw => False.elim (hp hw.1),fun hw => False.elim (hp hw.1)⟩

theorem toCopy_surjective : Function.Surjective toCopy := by
  rintro ⟨c,⟨e,rfl⟩⟩
  obtain ⟨X,rfl⟩ := criticalEmbedding_surjective e
  exact ⟨X,rfl⟩

noncomputable def copyEquiv : CriticalMap ≃ CopySpace :=
  Equiv.ofBijective toCopy ⟨toCopy_injective,toCopy_surjective⟩

/-- A bounded coding height gives finitely many points of P. -/
theorem bounded_points_finite (L : Nat) :
    Set.Finite {x : RevisedSparseModel | (word x).length ≤ L} := by
  let E : {x : RevisedSparseModel // (word x).length ≤ L} → CriticalCopies.Prefix (L+1) :=
    fun x => ⟨⟨word x.val,SparseNormalization.point_tree (word_point x.val)⟩,by
      have h := x.property
      change (word x.val).length < 3*(L+1)
      omega⟩
  have hE : Function.Injective E := by
    intro x y h
    apply Subtype.ext
    apply word_injective
    exact congrArg (fun u : CriticalCopies.Prefix (L+1) => u.val.val) h
  change Finite {x : RevisedSparseModel // (word x).length ≤ L}
  exact Finite.of_injective E hE

/-- The reverse finite-cylinder control, expressed in native point
coordinates rather than arbitrary words. -/
theorem finite_copy_cylinder (X : CriticalMap) (n : Nat) :
    ∃ L : Nat, ∀ Y : CriticalMap,
      (∀ x : RevisedSparseModel, (word x).length ≤ L →
        (toCopy X).val x = (toCopy Y).val x) →
      approx n X = approx n Y := by
  obtain ⟨L,hL⟩ := CriticalCopies.finite_cylinder_recovers_approx X n
  refine ⟨L,fun Y hY => hL Y ?_⟩
  intro w hw
  by_cases hp : Point w
  · let x := ofPoint w hp
    have hl : (word x).length ≤ L := by
      rw [show word x = w from word_ofPoint w hp]
      exact hw
    have he := hY x hl
    rw [← show word x = w from word_ofPoint w hp,← toCopy_true,← toCopy_true,he]
  · exact ⟨fun hw => False.elim (hp hw.1),fun hw => False.elim (hp hw.1)⟩


/-- The actual metric approximation topology is the pullback of the
published AR^ω code, with discrete finite approximations. It is not
the finer Ellentuck topology. -/
local instance finiteApproxTopology : TopologicalSpace system.FiniteApprox := ⊥
local instance finiteApproxDiscrete : DiscreteTopology system.FiniteApprox := ⟨rfl⟩

def approximationTopology : TopologicalSpace CriticalMap :=
  TopologicalSpace.induced system.publishedCode Pi.topologicalSpace

local instance : TopologicalSpace CriticalMap := approximationTopology

/-- Local constancy on open neighbourhoods implies continuity. -/
private theorem continuous_of_local_agreement {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] (f : A → B)
    (h : ∀ x : A, ∃ U : Set A, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y = f x) :
    Continuous f := by
  apply continuous_def.mpr
  intro V hV
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨U,hU,hxU,hconst⟩ := h x
  apply Filter.mem_of_superset (hU.mem_nhds hxU)
  intro y hy
  change f y ∈ V
  rw [hconst y hy]
  exact hx

theorem publishedCode_continuous :
    Continuous (fun X : CriticalMap => system.publishedCode X) :=
  continuous_induced_dom

theorem approximation_cylinder_open (X : CriticalMap) (n : Nat) :
    IsOpen {Y : CriticalMap | system.publishedCode Y n = system.publishedCode X n} := by
  have hcont : Continuous (fun Y : CriticalMap => system.publishedCode Y n) :=
    (continuous_apply n).comp publishedCode_continuous
  change IsOpen ((fun Y : CriticalMap => system.publishedCode Y n) ⁻¹'
    ({system.publishedCode X n} : Set system.FiniteApprox))
  exact (isOpen_discrete _).preimage hcont

theorem publishedCode_eq_approx {X Y : CriticalMap} {n : Nat}
    (h : system.publishedCode X n = system.publishedCode Y n) :
    approx n X = approx n Y := by
  change (Sigma.mk n (approx n X) : Sigma CriticalCopies.Approx) =
    Sigma.mk n (approx n Y) at h
  -- Project a dependent pair at the fixed level, avoiding a rewrite
  -- through the semireducible approximation-system projection.
  let atLevel (z : Sigma CriticalCopies.Approx) : CriticalCopies.Approx n :=
    if e : z.1 = n then e ▸ z.2 else approx n X
  have he := congrArg atLevel h
  simpa [atLevel] using he

/-- The forward continuity uses just one approximation coordinate
beyond the length of the queried coding point. -/
theorem toCopy_continuous : Continuous toCopy := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro x
  apply continuous_of_local_agreement
  intro X
  let n := (word x).length+1
  let U := {Y : CriticalMap | system.publishedCode Y n = system.publishedCode X n}
  refine ⟨U,approximation_cylinder_open X n,by change system.publishedCode X n = _; rfl,?_⟩
  intro Y hY
  have h := CriticalCopies.codingRange_agrees_short (publishedCode_eq_approx hY)
    (w := word x) (by dsimp [n]; omega)
  have hh : (toCopy Y).val x = true ↔ (toCopy X).val x = true :=
    (toCopy_true Y x).trans (h.trans (toCopy_true X x).symm)
  change (toCopy Y).val x = (toCopy X).val x
  cases h₁ : (toCopy Y).val x <;> cases h₂ : (toCopy X).val x <;> simp_all

/-- Conversely, finitely many native coding-membership coordinates
determine the prescribed finite approximation near any copy. -/
theorem copyEquiv_symm_continuous : Continuous copyEquiv.symm := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro n
  apply continuous_of_local_agreement
  intro c
  let X := copyEquiv.symm c
  obtain ⟨L,hL⟩ := finite_copy_cylinder X n
  let I := {x : RevisedSparseModel // (word x).length ≤ L}
  letI : Finite I := (bounded_points_finite L).to_subtype
  let U : Set CopySpace := ⋂ x : I, {d | d.val x.val = c.val x.val}
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro x
    change IsOpen ((fun d : CopySpace => d.val x.val) ⁻¹' {c.val x.val})
    exact (isOpen_discrete _).preimage ((continuous_apply x.val).comp continuous_subtype_val)
  refine ⟨U,hU,by simp [U],?_⟩
  intro d hd
  have heq : approx n X = approx n (copyEquiv.symm d) := by
    apply hL
    intro x hx
    have h := Set.mem_iInter.mp hd (⟨x,hx⟩ : I)
    change d.val x = c.val x at h
    have hc : toCopy X = c := copyEquiv.apply_symm_apply c
    have hd' : toCopy (copyEquiv.symm d) = d := copyEquiv.apply_symm_apply d
    rw [hc,hd']
    exact h.symm
  change (⟨n,approx n (copyEquiv.symm d)⟩ : system.FiniteApprox) =
    ⟨n,approx n X⟩
  rw [heq]

/-- The homeomorphism asserted in the manuscript, in the literal
AR^ω topology and the literal 2^P subspace topology. -/
noncomputable def copyHomeomorph : CriticalMap ≃ₜ CopySpace where
  toEquiv := copyEquiv
  continuous_toFun := toCopy_continuous
  continuous_invFun := copyEquiv_symm_continuous

/-- The same bijection is an order identification for inclusion. -/
theorem copyEquiv_inclusion (X Y : CriticalMap) :
    (∀ x : RevisedSparseModel, (toCopy X).val x = true → (toCopy Y).val x = true) ↔
      CriticalCopies.copyRange X ⊆ CriticalCopies.copyRange Y := by
  rw [← range_le_iff X Y]
  constructor
  · intro h x hx
    have hh := h x ((characteristic_true _ _).mpr hx)
    exact (characteristic_true _ _).mp hh
  · intro h x hx
    exact (characteristic_true _ _).mpr (h ((characteristic_true _ _).mp hx))

end AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion
