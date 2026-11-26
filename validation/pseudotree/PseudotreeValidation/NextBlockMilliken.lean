import PseudotreeValidation.RelativeMilliken
import PseudotreeValidation.CriticalCopies
import PseudotreeValidation.GeneralizedDiaryGrammar

/-! The actual sparse three-level gadgets as finite shapes for the
fixed-prefix Milliken theorem. These use the literal tree R and
whole-stage approximations, rather than a new forest encoding. -/
namespace AllThoseBigRamsey.Pseudotree.CriticalCopies
open RayEmbeddings
open SparseNormalization (critical critical_length tree_prefix tree_children)
open RayMilliken

noncomputable def blockNodes (n : Nat) : Finset Word := by
  classical
  letI : Fintype (Prefix n) := Fintype.ofFinite _
  exact Finset.univ.image (fun u : Prefix n => u.val.val)

@[simp] theorem mem_blockNodes (n : Nat) (w : Word) :
    w ∈ blockNodes n ↔ SparseNormalization.Tree w ∧ w.length < 3*n := by
  classical
  unfold blockNodes
  constructor
  · intro h
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp h
    exact ⟨u.val.property,u.property⟩
  · rintro ⟨hw,hl⟩
    exact Finset.mem_image.mpr ⟨⟨⟨w,hw⟩,hl⟩,Finset.mem_univ _,rfl⟩

/-- An incoming 1 is possible only at the unique critical vertex. -/
theorem one_parent_critical {w : Word} (hw : SparseNormalization.Tree (w ++ [1])) :
    w = critical w.length := by
  have hp := tree_prefix hw (List.prefix_append w [1])
  have h := (tree_children w.length w hp rfl 1).mp hw
  by_contra hn
  by_cases hl : w < critical w.length <;> simp [hn,hl] at h

/-- Each actual whole-block prefix is a restricted-Milliken shape. -/
noncomputable def blockShape (n : Nat) (hn : 0 < n) : Shape where
  nodes := blockNodes n
  root_mem := by
    apply (mem_blockNodes n []).mpr
    have hroot : SparseNormalization.Tree (critical 0) := (criticalNode 0).property
    have he : critical 0 = [] := List.length_eq_zero_iff.mp (critical_length 0)
    refine ⟨he ▸ hroot,?_⟩
    simp only [List.length_nil]
    omega
  prefix_closed := by
    intro s t h
    obtain ⟨ht,hl⟩ := (mem_blockNodes n _).mp h
    exact (mem_blockNodes n s).mpr ⟨tree_prefix ht (List.prefix_append _ _),
      by simp only [List.length_append] at hl; omega⟩
  one_per_level := by
    intro s hs t ht hlen hs1 ht1
    obtain ⟨u,rfl⟩ := hs1
    obtain ⟨v,rfl⟩ := ht1
    have hu := one_parent_critical ((mem_blockNodes n _).mp hs).1
    have hv := one_parent_critical ((mem_blockNodes n _).mp ht).1
    have he : u.length = v.length := by simpa using hlen
    have huv : u = v := hu.trans ((congrArg critical he).trans hv.symm)
    rw [huv]

@[simp] theorem blockShape_height (n : Nat) (hn : 0 < n) :
    (blockShape n hn).height = 3*n := by
  have hu : (blockNodes n).sup List.length ≤ 3*n-1 := by
    apply Finset.sup_le
    intro s hs
    have h := ((mem_blockNodes n s).mp hs).2
    omega
  have hl : 3*n-1 ≤ (blockNodes n).sup List.length := by
    have htree : SparseNormalization.Tree (critical (3*n-1)) :=
      (criticalNode (3*n-1)).property
    have hmem : critical (3*n-1) ∈ blockNodes n :=
      (mem_blockNodes n _).mpr ⟨htree,by rw [critical_length]; omega⟩
    simpa only [critical_length] using (Finset.le_sup (f := List.length) hmem)
  change (blockNodes n).sup List.length + 1 = 3*n
  omega

theorem blockShape_initial (n : Nat) (hn : 0 < n) :
    InitialShape (blockShape n hn) (blockShape (n+1) (by omega)) := by
  constructor
  · intro s hs
    change s ∈ blockNodes n at hs
    change s ∈ blockNodes (n+1)
    obtain ⟨ht,hl⟩ := (mem_blockNodes n s).mp hs
    exact (mem_blockNodes (n+1) s).mpr ⟨ht,by omega⟩
  · intro s hs
    rw [blockShape_height]
    change s ∈ blockNodes n ↔ s.length < 3*n
    have ht := ((mem_blockNodes (n+1) s).mp hs).1
    simp [mem_blockNodes,ht]

/-- A genuine strong map on the label tree agrees with the identity
on the old actual R prefix, not necessarily on all irrelevant words. -/
def FixesBlock (f : RayStrongMap) (n : Nat) : Prop :=
  ∀ u : Node, u.val.length < 3*n → f.map u.val = u.val

theorem fixesBlock_level (f : RayStrongMap) {n : Nat} (hn : 0 < n)
    (hf : FixesBlock f n) : f.level (3*n-1) = 3*n-1 := by
  have h := congrArg List.length (hf (criticalNode (3*n-1)) (by simp; omega))
  simpa only [f.length_map,criticalNode_length] using h

/-- The next-block pigeonhole theorem in the exact source domain needed
by the pseudotree. Its colouring may be arbitrary on finite embeddings
of the entire next block; the conclusion is relative to the fixed old
block. The case n=0 uses unrestricted Milliken. -/
theorem next_block_milliken (n : Nat) {colours : Nat}
    (colour : Embedding (blockShape (n+1) (by omega)) → Fin (colours+1)) :
    ∃ c : Fin (colours+1), ∃ g : RayStrongMap,
      FixesBlock g n ∧
      (n = 0 ∨ FixesThrough (3*n-1) g) ∧
      ∀ f : RayStrongMap, FixesBlock f n →
        colour (Embedding.ofTotal (blockShape (n+1) (by omega)) (g.comp f)) = c := by
  classical
  by_cases hn : n = 0
  · subst n
    obtain ⟨c,g,hg⟩ := restricted_milliken _ colour
    refine ⟨c,g,?_,Or.inl rfl,?_⟩
    · intro u hu
      omega
    · intro f _
      exact hg (Embedding.ofTotal _ f)
  · have hnpos : 0 < n := by omega
    let G := blockShape n hnpos
    let F := blockShape (n+1) (by omega)
    let hGF : InitialShape G F := blockShape_initial n hnpos
    let e₀ := Embedding.ofTotal G RayStrongMap.identity
    obtain ⟨g,hg,hmono⟩ := restricted_milliken_relative F G hGF colour e₀
    have htop : e₀.topLevel = 3*n-1 := by
      change G.topNode.val.length = 3*n-1
      rw [G.topNode_length,blockShape_height]
    have hg' : FixesThrough (3*n-1) g := htop ▸ hg
    refine ⟨colour (Embedding.ofTotal F g),g,?_,Or.inr hg',?_⟩
    · intro u hu
      exact hg' u.val (by omega)
    · intro f hf
      have hrestr (f : RayStrongMap) (hf : FixesBlock f n) :
          (Embedding.ofTotal F f).restrict G hGF.1 = e₀ := by
        apply Embedding.ext
        funext s
        have hs := (mem_blockNodes n s.val).mp s.property
        exact hf ⟨s.val,hs.1⟩ hs.2
      have he := hmono (Embedding.ofTotal F f)
        (Embedding.ofTotal F RayStrongMap.identity) (hrestr f hf) rfl
      exact he

end AllThoseBigRamsey.Pseudotree.CriticalCopies
