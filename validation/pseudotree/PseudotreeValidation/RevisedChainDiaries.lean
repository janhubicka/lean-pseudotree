import PseudotreeValidation.RevisedCodingRelations
import PseudotreeValidation.GeneralizedRecovery
import PseudotreeValidation.DiaryRecoveryMaximum

/-! The independently defined rightmost chain diaries in the revised
convention are exactly the generalized diaries whose coding points
form a chain. Their cardinality is transported from the checked
leftmost raw-set diary enumeration. The literal FIFO queue is not
reflected in this argument. -/
namespace AllThoseBigRamsey.Pseudotree.RevisedChainDiaries
open RayEmbeddings RayMapModel
open RevisedCodingRelations (model reflectWord flipDigit reflectWord_twice reflectWord_injective
  reflectWord_length flipDigit_twice flipDigit_one)
open RevisedConvention (revisedWordBelow revisedWordBelow_iff_revisedToBlocks_le)

@[simp] theorem flip_zero : flipDigit 0 = 2 := rfl
@[simp] theorem flip_two : flipDigit 2 = 0 := rfl

theorem flip_lt_iff (a b : Fin 3) : flipDigit a < flipDigit b ↔ b < a := by
  fin_cases a <;> fin_cases b <;> decide

@[simp] theorem reflect_append (s t : Word) :
    reflectWord (s ++ t) = reflectWord s ++ reflectWord t := by simp [reflectWord]
@[simp] theorem reflect_cons (a : Fin 3) (s : Word) :
    reflectWord (a :: s) = flipDigit a :: reflectWord s := rfl
@[simp] theorem reflect_child (s : Word) (a : Fin 3) :
    reflectWord (child s a) = child (reflectWord s) (flipDigit a) := by simp [child,reflectWord]
theorem reflect_take (s : Word) (j : Nat) :
    reflectWord (s.take j) = (reflectWord s).take j := by
  induction s generalizing j with
  | nil => cases j <;> rfl
  | cons a s ih => cases j <;> simp [reflectWord] <;> exact ih _

theorem mem_reflect_two (s : Word) : (2 : Fin 3) ∈ reflectWord s ↔ (0 : Fin 3) ∈ s := by
  constructor
  · intro h
    obtain ⟨a,ha,he⟩ := List.mem_map.mp h
    have h' := congrArg flipDigit he
    have ha0 : a = 0 := by simpa only [flipDigit_twice,flip_two] using h'
    exact ha0 ▸ ha
  · intro h
    exact List.mem_map.mpr ⟨0,h,flip_zero⟩

theorem reflect_lt_of_same_length {s t : Word} (hlen : s.length = t.length)
    (h : s < t) : reflectWord t < reflectWord s := by
  induction s generalizing t with
  | nil =>
    have he : t = [] := List.length_eq_zero_iff.mp hlen.symm
    subst t
    exact False.elim ((lt_irrefl _) h)
  | cons a s ih =>
    cases t with
    | nil => simp at hlen
    | cons b t =>
      have hlex : List.Lex (· < ·) (a::s) (b::t) := h
      change List.Lex (· < ·) (flipDigit b :: reflectWord t) (flipDigit a :: reflectWord s)
      cases hlex with
      | rel hab => exact List.Lex.rel ((flip_lt_iff b a).mpr hab)
      | cons ht => exact List.Lex.cons (ih (by simpa using hlen) ht)

theorem reflect_lt_iff {s t : Word} (hlen : s.length = t.length) :
    reflectWord s < reflectWord t ↔ t < s :=
  ⟨fun h => by
    simpa only [reflectWord_twice] using
      reflect_lt_of_same_length (by simpa only [reflectWord_length] using hlen) h,
    reflect_lt_of_same_length hlen.symm⟩

theorem reflect_special (kind : PaperKind) (a : Fin 3) :
    kind.special (flipDigit a) ↔ kind.special a := by
  cases kind <;> fin_cases a <;> decide

theorem reflect_local {w c : Word} (hlen : w.length = c.length) (kind : PaperKind) (a : Fin 3) :
    localChild (reflectWord c) kind.special (reflectWord w) (flipDigit a) ↔
      localChild c kind.special w a := by
  by_cases he : w = c
  · subst c
    simpa only [localChild,if_pos rfl] using reflect_special kind a
  · have hne : reflectWord w ≠ reflectWord c := fun h => he (reflectWord_injective h)
    rw [localChild,if_neg hne,localChild,if_neg he,reflect_lt_iff hlen]
    rcases lt_or_gt_of_ne he with h | h
    · have hn : ¬c < w := not_lt_of_gt h
      simp only [h,hn,if_true,if_false]
      constructor
      · intro h
        simpa only [flipDigit_twice,flip_two] using congrArg flipDigit h
      · rintro rfl
        rfl
    · have hn : ¬w < c := not_lt_of_gt h
      simp only [h,hn,if_true,if_false]
      constructor
      · intro h
        simpa only [flipDigit_twice,flip_zero] using congrArg flipDigit h
      · rintro rfl
        rfl

def reflectSet (C : Finset Word) : Finset Word := C.image reflectWord

@[simp] theorem mem_reflectSet (C : Finset Word) (s : Word) :
    s ∈ reflectSet C ↔ reflectWord s ∈ C := by
  constructor
  · intro h
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp h
    simpa only [reflectWord_twice] using hw
  · intro h
    exact Finset.mem_image.mpr ⟨reflectWord s,h,reflectWord_twice s⟩

@[simp] theorem reflectSet_twice (C : Finset Word) : reflectSet (reflectSet C) = C := by
  ext w
  simp

@[simp] theorem reflectSet_card (C : Finset Word) : (reflectSet C).card = C.card :=
  Finset.card_image_of_injective _ reflectWord_injective

theorem reflect_level {N C : Finset Word} {j : Nat} {k : PaperKind} {c : Word}
    (P : GeneralizedLevel N C j k c) :
    GeneralizedLevel (reflectSet N) (reflectSet C) j k (reflectWord c) := by
  refine ⟨by simp [P.critical_mem],by simpa using P.critical_length,?_,?_⟩
  · intro w hw hj
    have hw' := (mem_reflectSet N w).mp hw
    have hlen : (reflectWord w).length = j := by simpa using hj
    rw [mem_reflectSet,P.coding _ hw' hlen]
    constructor
    · rintro ⟨h,hk⟩
      exact ⟨by simpa only [reflectWord_twice] using congrArg reflectWord h,hk⟩
    · rintro ⟨rfl,hk⟩
      exact ⟨reflectWord_twice c,hk⟩
  · intro w hw hj a
    have hw' := (mem_reflectSet N w).mp hw
    have hlen : (reflectWord w).length = j := by simpa using hj
    rw [mem_reflectSet,reflect_child,P.children _ hw' hlen]
    have h := reflect_local (w := w) (c := reflectWord c)
      (by simpa only [reflectWord_length, P.critical_length] using hj) k a
    simpa only [reflectWord_twice] using h

theorem unreflect_level {N C : Finset Word} {j : Nat} {k : PaperKind} {c : Word}
    (P : GeneralizedLevel (reflectSet N) (reflectSet C) j k c) :
    GeneralizedLevel N C j k (reflectWord c) := by
  simpa only [reflectSet_twice] using reflect_level P

theorem reflect_axioms {N C : Finset Word} {h : Nat} (T : GeneralizedTreeAxioms N C h) :
    GeneralizedTreeAxioms (reflectSet N) (reflectSet C) h where
  height_pos := T.height_pos
  bounded := by intro w hw; simpa using T.bounded _ ((mem_reflectSet _ _).mp hw)
  prefix_closed := by
    intro w hw j hj
    rw [mem_reflectSet,reflect_take]
    exact T.prefix_closed _ ((mem_reflectSet _ _).mp hw) (by simpa using hj)
  code_subset := by intro w hw; exact (mem_reflectSet _ _).mpr (T.code_subset ((mem_reflectSet _ _).mp hw))
  level := by
    intro j hj
    obtain ⟨k,c,P⟩ := T.level j hj
    exact ⟨k,reflectWord c,reflect_level P⟩
  initial := fun c P => T.initial _ (unreflect_level P)
  following := by
    intro j c k p P Q he
    apply T.following j (reflectWord c) k (reflectWord p) (unreflect_level P) (unreflect_level Q)
    simpa only [reflect_child,flipDigit_one] using congrArg reflectWord he

/-- The old chain-local rules imply the generalized ones. The stronger
old adjacency restriction can simply be forgotten. -/
theorem forget_level {N C : Finset Word} {j : Nat} {k : PaperKind} {c : Word}
    (P : PaperLevel N C j k c) : GeneralizedLevel N C j k c :=
  ⟨P.critical_mem,P.critical_length,P.coding,P.children⟩

theorem recover_level {N C : Finset Word} {h j : Nat} {k : PaperKind} {c : Word}
    (T : PaperTreeAxioms N C h) (P : GeneralizedLevel N C j k c) :
    PaperLevel N C j k c := by
  obtain ⟨l,p,Q⟩ := T.level j (by rw [← P.critical_length]; exact T.bounded _ P.critical_mem)
  obtain ⟨hc,hk⟩ := P.unique (forget_level Q)
  subst p
  subst l
  exact Q

theorem forget_axioms {N C : Finset Word} {h : Nat} (T : PaperTreeAxioms N C h) :
    GeneralizedTreeAxioms N C h where
  height_pos := T.height_pos
  bounded := T.bounded
  prefix_closed := T.prefix_closed
  code_subset := T.code_subset
  level := by intro j hj; obtain ⟨k,c,P⟩ := T.level j hj; exact ⟨k,c,forget_level P⟩
  initial := fun c P => T.initial c (recover_level T P)
  following := by
    intro j c k p P Q he
    have hk := T.following j c k p (recover_level T P) (recover_level T Q)
    have hchild : child p 1 ∈ N := he ▸ P.critical_mem
    have hs := (Q.children p Q.critical_mem Q.critical_length 1).mp hchild
    cases k <;> simp_all [PaperKind.allowsTurn,localChild,PaperKind.special]

/-- Any prefix of a generalized diary node is again a node. -/
theorem prefix_node {D : GeneralizedDiary n} {s t : Word}
    (ht : t ∈ D.nodes) (h : s.IsPrefix t) : s ∈ D.nodes := by
  obtain ⟨w,hw,hp⟩ := (D.nodes_iff_prefix_code t).mp ht
  exact (D.nodes_iff_prefix_code s).mpr ⟨w,hw,h.trans hp⟩

theorem siblings {D : GeneralizedDiary n} {p : Word} {a b : Fin 3}
    (ha : child p a ∈ D.nodes) (hb : child p b ∈ D.nodes) (hab : a ≠ b) :
    (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) := by
  obtain ⟨h,T⟩ := D.axioms
  have hp := prefix_node ha (List.prefix_append p [a])
  obtain ⟨k,c,P⟩ := T.level p.length (T.bounded p hp)
  have har := (P.children p hp rfl a).mp ha
  have hbr := (P.children p hp rfl b).mp hb
  cases k <;> by_cases heq : p = c <;> by_cases hlt : p < c <;>
    simp_all [localChild,PaperKind.special] <;> aesop

private theorem first_diff {s t : Word} (hlen : s.length = t.length) (hne : s ≠ t) :
    ∃ p a b u v, s = p ++ a :: u ∧ t = p ++ b :: v ∧ a ≠ b := by
  induction s generalizing t with
  | nil =>
    have h : t = [] := List.length_eq_zero_iff.mp hlen.symm
    exact False.elim (hne h.symm)
  | cons a s ih =>
    cases t with
    | nil => simp at hlen
    | cons b t =>
      by_cases hab : a = b
      · subst b
        obtain ⟨p,c,d,u,v,hs,ht,hn⟩ := ih (by simpa using hlen)
          (fun h => hne (congrArg (List.cons a) h))
        exact ⟨a::p,c,d,u,v,by simp [hs],by simp [ht],hn⟩
      · exact ⟨[],a,b,s,t,rfl,rfl,hab⟩

/-- There is at most one right-original node at any level. -/
theorem no_zero_unique {D : GeneralizedDiary n} {s t : Word}
    (hs : s ∈ D.nodes) (ht : t ∈ D.nodes) (hlen : s.length = t.length)
    (hs0 : (0 : Fin 3) ∉ s) (ht0 : (0 : Fin 3) ∉ t) : s = t := by
  by_contra hne
  obtain ⟨p,a,b,u,v,he,he',hab⟩ := first_diff hlen hne
  have ha : child p a ∈ D.nodes := prefix_node hs (by rw [he]; exact ⟨u,by simp [child]⟩)
  have hb : child p b ∈ D.nodes := prefix_node ht (by rw [he']; exact ⟨v,by simp [child]⟩)
  rcases siblings ha hb hab with ⟨rfl,_⟩ | ⟨_,rfl⟩
  · exact hs0 (by rw [he]; simp)
  · exact ht0 (by rw [he']; simp)

private theorem noOne_point (s : List TernaryLetter) :
    NoOne s ↔ ∃ b, parseWord s = .point b := by
  induction s with
  | nil => simp [parseWord]
  | cons a s ih =>
    cases h : parseWord s with
    | point b =>
      have hs : NoOne s := ih.mpr ⟨b,h⟩
      cases a <;> simp [parseWord,prependBlock,h,hs]
    | above b t =>
      have hs : ¬NoOne s := by
        intro hn
        obtain ⟨c,hc⟩ := ih.mp hn
        rw [h] at hc
        cases hc
      cases a <;> simp [parseWord,prependBlock,h,hs]

private theorem below_distinct (a b : TernaryLetter) (s t : List TernaryLetter)
    (hne : a ≠ b) :
    revisedWordBelow (a::s) (b::t) ↔ a = .zero ∧ NoOne s := by
  rw [noOne_point]
  cases a <;> cases b <;> cases hs : parseWord s <;> cases ht : parseWord t <;>
    simp_all [revisedWordBelow,parseWord,prependBlock,RayTree.first,RevisedConvention.binaryLERevised]

theorem model_le_iff (s t : Word) :
    model s ≤ model t ↔ revisedWordBelow (s.map toLetter) (t.map toLetter) :=
  (revisedWordBelow_iff_revisedToBlocks_le _ _).symm

/-- An upper-cone turn beyond a left-hand prefix is incompatible
with every extension of a right-hand prefix of the same length. -/
theorem separated_incomparable (p q u v : Word) (hlen : p.length = q.length)
    (hlt : p < q) (hu : (1 : Fin 3) ∈ u) :
    ¬model (p++u) ≤ model (q++v) ∧ ¬model (q++v) ≤ model (p++u) := by
  have H (a b : Fin 3) (s t : Word) (h : a < b) (h1 : (1 : Fin 3) ∈ s) :
      ¬model (a::s) ≤ model (b::t) ∧ ¬model (b::t) ≤ model (a::s) := by
    have hne : toLetter a ≠ toLetter b := by
      intro he
      exact (ne_of_lt h) (by simpa only [toFin_toLetter] using congrArg toFin he)
    constructor
    · intro he
      have hh := (model_le_iff _ _).mp he
      have hn := (below_distinct (toLetter a) (toLetter b) _ _ hne).mp hh
      exact hn.2 .one (List.mem_map.mpr ⟨1,h1,rfl⟩) rfl
    · intro he
      have hh := (model_le_iff _ _).mp he
      have hn := (below_distinct (toLetter b) (toLetter a) _ _ hne.symm).mp hh
      have hb : b = 0 := by simpa only [toFin_toLetter] using congrArg toFin hn.1
      omega
  induction p generalizing q with
  | nil =>
    have he : q = [] := List.length_eq_zero_iff.mp hlen.symm
    subst q
    exact False.elim ((lt_irrefl _) hlt)
  | cons a p ih =>
    cases q with
    | nil => simp at hlen
    | cons b q =>
      have hlex : List.Lex (· < ·) (a::p) (b::q) := hlt
      cases hlex with
      | rel hab =>
        exact H a b (p++u) (q++v) hab (List.mem_append_right _ hu)
      | cons ht =>
        have hi := ih q (by simpa using hlen) ht
        constructor
        · intro he
          apply hi.1
          apply (model_le_iff _ _).mpr
          exact (RevisedConvention.below_common_prefix [toLetter a] _ _).mp ((model_le_iff _ _).mp he)
        · intro he
          apply hi.2
          apply (model_le_iff _ _).mpr
          exact (RevisedConvention.below_common_prefix [toLetter a] _ _).mp ((model_le_iff _ _).mp he)

def ChainCodes (D : GeneralizedDiary n) : Prop :=
  ∀ s ∈ D.codes, ∀ t ∈ D.codes, model s ≤ model t ∨ model t ≤ model s

/-- The rightmost-branch condition is forced by the actual chain order.
A prior zero has either a right sibling or a critical node to its right.
Taking coding descendants, and then using the later one-turn, produces
an incomparable pair. -/
theorem rightmost_rule {D : GeneralizedDiary n} (hc : ChainCodes D)
    {j : Nat} {k : PaperKind} {c : Word}
    (P : GeneralizedLevel D.nodes D.codes j k c) (hk : k.continues = true) :
    (0 : Fin 3) ∉ c := by
  intro hz
  obtain ⟨p,t,he⟩ := List.append_of_mem hz
  have hchild : child c 1 ∈ D.nodes := (P.children c P.critical_mem P.critical_length 1).mpr
    (by cases k <;> simp_all [PaperKind.continues,localChild,PaperKind.special])
  obtain ⟨x,hx,z,hxz⟩ := (D.nodes_iff_prefix_code _).mp hchild
  have hxform : x = p ++ 0 :: (t ++ [1] ++ z) := by
    rw [← hxz,child,he]
    simp [List.append_assoc]
  have hp : p ∈ D.nodes := prefix_node P.critical_mem (by rw [he]; exact List.prefix_append _ _)
  have hp0 : child p 0 ∈ D.nodes :=
    prefix_node P.critical_mem (by rw [he]; exact ⟨t,by simp [child]⟩)
  obtain ⟨height,T⟩ := D.axioms
  obtain ⟨l,d,Q⟩ := T.level p.length (T.bounded p hp)
  have h0 := (Q.children p hp rfl 0).mp hp0
  by_cases hd : p = d
  · subst d
    have hl : l = .split := by cases l <;> simp_all [localChild,PaperKind.special]
    subst l
    have hp2 : child p 2 ∈ D.nodes :=
      (Q.children p hp rfl 2).mpr (by simp [localChild,PaperKind.special])
    obtain ⟨y,hy,v,hyv⟩ := (D.nodes_iff_prefix_code _).mp hp2
    have hxx : x = child p 0 ++ (t ++ [1] ++ z) := by simpa [child,List.append_assoc] using hxform
    have hbad := separated_incomparable (child p 0) (child p 2) (t++[1]++z) v
      (by simp [child]) (child_lt_same p (by decide)) (by simp)
    rw [← hxx,hyv] at hbad
    exact (hc x hx y hy).elim hbad.1 hbad.2
  · have hpd : p < d := by
      by_contra hn
      simp [localChild,hd,hn] at h0
    obtain ⟨y,hy,v,hyv⟩ := (D.nodes_iff_prefix_code d).mp Q.critical_mem
    have hbad := separated_incomparable p d (0::(t++[1]++z)) v
      Q.critical_length.symm hpd (by simp)
    rw [← hxform,hyv] at hbad
    exact (hc x hx y hy).elim hbad.1 hbad.2

theorem turn_after_noncontinuation {D : GeneralizedDiary n} (hc : ChainCodes D)
    {j : Nat} {c p : Word} {k : PaperKind}
    (P : GeneralizedLevel D.nodes D.codes (j+1) .turn c)
    (Q : GeneralizedLevel D.nodes D.codes j k p) : k.allowsTurn = true := by
  obtain ⟨_,T⟩ := D.axioms
  by_cases hk : k.continues = true
  · have hp0 := rightmost_rule hc Q hk
    have hc0 := rightmost_rule hc P rfl
    have hp1 : child p 1 ∈ D.nodes := (Q.children p Q.critical_mem Q.critical_length 1).mpr
      (by cases k <;> simp_all [PaperKind.continues,localChild,PaperKind.special])
    have he := no_zero_unique P.critical_mem hp1
      (by simp [child,P.critical_length,Q.critical_length]) hc0 (by simp [child,hp0])
    exact False.elim (T.following j c k p P Q he)
  · cases k <;> simp_all [PaperKind.continues,PaperKind.allowsTurn]

/-- The raw rightmost chain diagrams are identified with the old
independently counted raw-set diaries by explicit digit reflection. -/
abbrev ChainDiary (n : Nat) := {D : GeneralizedDiary n // ChainCodes D}

noncomputable def fromPaper (D : PaperDiary n) : ChainDiary n := by
  let E : GeneralizedDiary n := {
    nodes := reflectSet D.nodes
    codes := reflectSet D.codes
    axioms := ⟨D.axioms.choose,reflect_axioms (forget_axioms D.axioms.choose_spec)⟩
    size := (reflectSet_card _).trans D.size }
  refine ⟨E,?_⟩
  intro s hs t ht
  rw [RevisedCodingRelations.model_reflect,RevisedCodingRelations.model_reflect]
  exact DiaryChains.paper_codes_chain D ((mem_reflectSet _ _).mp hs) ((mem_reflectSet _ _).mp ht)

noncomputable def toPaper (D : ChainDiary n) : PaperDiary n := by
  let T := D.val.axioms.choose_spec
  let U := reflect_axioms T
  let N := reflectSet D.val.nodes
  let C := reflectSet D.val.codes
  have paper : PaperTreeAxioms N C D.val.axioms.choose := by
    refine ⟨U.height_pos,U.bounded,U.prefix_closed,U.code_subset,?_,?_,?_⟩
    · intro j hj
      obtain ⟨k,c,P⟩ := T.level j hj
      have R := reflect_level P
      refine ⟨k,reflectWord c,R.critical_mem,R.critical_length,R.coding,R.children,?_⟩
      intro hk h
      exact rightmost_rule D.property P hk ((mem_reflect_two c).mp h)
    · intro c P
      exact U.initial c (forget_level P)
    · intro j c k p P Q
      exact turn_after_noncontinuation D.property
        (unreflect_level (forget_level P)) (unreflect_level (forget_level Q))
  exact ⟨N,C,⟨_,paper⟩,(reflectSet_card _).trans D.val.size⟩

theorem generalized_ext {D E : GeneralizedDiary n} (hn : D.nodes = E.nodes)
    (hc : D.codes = E.codes) : D = E := by
  cases D
  cases E
  cases hn
  cases hc
  rfl

noncomputable def diaryEquiv (n : Nat) : PaperDiary n ≃ ChainDiary n where
  toFun := fromPaper
  invFun := toPaper
  left_inv := by
    intro D
    apply PaperDiary.ext <;> exact reflectSet_twice _
  right_inv := by
    intro D
    apply Subtype.ext
    apply generalized_ext <;> exact reflectSet_twice _

noncomputable instance (n : Nat) : Fintype (ChainDiary n) :=
  Fintype.ofEquiv (PaperDiary n) (diaryEquiv n)

/-- Exact count of generalized chain diaries in the revised literal
convention, not merely a count of an abstract grammar. -/
theorem chainDiary_card (n : Nat) :
    Fintype.card (ChainDiary n) = diaryCount true n 1 := by
  rw [← Fintype.card_congr (diaryEquiv n),paperDiary_card]

end AllThoseBigRamsey.Pseudotree.RevisedChainDiaries
