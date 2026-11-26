import PseudotreeValidation.RevisedDiaryExpansion
import PseudotreeValidation.CodingTopology

/-! Connect native self-embeddings of the exact expansion to the
critical-copy coding-range identification. -/
namespace AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion
open RayEmbeddings FirstOrder
open scoped FirstOrder
open RevisedConvention (RevisedSparseModel)
open SparseNormalization (Point point_tree)
open CriticalCopies (CriticalMap total total_agrees codingRange)

theorem codingAction_preserves (e : RevisedSparseModel ↪[expandedLanguage] RevisedSparseModel) :
    CriticalCopies.PreservesCoding (codingAction e) :=
  ⟨fun w hw => codingAction_point e hw,embedding_labelled e⟩

theorem criticalEmbedding_surjective : Function.Surjective criticalEmbedding := by
  intro e
  obtain ⟨X,hX⟩ := (codingAction_preserves e).extends_critical
  refine ⟨X,?_⟩
  apply FirstOrder.Language.Embedding.ext
  intro x
  apply word_injective
  change word (criticalPointMap X x) = word (e x)
  rw [criticalPointMap_word,total_agrees X (⟨word x,point_tree (word_point x)⟩ : CriticalCopies.Node),
    hX (word x) (word_point x),codingAction_word]

theorem criticalEmbedding_injective : Function.Injective criticalEmbedding := by
  intro X Y h
  apply CriticalCopies.eq_of_agrees_points X Y
  intro w hw
  have he := congrArg (fun e : RevisedSparseModel ↪[expandedLanguage] RevisedSparseModel =>
    word (e (ofPoint w hw))) h
  change word (criticalPointMap X (ofPoint w hw)) =
    word (criticalPointMap Y (ofPoint w hw)) at he
  rwa [criticalPointMap_word,criticalPointMap_word,word_ofPoint,
    total_agrees X (⟨w,point_tree hw⟩ : CriticalCopies.Node),
    total_agrees Y (⟨w,point_tree hw⟩ : CriticalCopies.Node)] at he

/-- A native expansion self-embedding has exactly one critical map. -/
noncomputable def embeddingEquiv :
    CriticalMap ≃ (RevisedSparseModel ↪[expandedLanguage] RevisedSparseModel) :=
  Equiv.ofBijective criticalEmbedding ⟨criticalEmbedding_injective,criticalEmbedding_surjective⟩

theorem range_coding (X : CriticalMap) :
    word '' Set.range (criticalEmbedding X) = codingRange X := by
  ext w
  rw [CriticalCopies.mem_codingRange_iff]
  constructor
  · rintro ⟨_,⟨x,rfl⟩,rfl⟩
    refine ⟨word x,word_point x,?_⟩
    change X.map ⟨word x,point_tree (word_point x)⟩ = word (criticalPointMap X x)
    rw [criticalPointMap_word,total_agrees X (⟨word x,point_tree (word_point x)⟩ : CriticalCopies.Node)]
  · rintro ⟨v,hv,rfl⟩
    let x := ofPoint v hv
    refine ⟨criticalEmbedding X x,⟨x,rfl⟩,?_⟩
    change word (criticalPointMap X x) = X.map ⟨v,point_tree hv⟩
    rw [criticalPointMap_word,show word x = v from word_ofPoint v hv,
      total_agrees X (⟨v,point_tree hv⟩ : CriticalCopies.Node)]

theorem range_le_iff (X Y : CriticalMap) :
    Set.range (criticalEmbedding X) ⊆ Set.range (criticalEmbedding Y) ↔
      CriticalCopies.copyRange X ⊆ CriticalCopies.copyRange Y := by
  rw [← CriticalCopies.codingRange_le_iff,← range_coding,← range_coding]
  constructor
  · exact fun h => Set.image_mono h
  · intro h x hx
    obtain ⟨y,hy,he⟩ := h (show word x ∈ word '' Set.range (criticalEmbedding X) from ⟨x,hx,rfl⟩)
    exact (word_injective he) ▸ hy

end AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion
