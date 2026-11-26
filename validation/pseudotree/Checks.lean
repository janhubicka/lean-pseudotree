import PseudotreeValidation
import Lean

-- The two substantive tree Ramsey inputs are imported with proofs.
#print axioms Milliken.GeneralTree.generalProductHL_unconditional
#print axioms Milliken.GeneralTree.heterogeneousHDHL_unconditional

-- Finite-colour density, arbitrary finite demands, and actual word factors.
#print axioms AllThoseBigRamsey.Pseudotree.finiteColourSparseHL
#print axioms AllThoseBigRamsey.Pseudotree.finiteColourFixedBase
#print axioms AllThoseBigRamsey.Pseudotree.finiteColourDenseMatrices
#print axioms AllThoseBigRamsey.Pseudotree.finiteDemandDenseMatrices
#print axioms AllThoseBigRamsey.Pseudotree.finiteIndexedProductHL
#print axioms AllThoseBigRamsey.Pseudotree.heterogeneousFiniteDemandDenseMatrices
#print axioms AllThoseBigRamsey.Pseudotree.WordTrees.level_eq_length
#print axioms AllThoseBigRamsey.Pseudotree.WordTrees.binary_place_range
#print axioms AllThoseBigRamsey.Pseudotree.WordTrees.ternary_place_range
#print axioms AllThoseBigRamsey.Pseudotree.WordTrees.wordFiniteDemandDenseMatrices
#print axioms AllThoseBigRamsey.Pseudotree.WordTrees.binaryTernaryFiniteDemandDenseMatrices
#print axioms AllThoseBigRamsey.Pseudotree.WordTrees.rayConeDenseMatrices
#print axioms AllThoseBigRamsey.Pseudotree.WordTrees.wordStrongProductHL
#print axioms AllThoseBigRamsey.Pseudotree.WordTrees.rayConeStrongMapsHL
#print axioms AllThoseBigRamsey.Pseudotree.Mixed.exists_rayStable_embedding
#print axioms AllThoseBigRamsey.Pseudotree.Mixed.mixed_product
#print axioms AllThoseBigRamsey.Pseudotree.Mixed.mixed_level_product
#print axioms AllThoseBigRamsey.Pseudotree.RayMilliken.restricted_milliken
#print axioms AllThoseBigRamsey.Pseudotree.DiaryCanonization.simultaneous
#print axioms AllThoseBigRamsey.Pseudotree.PaperDiary.represented
#print axioms AllThoseBigRamsey.Pseudotree.Diary.paper_axioms
#print axioms AllThoseBigRamsey.Pseudotree.Diary.toPaper_injective
#print axioms AllThoseBigRamsey.Pseudotree.Diary.toPaper_surjective
#print axioms AllThoseBigRamsey.Pseudotree.paperDiary_card

-- Identification of the literal ternary model and its finite extensions.
#print axioms AllThoseBigRamsey.Pseudotree.BinaryRay.nonempty_orderIso_rat
#print axioms AllThoseBigRamsey.Pseudotree.wordEquiv
#print axioms AllThoseBigRamsey.Pseudotree.wordBelow_iff_toBlocks_le
#print axioms AllThoseBigRamsey.Pseudotree.toBlocks_wordMeet
#print axioms AllThoseBigRamsey.Pseudotree.wordBelow_prefix_incomparable_lex
#print axioms AllThoseBigRamsey.Pseudotree.ternaryModel_two_cones
#print axioms AllThoseBigRamsey.Pseudotree.extend_finite
#print axioms AllThoseBigRamsey.Pseudotree.finite_universal
#print axioms AllThoseBigRamsey.Pseudotree.RayTree.isUltrahomogeneous
#print axioms AllThoseBigRamsey.Pseudotree.RayTree.age_eq_finiteBinaryClass
#print axioms AllThoseBigRamsey.Pseudotree.ternaryModel_isFraisseLimit
#print axioms AllThoseBigRamsey.Pseudotree.ternaryModel_unique
#print axioms AllThoseBigRamsey.Pseudotree.RayMapModel.embedding
#print axioms AllThoseBigRamsey.Pseudotree.RayMapModel.embedding_apply_word

-- The actual sparse model, normalization, and realization in every subcopy.
#print axioms AllThoseBigRamsey.Pseudotree.SparseModel.isFraisseLimit
#print axioms AllThoseBigRamsey.Pseudotree.SparseModel.selfEmbedding_range
#print axioms AllThoseBigRamsey.Pseudotree.SparseNormalization.normalized_axioms
#print axioms AllThoseBigRamsey.Pseudotree.SparseNormalization.extraction
#print axioms AllThoseBigRamsey.Pseudotree.SparseExtraction.sparse_copy_representation
#print axioms AllThoseBigRamsey.Pseudotree.LowerRealization.sparse_chain_realization
#print axioms AllThoseBigRamsey.Pseudotree.DiaryRecovery.codes_source
#print axioms AllThoseBigRamsey.Pseudotree.DiaryRecovery.image_recovery
#print axioms AllThoseBigRamsey.Pseudotree.DiaryRecovery.embeddedChain_unique

-- The incomparable-pair argument and transfer to every finite such structure.
#print axioms AllThoseBigRamsey.Pseudotree.Incomparables.every_oscillation
#print axioms AllThoseBigRamsey.Pseudotree.Incomparables.every_pairColour
#print axioms AllThoseBigRamsey.Pseudotree.Incomparables.extend_incomparable_pair
#print axioms AllThoseBigRamsey.Pseudotree.Incomparables.arbitrarily_many_copy_colours
#print axioms AllThoseBigRamsey.Pseudotree.Incomparables.no_finite_bound
#print axioms AllThoseBigRamsey.Pseudotree.GenericIncomparables.arbitrarily_many_copy_colours
#print axioms AllThoseBigRamsey.Pseudotree.GenericIncomparables.no_finite_bound_of_countable

-- Endpoints in the original repository API, with no representation,
-- canonization, realization, or diary uniqueness assumptions remaining.
#print axioms AllThoseBigRamsey.Pseudotree.RepoBridge.bound_iff
#print axioms AllThoseBigRamsey.Pseudotree.RepoBridge.incomparable_degree_infinite
#print axioms AllThoseBigRamsey.Pseudotree.RepoBridge.singleton_degree
#print axioms AllThoseBigRamsey.Pseudotree.chain_upper_bound
#print axioms AllThoseBigRamsey.Pseudotree.chain_degree
#print axioms AllThoseBigRamsey.Pseudotree.chain_degree_diaries

-- Generalized selection and labelled projection, without a chain hypothesis.
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedNormalization.essential_subset_selected
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedNormalization.binaryGaps
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedNormalization.rayMap_codes
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedNormalization.selected_image
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedNormalization.code_image
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedNormalization.codes_image

-- The actual exported Abstract Ellentuck Theorem at the inherited pin.
#print axioms RamseySpace.abstractEllentuck_textbook

-- Generalized diary grammar and its Milliken shape interface.
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedNormalization.adjacent_next
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedLevel.unique
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedDiary.shape
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedNormalization.normalized_axioms
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedNormalization.extraction

-- Critical-copy space: sequencing, finitization, and closedness.
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.system
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.finiteRange_injective
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.finitization
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.closed
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.tychonoffClosed
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.ellentuck_of_axioms

-- FIFO stage indexing and actual event geometry (no queue axioms).
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.FIFO.labelStage_injective
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.FIFO.labelStage_surjective
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.FIFO.child_head
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.FIFO.H_surjective_sparse
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.FIFO.U_descendant
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.FIFO.H_branch
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.FIFO.eventNode_critical
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.FIFO.passingNode_geometry
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.FIFO.passingEdge_binary

-- Absolute FIFO lift, for literal generalized diaries and the infinite sparse tree.
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.FIFO.liftedNode_step
#print axioms AllThoseBigRamsey.Pseudotree.FIFOLifting.diary_lift
#print axioms AllThoseBigRamsey.Pseudotree.FIFOLifting.liftCritical
#print axioms AllThoseBigRamsey.Pseudotree.FIFOLifting.liftCritical_code

-- Generalized literal recovery and code-set IRT.
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedDiary.nodes_iff_prefix_code
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedNormalization.selected_source
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedNormalization.labelled_image_recovery
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedNormalization.image_nodes_recovery
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.maps_point
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedCanonization.literal_realized
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedCanonization.finite_fragment
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedCanonization.codeSet_IRT

-- Unbounded rational reservoir transitions and recurrence.
#print axioms AllThoseBigRamsey.Pseudotree.Reservoir.exists_step
#print axioms AllThoseBigRamsey.Pseudotree.Reservoir.recurrence
#print axioms AllThoseBigRamsey.Pseudotree.Reservoir.recurrent_code_sets

-- Critical-copy composition, finite and infinite pullback, and A.3(1) reduction.
#print axioms AllThoseBigRamsey.Pseudotree.RayEmbeddings.RayStrongMap.reflect_edge
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.compose
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.pullFinite
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.le_iff_factor
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.amalgamation_nonempty_of_extension
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.depth_top
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.strict_prefix_leFin

-- Whole-block extension and relative FIFO geometry.
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.FIFO.synchronized_slot_labels
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.FIFO.slot_label_lex
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.RelativeLabels.extendCritical
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.SlotFamily.relative_lift
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.wholeBlockExtension
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.amalgamation_nonempty

-- Coding-range support and rational reservoirs for relative amalgamation.
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.prefix_mem_of_retained
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.fork_prefix_mem
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.le_iff_coding_inclusion
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.FIFO.slot_rayCopy
#print axioms AllThoseBigRamsey.Pseudotree.LowerGeometry.RayCopy.mapped_slot

-- Initialization and the explicit relative reservoir support invariants.
#print axioms AllThoseBigRamsey.Pseudotree.Reservoir.relativeInitial
#print axioms AllThoseBigRamsey.Pseudotree.Reservoir.Step.root_supported
#print axioms AllThoseBigRamsey.Pseudotree.Reservoir.Step.split_supported

-- Infinite relative reservoir assembly and the actual A.3(2) endpoint.
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.RelativeTail.assemble
#print axioms AllThoseBigRamsey.Pseudotree.Reservoir.TailRun.ofInitial
#print axioms AllThoseBigRamsey.Pseudotree.Reservoir.relative_reservoir
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.refinement_of_support
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.amalgamation_refine_of_support
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.assigned_seeds
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.relative_support_construction
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.amalgamation_refine

-- Fixed-prefix Milliken and the sparse next-block forest representation.
#print axioms AllThoseBigRamsey.Pseudotree.RayMilliken.all_fibres_fusion_above
#print axioms AllThoseBigRamsey.Pseudotree.RayMilliken.restricted_milliken_relative
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.blockShape
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.next_block_milliken
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.slotMapsOfStrong
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.suffixLift
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.suffixLift_fixesBlock

-- Relative FIFO comparison, concrete A.4, and Abstract Ellentuck assembly.
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.SlotTransport.inject_injective
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.SlotTransport.suffixes
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.SlotTransport.labels_comp
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.SlotTransport.lift_comp
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.relative_next_colour
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.absolute_next_colour
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.pigeonhole
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.ramseySpace
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.concrete_ellentuck

-- Coding map reconstruction, uniqueness, order and finite-coordinate continuity.
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.CodingCover.exists_cover
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.PreservesCoding.local_agrees
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.PreservesCoding.extends_critical
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.PreservesCoding.unique_extension
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.codingRange_characterization
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.codingRange_le_iff
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.codingRange_injective
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.codingRange_agrees_short
#print axioms AllThoseBigRamsey.Pseudotree.CriticalCopies.finite_cylinder_recovers_approx

-- Finite meet-closed diary relations suffice for the full coding relations.
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedNormalization.code_restriction
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedNormalization.labelled_of_superset
#print axioms AllThoseBigRamsey.Pseudotree.CodingRelations.hull_closed
#print axioms AllThoseBigRamsey.Pseudotree.CodingRelations.labelled_of_closed
#print axioms AllThoseBigRamsey.Pseudotree.CodingRelations.closed_image_iff

-- Native expansion language and correspondence with critical embeddings.
#print axioms AllThoseBigRamsey.Pseudotree.GeneralizedNormalization.labelled_of_codes
#print axioms AllThoseBigRamsey.Pseudotree.CodingRelations.labelled_of_named_diaries
#print axioms AllThoseBigRamsey.Pseudotree.DiaryExpansion.exists_increasing_tuple
#print axioms AllThoseBigRamsey.Pseudotree.DiaryExpansion.criticalEmbedding
#print axioms AllThoseBigRamsey.Pseudotree.DiaryExpansion.embedding_labelled
#print axioms AllThoseBigRamsey.Pseudotree.DiaryExpansion.embeddingEquiv
#print axioms AllThoseBigRamsey.Pseudotree.DiaryExpansion.range_le_iff

-- Analytic transfer by the checked diagonal Souslin-closure theorem.
#print axioms RamseySpace.operation_approxImageScheme
#print axioms RamseySpace.prefixContinuous_range_isRamsey
#print axioms AllThoseBigRamsey.Pseudotree.DiaryExpansion.copyEquiv
#print axioms AllThoseBigRamsey.Pseudotree.DiaryExpansion.finite_copy_cylinder
#print axioms AllThoseBigRamsey.Pseudotree.DiaryExpansion.prefixContinuous_of_continuous
#print axioms AllThoseBigRamsey.Pseudotree.DiaryExpansion.analytic_copies_ramsey

-- Native order/topology identification and first-order Ramsey adapters.
#print axioms AllThoseBigRamsey.Pseudotree.DiaryExpansion.copyHomeomorph
#print axioms AllThoseBigRamsey.Pseudotree.DiaryExpansion.copyEquiv_inclusion
#print axioms AllThoseBigRamsey.Pseudotree.DiaryExpansion.native_recurrence
#print axioms AllThoseBigRamsey.Pseudotree.DiaryExpansion.substructure_diary_preserved
#print axioms AllThoseBigRamsey.Pseudotree.DiaryExpansion.embeddingCodes_injective
#print axioms AllThoseBigRamsey.Pseudotree.DiaryExpansion.native_IRT

-- Anchored oscillation and the exact copy-level obstruction.
#print axioms AllThoseBigRamsey.Pseudotree.FiniteOscillation.two_family_tail
#print axioms AllThoseBigRamsey.Pseudotree.Profiles.System.anchored_oscillations
#print axioms AllThoseBigRamsey.Pseudotree.NoInfiniteCanonical.prescribe_bits
#print axioms AllThoseBigRamsey.Pseudotree.NoInfiniteCanonical.no_universal_partition
#print axioms AllThoseBigRamsey.Pseudotree.NoInfiniteCanonical.ternary_no_universal_partition
#print axioms AllThoseBigRamsey.Pseudotree.NoInfiniteCanonical.factorThrough_comp
#print axioms AllThoseBigRamsey.Pseudotree.NoInfiniteCanonical.tag_rep_comp
#print axioms AllThoseBigRamsey.Pseudotree.NoInfiniteCanonical.transfer_obstruction
#print axioms AllThoseBigRamsey.Pseudotree.NoInfiniteCanonical.ternary_no_universal_copy_partition

-- Countable branching: finite-set avoidance from homogeneity.
#print axioms AllThoseBigRamsey.Pseudotree.NoInfiniteCanonical.withBot_extensionPair
#print axioms AllThoseBigRamsey.Pseudotree.NoInfiniteCanonical.embed_withBot_at
#print axioms AllThoseBigRamsey.Pseudotree.NoInfiniteCanonical.finite_set_avoidance
#print axioms AllThoseBigRamsey.Pseudotree.NoInfiniteCanonical.no_universal_partition_of_countable
#print axioms AllThoseBigRamsey.Pseudotree.NoInfiniteCanonical.no_universal_copy_partition_of_countable

-- Geometry-independent reservoir transitions and revised native recurrence.
#print axioms AllThoseBigRamsey.Pseudotree.LowerGeometry.RayCopy.split_of_prefix_antichain
#print axioms AllThoseBigRamsey.Pseudotree.RevisedConvention.reflected_prefix_antichain
#print axioms AllThoseBigRamsey.Pseudotree.RevisedConvention.revised_sparse_split
#print axioms AllThoseBigRamsey.Pseudotree.RevisedConvention.revisedChart
#print axioms AllThoseBigRamsey.Pseudotree.ChartReservoir.exists_step
#print axioms AllThoseBigRamsey.Pseudotree.ChartReservoir.recurrence
#print axioms AllThoseBigRamsey.Pseudotree.RevisedConvention.revised_recurrent_code_sets
#print axioms AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion.native_recurrence

-- Check all declarations in the manuscript namespace, with transitive
-- dependency collection through mathlib and the tree Ramsey libraries.
-- Defining Fraisse-age application for Psi_omega.
#print axioms AllThoseBigRamsey.Pseudotree.finiteBinaryClass_subset_finiteMeetTreeClass
#print axioms AllThoseBigRamsey.Pseudotree.OmegaFraisse.predecessors
#print axioms AllThoseBigRamsey.Pseudotree.OmegaFraisse.model_dense
#print axioms AllThoseBigRamsey.Pseudotree.OmegaFraisse.model_noMinOrder
#print axioms AllThoseBigRamsey.Pseudotree.OmegaFraisse.model_noMaxOrder
#print axioms AllThoseBigRamsey.Pseudotree.OmegaFraisse.opposite_branch
#print axioms AllThoseBigRamsey.Pseudotree.OmegaFraisse.no_finite_bound
#print axioms AllThoseBigRamsey.Pseudotree.OmegaFraisse.no_universal_copy_partition

-- Literal revised binary convention and unchanged FIFO sparse copy.
#print axioms AllThoseBigRamsey.Pseudotree.RevisedConvention.mirror_below_iff
#print axioms AllThoseBigRamsey.Pseudotree.RevisedConvention.mirror_revisedMeet
#print axioms AllThoseBigRamsey.Pseudotree.RevisedConvention.revised_sparse_meet_closed
#print axioms AllThoseBigRamsey.Pseudotree.RevisedConvention.sparse_dense
#print axioms AllThoseBigRamsey.Pseudotree.RevisedConvention.sparse_fork
#print axioms AllThoseBigRamsey.Pseudotree.RevisedConvention.RevisedSparseModel.isFraisseLimit
#print axioms AllThoseBigRamsey.Pseudotree.RevisedConvention.RevisedSparseModel.selfEmbedding_range

-- Revised native expansion and copy-space endpoints.
#print axioms AllThoseBigRamsey.Pseudotree.RevisedCodingRelations.conjugate_reflect
#print axioms AllThoseBigRamsey.Pseudotree.RevisedCodingRelations.map_meet
#print axioms AllThoseBigRamsey.Pseudotree.RevisedCodingRelations.labelled_of_named_diaries
#print axioms AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion.criticalEmbedding
#print axioms AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion.embeddingEquiv
#print axioms AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion.native_IRT
#print axioms AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion.copyHomeomorph
#print axioms AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion.analytic_copies_ramsey

-- Finite age corollary of revised native IRT.
#print axioms AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion.finite_superstructure
#print axioms AllThoseBigRamsey.Pseudotree.RevisedDiaryExpansion.finite_age_ramsey

-- Exact revised chain-diary characterization and count.
#print axioms AllThoseBigRamsey.Pseudotree.RevisedChainDiaries.reflect_axioms
#print axioms AllThoseBigRamsey.Pseudotree.RevisedChainDiaries.separated_incomparable
#print axioms AllThoseBigRamsey.Pseudotree.RevisedChainDiaries.rightmost_rule
#print axioms AllThoseBigRamsey.Pseudotree.RevisedChainDiaries.turn_after_noncontinuation
#print axioms AllThoseBigRamsey.Pseudotree.RevisedChainDiaries.diaryEquiv
#print axioms AllThoseBigRamsey.Pseudotree.RevisedChainDiaries.chainDiary_card

run_cmd do
  let env ← Lean.getEnv
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if `AllThoseBigRamsey.Pseudotree |>.isPrefixOf name then
      for ax in ← Lean.collectAxioms name do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  Lean.logInfo m!"Audited {checked} pseudotree declarations: only standard axioms."
