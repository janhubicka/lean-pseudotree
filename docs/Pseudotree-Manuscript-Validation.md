# Manuscript validation markers

The current paper uses the revised binary in-order convention
`0 < end < 2`, with rightmost chain diaries and a fixed literal FIFO
queue. This map distinguishes the current results from the original
leftmost-convention proof. The marker links in the TeX source pin an
audited commit, never a moving branch. The manuscript is maintained
in `janhubicka/pseudotree`.

## Last independently audited checkpoint

- Lean: [43dcece03adb](https://github.com/janhubicka/lean-pseudotree/commit/43dcece03adbdb21a8f1a1832b04fe2cfb978a7a)
- Exact-head audit: [45921125425](https://github.com/janhubicka/lean-pseudotree/actions/runs/45921125425),
  5,439 pseudotree declarations, only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Manuscript: [3cf339c55b74](https://github.com/janhubicka/pseudotree/commit/3cf339c55b746ca95359d837bb9c6da0e2be909d).
- Pending consolidated build: [45983941867](https://github.com/janhubicka/lean-pseudotree/actions/runs/45983941867)
  at `58307f5464e4164deec7afbf7a1e39bdf1bbc08d`. The core and independent audit passed; two final adapters compiled. The remaining two source locations were repaired in the following validation batch.

## Statement map

Here `V/` abbreviates `validation/pseudotree/PseudotreeValidation/`
and `S/` abbreviates `AllThoseBigRamsey/Pseudotree/`.
All local declaration names have the prefix
`AllThoseBigRamsey.Pseudotree`. “Audited” means a statement at the
last independent audited checkpoint, with its transitive dependencies;
“interface” records an explicit change of presentation or model,
and “pending” is not a checked declaration.

| Manuscript claim | Status at audited checkpoint | Lean statement(s) |
| --- | --- | --- |
| Oscillation lemma | Audited | `V/FiniteOscillation.lean`: `FiniteOscillation.all_oscillations` |
| Heterogeneous dense-matrix HL and strong maps | Audited | `V/HeterogeneousMatrices.lean`: `heterogeneousFiniteDemandDenseMatrices`; `V/HeterogeneousStrongMaps.lean`: `WordTrees.rootedHeterogeneousWordStrongMapsHL` |
| Infinite degrees in both branching models | Audited, defining-age interface for Ψω | `V/RepoBridge.lean`: `RepoBridge.incomparable_degree_infinite`; `V/OmegaFraisseApplication.lean`: `OmegaFraisse.no_finite_bound`; `V/GenericIncomparables.lean`: image-invariant lower bound |
| Ternary model | Audited, reflection interface | `V/FraisseModel.lean`: `ternaryModel_isFraisseLimit`, `ternaryModel_unique`; `V/RevisedSparseModel.lean`: revised word equivalence |
| Revised lexicographic and separator-prefix clauses | Audited via reflection; direct adapters pending | `V/RevisedSparseGeometry.lean`: `RevisedConvention.mirror_below_iff`; `S/WordLex.lean` and `V/SparseChainGeometry.lean`: original orientation statements |
| Ray-preserving maps, composition, fusion, grafting and completion | Audited | `V/RevisedCodingRelations.lean`: `conjugate`, `model_map`, `map_meet`; `S/RayEmbeddings.lean`, `S/RayGrafting.lean`, `S/RayExtension.lean` |
| Mixed product and one-ternary-factor sharpness | Audited | `V/MixedProduct.lean`: `Mixed.mixed_level_product`; `S/RayObstruction.lean`: `RayEmbeddings.two_ternary_obstruction` |
| Restricted Milliken | Audited | `V/RayMilliken.lean`: `RayMilliken.restricted_milliken` |
| Rightmost chain diaries and exact count | Audited | `V/RevisedChainDiaries.lean`: `rightmost_rule`, `turn_after_noncontinuation`, `diaryEquiv`, `chainDiary_card`; `S/DiaryCounts.lean`: `diaryCount_first_five` |
| Actual revised FIFO sparse model | Audited | `V/RevisedSparseGeometry.lean`: `revised_sparse_meet_closed`; `V/RevisedSparseModel.lean`: `RevisedSparseModel.isFraisseLimit`, `selfEmbedding_range` |
| Generalized normalization, extraction and invariance | Audited on the sparse set; arbitrary-diary-subset adapter compiled; audit pending | `V/GeneralizedNormalization.lean`: `selected_image`, `code_image`; `V/GeneralizedDiaryGrammar.lean`: `normalize`, `extraction`; `V/GeneralizedRecovery.lean`: `image_recovery`, `labelled_image_recovery` |
| Exact revised chain BRD | Audited for functional embeddings; chain-copy adapter compiled; audit pending | `V/RevisedChainDegrees.lean`: `exact_degree`, `realized`, `unavoidable`, `canonical`; chains are rigid |
| FIFO lifting | Audited for finite diaries and the actual infinite sparse tree | `V/FIFOLifting.lean`: `diary_lift`, `liftCritical` |
| Revised recurrence | Audited | `V/RevisedRecurrence.lean`: `RevisedDiaryExpansion.native_recurrence` |
| Native IRT and finite Ramsey age | Audited | `V/RevisedNativeRamsey.lean`: `native_IRT`; `V/RevisedAgeRamsey.lean`: `finite_age_ramsey` |
| Realized versus abstract generalized diaries | Audited | `V/RevisedDiaryRealization.lean`: `realize_pair`, `normalized_pair`, `diary_labels_iff` |
| Non-precompactness for each finite nonchain | Audited for diary labels | `V/RevisedDiaryRealization.lean`: `infinite_nonchain_diaries` |
| Full induced-expansion bijection and local labeled generalized BRS | Pending final compile and audit | `V/RevisedExpansionClassification.lean`, `V/RevisedLocalBRS.lean` (development branch) |
| Minimal unavoidable partition, local finite-fragment canonization, sharpness | Audited on actual literal copies, including nonrigid patterns | `V/RevisedCopyCanonization.lean`: `unavoidable`, `finite_fragment`, `no_proper_unavoidable_refinement`, `sharpness`; all abstract labels identified by `diary_labels_iff` |
| Anchored oscillation and no simultaneous universal partition | Audited, defining-age interface for Ψω | `V/AnchoredOscillation.lean`: `Profiles.System.anchored_oscillations`; `V/CopyPartitionTransfer.lean`, `V/GenericAvoidance.lean`, `V/OmegaFraisseApplication.lean`: actual copy-level obstruction |
| Concrete approximation system, A.1–A.4 and metric closedness | Audited | `V/ConcreteEllentuck.lean`: `CriticalCopies.ramseySpace`, `concrete_ellentuck`; `V/RelativeFIFO.lean`, `V/RelativeMilliken.lean` and related reservoir modules |
| Native expanded-copy identification and analytic Ramsey theorem | Audited in literal revised model | `V/RevisedExpandedCopyLanguage.lean`: `embeddingEquiv`, `range_le_iff`; `V/RevisedCopySpaceTopology.lean`: `copyHomeomorph`; `V/RevisedAnalyticCopies.lean`: `analytic_copies_ramsey` |

## Scope and reproducibility

The countably branching model is treated at its defining Fraïssé-age
interface. Its required geometric hypotheses are derived from the age,
not assumed individually. There is no independent concrete construction
of Ψω in this package. The original and revised word models are
isomorphic, but the two literal FIFO queues are **not** identified by
reflection. All revised sparse-model statements refer to the actual
unchanged queue. The general definition of generalized BRS and its
abstract equivalences are mathematical explanatory statements; the
native local interface is the concrete application in this paper.

Use the [optional package build instructions](../validation/pseudotree/README.md)
and [the cumulative audit ledger](Generalized-Pseudotree-Validation.md).
Historical audit files are snapshots and must not be confused with the
current exact-head CI. The manuscript's marker mode can be changed
without changing mathematical text.
