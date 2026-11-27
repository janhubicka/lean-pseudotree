# Manuscript validation markers

The current paper uses the revised binary in-order convention
`0 < end < 2`, with rightmost chain diaries and a fixed literal FIFO
queue. This map distinguishes the current results from the original
leftmost-convention proof. The marker links in the TeX source pin an
audited commit, never a moving branch. The manuscript is maintained
in `janhubicka/pseudotree`.

## Completed validation checkpoint

- Cleaned Lean proof checkpoint: [09b7edf67a46](https://github.com/janhubicka/lean-pseudotree/commit/09b7edf67a466e97f52a4d946d17bb86e88c9fca).
- Full exact-head CI: [45991877707](https://github.com/janhubicka/lean-pseudotree/actions/runs/45991877707),
  job 140481444702; both builds succeeded (9,304 jobs).
- Independent endpoint audit: 5,113 declarations.
- Final cumulative audit: **5,165 declarations**, only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Lean/Std core: [45991877606](https://github.com/janhubicka/lean-pseudotree/actions/runs/45991877606), success.
- Manuscript pin: [fe3ed30e12db](https://github.com/janhubicka/pseudotree/commit/fe3ed30e12dbee44ac093cc04a045a3abfe3d7a3).
- The original 5,498-declaration checkpoint remains in Git history.
  The [post-validation audit](Post-Validation-Audit.md) documents the
  removed duplicate proofs and successful refactor. No pending compiler
  errors or unexpected axioms at the pinned checkpoint.

## Statement map

Here `V/` abbreviates `validation/pseudotree/PseudotreeValidation/`
and `S/` abbreviates `AllThoseBigRamsey/Pseudotree/`.
All local declaration names have the prefix
`AllThoseBigRamsey.Pseudotree`. “Audited” means a statement at the
completed full audited checkpoint, with its transitive dependencies;
“interface” records an explicit change of presentation or model.

| Manuscript claim | Status at audited checkpoint | Lean statement(s) |
| --- | --- | --- |
| Oscillation lemma | Audited | `V/FiniteOscillation.lean`: `FiniteOscillation.all_oscillations` |
| Heterogeneous dense-matrix HL and strong maps | Audited | `V/HeterogeneousMatrices.lean`: `heterogeneousFiniteDemandDenseMatrices`; `V/HeterogeneousStrongMaps.lean`: `WordTrees.rootedHeterogeneousWordStrongMapsHL` |
| Infinite degrees in both branching models | Audited, defining-age interface for Ψω | `V/RepoBridge.lean`: `RepoBridge.incomparable_degree_infinite`; `V/OmegaFraisseApplication.lean`: `OmegaFraisse.no_finite_bound`; `V/GenericIncomparables.lean`: image-invariant lower bound |
| Ternary model | Audited, reflection interface | `V/FraisseModel.lean`: `ternaryModel_isFraisseLimit`, `ternaryModel_unique`; `V/RevisedSparseModel.lean`: revised word equivalence |
| Revised lexicographic and separator-prefix clauses | Audited directly in revised order | `V/RevisedWordLex.lean`: `revisedWordBelow_prefix_incomparable_lex`, `revisedWordBelow_one_prefix` |
| Ray-preserving maps, composition, fusion, grafting and completion | Audited | `V/RevisedCodingRelations.lean`: `conjugate`, `model_map`, `map_meet`; `S/RayEmbeddings.lean`, `S/RayGrafting.lean`, `S/RayExtension.lean` |
| Mixed product and one-ternary-factor sharpness | Audited | `V/MixedProduct.lean`: `Mixed.mixed_level_product`; `S/RayObstruction.lean`: `RayEmbeddings.two_ternary_obstruction` |
| Restricted Milliken | Audited | `V/RayMilliken.lean`: `RayMilliken.restricted_milliken` |
| Rightmost chain diaries and exact count | Audited | `V/RevisedChainDiaries.lean`: `rightmost_rule`, `turn_after_noncontinuation`, `diaryEquiv`, `chainDiary_card`; `S/DiaryCounts.lean`: `diaryCount_first_five` |
| Actual revised FIFO sparse model | Audited | `V/RevisedSparseGeometry.lean`: `revised_sparse_meet_closed`; `V/RevisedSparseModel.lean`: `RevisedSparseModel.isFraisseLimit`, `selfEmbedding_range` |
| Generalized normalization, extraction and invariance | Audited, including arbitrary subsets of abstract diaries | `V/GeneralizedNormalization.lean`: `selected_image`, `code_image`; `V/GeneralizedDiaryGrammar.lean`: `normalize`, `extraction`; `V/GeneralizedRecovery.lean`: `image_recovery`, `labelled_image_recovery`; `V/GeneralizedSubsetNormalization.lean`: `normalize_subset` |
| Exact revised chain BRD | Audited for literal copies and embeddings | `V/RevisedChainCopyDegree.lean`: `exact_copy_degree`; `V/RevisedChainDegrees.lean`: `exact_degree`, `realized`, `unavoidable`, `canonical` |
| FIFO lifting | Audited for finite diaries and the actual infinite sparse tree | `V/FIFOLifting.lean`: `diary_lift`, `liftCritical` |
| Revised recurrence | Audited | `V/RevisedRecurrence.lean`: `RevisedDiaryExpansion.native_recurrence` |
| Native IRT and finite Ramsey age | Audited | `V/RevisedNativeRamsey.lean`: `native_IRT`; `V/RevisedAgeRamsey.lean`: `finite_age_ramsey` |
| Realized versus abstract generalized diaries | Audited | `V/RevisedDiaryRealization.lean`: `realize_pair`, `normalized_pair`, `diary_labels_iff` |
| Non-precompactness for each finite nonchain | Audited for diary labels | `V/RevisedDiaryRealization.lean`: `infinite_nonchain_diaries` |
| Full induced-expansion bijection and local labeled generalized BRS | Audited | `V/RevisedExpansionClassification.lean`: `induced_eq_iff_labels`, `expansionEquiv`; `V/RevisedLocalBRS.lean`: `expansion_unavoidable`, `local_embedding_canonization` |
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
native local interface is the audited concrete application in this paper.
The successful full build certifies the stated Lean endpoints, not a
line-by-line formalization of every English auxiliary observation.

Use the [optional package build instructions](../validation/pseudotree/README.md)
and [the cumulative audit ledger](Generalized-Pseudotree-Validation.md).
Historical audit files are snapshots and must not be confused with the
current exact-head CI. The manuscript's marker mode can be changed
without changing mathematical text.
