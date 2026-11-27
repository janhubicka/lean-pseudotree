# Post-validation refactor

Baseline: [fce8813d6341](https://github.com/janhubicka/lean-pseudotree/commit/fce8813d6341f029520e697eefed1d3e451205f2), successful full audit of 5,498 declarations.
The cleanup on `post-validation-audit` passed the full build and transitive audit at `09b7edf67a466e97f52a4d946d17bb86e88c9fca` (5,165 declarations). It is now merged with the separate Boolean-algebra development, preserving both histories.

## Proof consolidation

The old finite-chain-only realization and normalization assembly had been
superseded by the actual generalized diary realization and exact revised chain
degree. The old finite-chain pipeline (LowerLayers, LowerStep, LowerParents,
LowerTransition, LowerAssembly, LowerRealization, DegreeAssembly, ChainDegrees,
SparseExtraction and the final DiaryRecovery wrapper) is removed from the
active package. Its source remains at the baseline commit in Git history.
The small shared geometric lemmas are extracted unchanged into ReservoirGeometry.
Shared normalization primitives, finite diary enumeration, and proved word
geometry are retained, even when first developed in the original convention.

The original and revised reservoir transition proofs were almost verbatim
duplicates. ReservoirSource now contains the common source events, sparse
source and ordered-child bookkeeping; ChartReservoir is the single transition
and infinite recurrence proof. ReservoirTransitions and SparseRecurrence are
thin specializations to the original coordinate chart. This preserves the
relative construction for Ellentuck without a second transition proof.
The revised chart does not reflect the literal FIFO queue.

RevisedChainDegrees uses the already proved native copy interface to obtain
the unavoidable types, and the common reduct-critical embedding and words
composition lemma. No theorem statement used by the manuscript is weakened.

The five abandoned stage-specific diagnostic audit entry points are removed;
the two active aggregate audit entry points and namespace-wide axiom check
remain. Historical CI logs are retained and identified as historical.

## Audit policy

Only the standard three logical axioms are permitted; the core and full
checks still run. No new admissions. A smaller declaration count after
removing historical duplicate proofs is expected, not a loss of validated
main endpoints. Release validation markers remain pinned to the green
baseline until this cleanup itself is checked.

## First cleanup build

Run [45987683076](https://github.com/janhubicka/lean-pseudotree/actions/runs/45987683076)
at 11154adf26b800d73977345756eb8260f23a064b:
the core audit passed, and ReservoirGeometry, ReservoirSource,
ReservoirChart, ChartReservoir, ReservoirTransitions, SparseRecurrence,
RevisedRecurrence, RevisedCopyCanonization, RevisedExpansionClassification
and RevisedLocalBRS all compiled. The full build reported two underlying
regressions: FIFOBoundary still imported removed LowerStep, blocking
the relative construction; and the simplified chain unavoidability
proof used the duplicated chainWords and words definitions with a
simp-only equality. These are repaired by importing ReservoirGeometry
and making chainWords an abbreviation of the common definition.
The next full build checks the downstream relative amalgamation
and all final endpoints. No mathematical statements have changed.

## Second cleanup build

Run [45989033533](https://github.com/janhubicka/lean-pseudotree/actions/runs/45989033533)
at 9e5a59c9c85657bca5b059c1ea51e39c0a1371f6 passed the core build. The common chainWords definition
and the revised exact chain and literal-copy degree modules compiled;
FIFOBoundary and the relative FIFO and slot modules also compiled.
Only two errors in RelativeReservoirInit were reported, both requiring
explicit reduction of ReservoirChart.original.decode to fromBlocks.
Both simp calls now include ReservoirChart.original. The downstream
relative coding witness likewise reduces the original encode projection
explicitly, to avoid a further elaboration-only regression.
No proof statement was weakened. The full audit must pass before the
new main checkpoint is promoted.

## Independent dependency-patch integrity check

At the exact pinned upstream commits in the current lockfile, the
original and patched SHA-256 hashes and the common hash of the
non-import lines agree with all three entries of
`validation/pseudotree/import-patches/source-integrity.json`.
We independently fetched the pinned source files, applied the recorded
unified-diff hunks in memory, and compared the bytes with the import
lines removed. All three comparisons passed: Milliken/AmbientTree.lean,
Milliken/GeneralTree/HeterogeneousWedgeOrder.lean, RamseySpace/Basic.lean.
This confirms the patch files change imports only, not statements,
proofs, definitions or compiler settings.

The optional reproducibility script `scripts/check_import_patches.py`
checks those same conditions against the actual local patched Lake
checkout, including the commit revisions and the set of modified
tracked files. It does not itself build Lean, and its execution against
a real local Lake checkout remains to be performed. The running full CI
uses the same dependency pins and the unchanged patch files.

## Completed post-cleanup audit

[Exact-head full CI run 45991877707](https://github.com/janhubicka/lean-pseudotree/actions/runs/45991877707)
at `09b7edf67a466e97f52a4d946d17bb86e88c9fca` (job 140481444702) succeeded. Both full builds completed
with 9,304 jobs. The independent endpoint audit checked 5,113
declarations, and the final cumulative audit checked **5,165
declarations**, with only propext, Classical.choice, and Quot.sound.
The separate Lean/Std core run 45991877606 also passed.
The reduction from 5,498 declarations is expected after eliminating
superseded proof paths. No checked main theorem endpoints were
removed or weakened.

The manuscript at `fe3ed30e12dbee44ac093cc04a045a3abfe3d7a3` pins this exact green commit.
The cleaned sources are merged into main with a second parent,
preserving the independent Boolean-algebra companion changes.
The combined repository head needs its own CI; the manuscript
continues to cite the independently verified pseudotree commit.
The dependency-integrity and marker checks passed; standalone
execution of the new convenience scripts and full TeX compilation
have not been performed.

## Combined main and remaining abstract proposition

The combined pseudotree/Boolean companion main commit
12392752df02ef52843b168a997e566c62b630d2 passed exact-head full
run 45994764823 (job 140491288222); the cumulative pseudotree audit
again checked 5165 declarations using only standard axioms.
Subsequent Boolean-only changes are preserved.

AbstractLocalBRS is a separate draft formalization of the three
general equivalences of Proposition local-brs, including relative
minimality inside every reduct self-copy (not merely minimality at
the ambient copy). It uses an occurrence action with composition and
identity and instantiates it with actual first-order embeddings.
Finite palettes, relative refinements and expansion-preserving
self-embeddings are explicit. This additional auxiliary development
awaits compilation; the existing fully audited pseudotree endpoints
are unchanged.
