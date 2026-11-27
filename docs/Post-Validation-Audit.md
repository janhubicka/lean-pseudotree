# Post-validation refactor

Baseline: [fce8813d6341](https://github.com/janhubicka/lean-pseudotree/commit/fce8813d6341f029520e697eefed1d3e451205f2), successful full audit of 5,498 declarations.
The new cleanup is developed on `post-validation-audit` and must pass the full build and transitive audit before promotion.

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
