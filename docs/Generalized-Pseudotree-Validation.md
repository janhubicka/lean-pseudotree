# Generalized diary and Ellentuck validation batch

This branch incorporates main at b4eed2a9edfcdabbe5008798f1342aa5ec1c8770 (checked generalized normalization)
and repairs the failed CriticalCopies elaboration at 5690d882b3b584ae20a0f03a9acec67d4c96575e.

New work:
- GeneralizedProjection: inverse-prefix and child correspondence, uniqueness of
  consecutive retained steps, finite-code cardinality, and invariant normalized
  prefix sets.
- GeneralizedDiaryGrammar: independent literal local rules, unique critical
  node and kind, direct restricted-Milliken Shape, and extraction of arbitrary
  nonempty finite subsets of the actual sparse coding set. The old chain-only
  grammar and its proofs are untouched.
- CriticalCopies: fix the reserved name, subtype and elaboration errors from
  run 45831225235; retain explicit A.1, A.2 and closedness obligations.

All new declarations await exact-head Lean build and axiom audit. No additional
axioms, sorry, admit or changed dependencies are introduced. The abstract
Ellentuck endpoint remains explicitly conditional. Next obligations include
recovery for arbitrary literal generalized diaries, FIFO lifting (absolute
and relative), recurrence, expanded copy identification, A.3 and A.4.
The current upstream A.2 interface uses non-strict initial segments; the
strict variant in the manuscript should also be proved explicitly.

## Second batch

Repairs the eight elaboration errors in GeneralizedProjection and CriticalCopies
from run 45833869256. Adds FIFOIndex: breadth-first heap indexing of the actual
sparse queue; the code/head cone formulas, event heights and waiting-node
separation; binary continuation of waiting branches. These are prerequisites
for the complete local-to-global FIFO lift, not yet the lift itself. Pending
exact-head validation; main stays at the previously checked revision.

## Third batch

Run 45835182930 compiled GeneralizedProjection, GeneralizedDiaryGrammar and CriticalCopies; the full audit was blocked by six FIFOIndex elaboration errors. This batch repairs them and develops FIFOEdges and FIFOLifting. The latter instantiates a local event-tree interface on the literal generalized diaries and the actual infinite sparse tree. Both finite and infinite lifts use the explicit FIFO formula. No new axioms or sorry are introduced. Awaiting exact-head build and audit; relative lifting, literal recovery, recurrence and A.3/A.4 remain separate obligations.

## Fourth batch

GeneralizedRecovery proves the prefix-closure characterization and recovery of the independent literal grammar under normalization, including labels on arbitrary finite images. GeneralizedCanonization proves literal realizability and finite-fragment canonization / IRT in the concrete code-set representation, conditional only on the compilation of the actual FIFO construction imported from FIFOLifting. The first-order expansion packaging, recurrence in arbitrary reduct copies, and relative A.3/A.4 remain separate obligations. The new declarations are not marked verified until exact-head CI passes.

## Fifth batch

Run 45839462556 successfully compiled FIFOIndex, FIFOEdges, GeneralizedProjection, GeneralizedDiaryGrammar, GeneralizedRecovery, and CriticalCopies. Four recursive simplifier errors in FIFOLifting prevented the full axiom audit. This batch replaces the recursive rewrites with explicit local equations. ReservoirTransitions extends the checked local rational-reservoir geometry to unbounded sources, allowing a separate target for each vertex (constant along the edges being extended). SparseRecurrence instantiates this with the actual infinite sparse tree and assembles a critical map into any prescribed sparse reduct copy, preserving all finite code-set types. New declarations await exact-head compilation and transitive audit. The relative initialization, full relative A.3/A.4, and first-order packaging remain separate tasks. The earlier chain proof is left unchanged.

## Sixth batch

CriticalPullback develops binary edge reflection, exact composition, finite pullback (without assuming infinite extendibility), and infinite factorization. A.3(1) is reduced to the explicit WholeBlockExtension obligation. The existing exact-tail lemma is exported without changing its proof. CriticalDepth proves the final coding level characterization of depth and the strict A.2(3) variant in the manuscript. No new axioms or sorry are introduced. All new declarations await compilation and transitive audit; whole-block extension and relative A.3(2)/A.4 remain outstanding.

Run 45842568797 successfully compiled FIFOLifting and ReservoirTransitions in addition to the earlier modules. It failed on two elaboration errors in the endpoint modules: membership in the root set and the identity-map expression in labelled recovery. Both are repaired by explicit change statements in the follow-up. The full axiom audit was not reached.

## Seventh batch

Run 45843713728 compiled all of the generalized grammar, recovery, absolute
FIFO lifting, recurrence and finite-fragment canonization / code-set IRT
modules. It failed on two missing definitional unfoldings in the pullback
length equations. Both are repaired, with the analogous depth proof made
explicit.

The new relative FIFO development has three components:

- FIFOBoundary identifies label cones for live queue slots using the actual
  FIFO child schedule, and pads finitely many labels to a common depth.
- RelativeFIFO assembles the local FIFO formula above a prescribed finite
  critical map, including the incoming binary-edge root condition.
- RelativeSlots supplies those hypotheses using the actual frontier and
  synchronized strong suffix maps. The wholeBlockExtension and
  amalgamation_nonempty endpoints are unconditional, awaiting Lean checking.

The CI job now audits the generalized base independently before compiling
the relative-space modules. The same runner and dependency build are reused;
this avoids losing an entire axiom audit because a later module fails.
No dependency revisions or proof axioms have been changed. The new relative
theorems are not marked verified pending compilation and transitive audit.
A.3(2), the relative forest pigeonhole step, and the expanded-copy
identification remain outstanding.
