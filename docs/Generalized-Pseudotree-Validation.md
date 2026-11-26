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

## Eighth batch

Run 45845706438 passed the independent generalized audit (3841 declarations; standard axioms only) and compiled CriticalPullback and CriticalDepth. The only reported failure was the synchronized-slot length calculation in FIFOBoundary, now rewritten explicitly. The independently audited sources have been promoted to main at 69c5ddeab9d8a5a7b44eac92d1af973b1e80275c; unfinished relative modules stay on this branch. CriticalSupport develops retention of genuine fork heights and membership of range prefixes at selected levels, plus the implication from coding-set inclusion to tree-range inclusion. SlotReservoirs constructs an actual rational interval in any live slot and transports it by a ray-preserving map. These are the geometric prerequisites to initialize the relative reservoir continuation in A.3(2), not an assertion that A.3(2) is already verified. New files await exact-head Lean checking.

RelativeReservoirInit constructs a synchronized initial reservoir layer from the incoming slot reservoirs, and proves the explicit prefix and fork support invariants of each subsequent reservoir step. These permit the relative continuation to track selected target heights. The final choice of targets by relevance and the infinite relative assembly remain to be connected to A.3(2).

## Ninth batch

The audited main checkpoint 69c5ddeab9d8a5a7b44eac92d1af973b1e80275c has passed both CI jobs (45853473098 and 45853473115). Branch run 45853957205 again passed the 3841-declaration generalized audit and compiled FIFOBoundary, CriticalPullback and CriticalDepth. RelativeFIFO and CriticalSupport failed on naming, unfolding, dependent rewrite and subtype elaboration issues. This batch addresses those errors; no mathematical theorem was removed or weakened.

New development:
- RelativeTail: glue a fixed finite critical map to a critical tail with explicit local conditions.
- RelativeReservoirRun: iterate the actual rational reservoir transitions starting at a prescribed frontier; preserve each slot's target and record coding, fork and prefix witnesses.
- CriticalAmalgamation: isolate the range-inclusion argument and transport it through arbitrary ambient critical copies, with the relative support construction as an explicit premise.
- RelevantReservoirs: construct the actual target assignments and rational seeds, derive relative support from the reservoir witnesses, and discharge the premise in the A.3(2) endpoint.

These new modules are proof implementations, pending compilation and transitive audit. The stable generalized base remains independently checked; no new axioms or sorry are introduced. The new A.3(2) endpoint is not yet a checked theorem. A.4 and full identification with expanded self-copies remain outstanding.

## Tenth batch

Run 45859052726 again passed the 3841-declaration generalized audit. CriticalPullback, CriticalDepth, FIFOBoundary, RelativeFIFO, and CriticalSupport now compile; the full branch build stopped on elaboration errors in RelativeTail, RelativeSlots, CriticalAmalgamation, and SlotReservoirs. This batch repairs the reported errors without changing the intended mathematical statements.

For A.4, the new RelativeMilliken development starts the existing fibre fusion at the top of a prescribed initial embedding and stops the height induction at the prescribed initial subshape. It uses the already checked mixed boundary product and fibre theorem. NextBlockMilliken instantiates the relative theorem on actual finite whole-block prefixes of R, with the old block fixed; the n=0 case uses ordinary restricted Milliken. SlotSuffixMaps extracts synchronized strong maps from the actual boundary slots of a map fixing the old block and assembles such a family back into a total ray map. These are concrete implementations of the finite-gadget forest input, not yet a proof of the final A.4 statement. The relative lift comparison and extension to all ambient slots remain. The new modules and repairs await exact-head checking.

## Eleventh batch

Run 45861136182 passed the generalized-base audit of 3841 declarations. RelativeTail, RelativeFIFO, CriticalSupport, CriticalAmalgamation and SlotReservoirs now compile, as do CriticalPullback, CriticalDepth and FIFOBoundary. The reported failures were an unused nested-truncation lemma and two dependent coercion rewrites in RelativeSlots. Remove the unused lemma and make the coercion equalities explicit.

SlotTransport constructs the ordered relevant-slot injection with entering-digit preservation, extends synchronized suffix maps to unused ambient slots by zero padding, and proves the exact composition of relative FIFO labels. Its lift_comp compares both the ordinary node label and the critical label (with the preserved split/coding phase). LocalPigeonhole reduces the induced colour to the actual finite next approximation, applies fixed-prefix Milliken for nonempty prefixes and absolute Milliken for the empty prefix, and uses the relative locality identity to control every extension. ConcreteEllentuck transports this argument through arbitrary ambient copies, defines the actual A.4 field and assembles A.1--A.4 with the upstream abstract theorem. No new mathematical axioms or sorry are introduced in the new proof source. The new A.4 endpoint and the concrete assembly still await exact-head compilation and transitive axiom audit, as do some A.3 modules. Identification with the expanded-copy topology, analytic-set transfer and full first-order expansion packaging remain separate obligations.

## Twelfth batch

Run 45862380164 again passed the 3841-declaration audit, and compiled RelativeMilliken, FIFOBoundary, CriticalPullback, CriticalDepth, RelativeFIFO, RelativeTail, CriticalSupport, CriticalAmalgamation and SlotReservoirs. It reported only two errors: a missing local Fintype instance in NextBlockMilliken and a subtype-coercion elaboration in RelativeSlots. Both are addressed in this batch. The full A.3/A.4 endpoint files were not yet reached because of these dependencies.

The new coding-range identification has four components. CodingCover chooses finite coding witnesses for every initial segment, proves all its levels essential, and identifies the initial retained schedule with the original levels. ExpandedCoding reconstructs local ray maps from preservation of labelled normalized codes, proves overlap compatibility by finite unions and assembles the infinite critical map. CodingIdentification proves uniqueness of the extension, reflection of coding points, characterization of the range and order, and forward finite-coordinate control. CodingTopology recovers a finite initial segment of the length-ordered coding enumeration from its range and proves reverse finite-coordinate control and injectivity of the coding-range assignment. These statements work in the explicit relation-level representation: the first-order expansion packaging and analytic-set theorem remain separate. The new reconstruction and topology files await compilation.

The branch CI now independently audits the already compiling relative-geometry modules and fixed-prefix Milliken before the full endpoint build, reusing the same dependency build. This records an additional verified checkpoint even if a later elaboration error remains. No new axioms or sorry declarations are introduced.

## Thirteenth batch

Run 45863816431 passed both the 3841-declaration generalized audit and the 4126-declaration relative geometry audit (only propext, Classical.choice, Quot.sound). It additionally compiled NextBlockMilliken and RelativeSlots, including wholeBlockExtension and amalgamation_nonempty (A.3(1)), outside the independent audit. The exact audited geometry sources were promoted to main at e31f6f4ad691f19007e0244dd364cc0eba8c0311; its own exact-head workflow is running. The full branch build stopped on CodingCover (explicit dependent witness and successor arithmetic), RelativeReservoirInit (Step.critical shadowing the literal critical-node function and two coercions), and SlotSuffixMaps (reserved keyword prefix and level arithmetic). This batch addresses those reported errors and factors out the dependent parent/slot coercion for reuse in the following reservoir assembly.

DiaryRestriction proves labelled normalization of arbitrary subsets is determined by the normalized labelled superset. It constructs the actual finite meet-closed hull using the pairwise-meet lemma, proves that preservation of the manuscript's nonempty meet-closed diary relations suffices for all finite coding subsets, and proves meet-closure reflection under ray maps. This closes the conceptual gap between the relation-level reconstruction hypothesis and the intended relation language, pending compilation. Native first-order symbol packaging, tuple enumeration and the analytic topology transfer remain separate. No new mathematical axioms or sorry declarations are introduced. The branch continues to await full checking.

## Fourteenth batch

Main checkpoint e31f6f4ad691f19007e0244dd364cc0eba8c0311 passed its exact-head core and full runs (45864995029, 45864995240). Branch run 45865112760 again passed both independent transitive audits (3841 and 4126 declarations) and compiled NextBlockMilliken, RelativeSlots, DiaryRestriction, and SlotSuffixMaps. It failed on a dependent membership cast in CodingCover, two ambiguous dotted constructor identifiers in RelativeReservoirInit, and four elaboration errors in SlotTransport (nil append, schedule arithmetic, and implicit take/drop lemmas). This batch repairs those seven reported errors. It also simplifies the pending relevant-slot last-digit calculation and explicitly identifies the source parent before the dependent rewrite, and uses the direct drop lemma in LocalPigeonhole. The upstream published-axiom assembly explicitly supplies nonemptiness for A.3(2) from A.3(1), and disjointness from the complement conclusion in A.4. These are interface adapters, not extra assumptions.

The workflow independently audits the compiled whole-block extension, next-block Milliken, suffix-map representation and meet-closed restriction through CriticalExtensionBase. This permits further promotion without requiring all endpoint files to compile. No proof statements were weakened or admitted. The new repairs and endpoint assembly await exact-head validation.
