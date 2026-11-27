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

## Fifteenth batch

Run 45866695059 passed all three independent audits, with 3841, 4126 and 4314 declarations respectively, all using only standard axioms. The audited whole-block extension checkpoint was promoted to main at b510c7bf606730b06f976540209248ae82b50fa2. The full branch build additionally compiled CodingCover and SlotTransport, including the exact relative FIFO composition identity. It failed on two literal-letter conversion proofs in RelativeReservoirInit, omitted section parameter H in ExpandedCoding (with cascading errors), and unfolding the local colouring in LocalPigeonhole. This batch repairs those reported causes.

DiaryLabels proves label recovery from unlabelled normalized code-set equality and coding-height order, and combines it with the checked meet-closed restriction bridge. DiaryExpansion defines the native first-order language on SparseModel (reduct meet/order, height order, and diary relations indexed by the actual generalized diaries with meet-closed code set), increasing tuple enumeration, and both directions of the named-relation preservation bridge. ExpandedCopyLanguage connects these to the reconstruction by an explicit equivalence of critical maps and native expansion embeddings, and the corresponding range inclusion. The new native packaging and endpoint repairs await compilation. The topological homeomorphism and analytic-set transfer remain separate, and the native IRT/recurrence/finite-age statements still need their final adapters. No new mathematical axioms or sorry declarations are introduced.

## Sixteenth batch

Main checkpoint b510c7bf606730b06f976540209248ae82b50fa2 passed exact-head core and full CI (45867816673, 45867816280). Branch run 45867981360 repeated all three independent audits successfully (3841, 4126, 4314 declarations, only standard axioms). It compiled RelativeReservoirInit and LocalPigeonhole, including the actual local empty/nonempty-prefix homogeneous refinement statements, along with CodingCover and SlotTransport. The three failing modules were DiaryLabels (two local-definition unfolding issues), ExpandedCoding (take length inequality and final subtype length), RelativeReservoirRun (dependent index transport, a retained-level index equation, four literal constructor ambiguities and a last-digit coercion). This batch addresses all eleven reported errors. In particular the dependent reservoir evaluation is expressed through an explicit index-and-proof function so both components are transported together. No theorem statements were weakened.

The workflow replaces the three repeated cumulative audits by a single larger LocalPigeonholeBase audit, which includes all the previously audited modules unchanged and adds the newly compiling CodingCover, relative initialization, transport and local A.4 modules. The final full build runs even if this checkpoint fails. This avoids repeated audits of overlapping declarations and gives a separate independently verified A.4-local checkpoint. The final ambient A.4 endpoint and A.3(2) remain dependent on the full relative iteration; the native expansion, reconstruction and analytic transfer still need checking. Manuscript CI is not required (manual PDF verification by the author).

## Seventeenth batch

Run 45868929249 at e0800b70dede66dc93e116c5c5171426df1d668a passed the cumulative 4470-declaration LocalPigeonholeBase audit, with standard axioms only. The corresponding unchanged audited modules were promoted to main at 479c3ba58f39bf45fa591c18a183f3b99997bf46. The full build additionally compiled RelativeReservoirRun, ExpandedCoding, DiaryLabels and DiaryExpansion. The remaining errors were one dependent existential binder in CodingIdentification (with two cascading errors), and five local unfolding/conditional/letter conversion failures in RelevantReservoirs. All are addressed in this batch. The A.4 ambient transfer is split from the final assembly into AmbientPigeonhole, so it is checked independently of A.3(2). ReconstructionBase cumulatively audits the previously compiled relative continuation, labelled reconstruction and actual native expansion, without repeated earlier audits. No new proof assumptions or placeholders. The new endpoint corrections await exact-head CI. Manuscript PDF verification remains manual.

AnalyticApproximation implements the generic Souslin representation of a prefix-continuous Baire-space image: its scheme sets depend on one finite approximation, so are Ramsey, and the operation is exactly the range by local prefix continuity and separation. It uses the pinned diagonal two-sorted Souslin theorem and the existing fusion-completeness theorem, not a new axiom. AnalyticCopies packages the literal characteristic-function subspace of native expansion self-embedding ranges, obtains a bijection from critical maps, and uses reverse finite-cylinder control to turn continuity of Baire-space parametrizations into prefix continuity. The endpoint uses mathlib's actual AnalyticSet definition. These new transfer proofs await compilation. A native homeomorphism statement (rather than its finite-cylinder criteria and direct analytic transfer) remains to be packaged. No manuscript build is needed in CI.

## Eighteenth batch

The 4470-declaration checkpoint on main (479c3ba58f39bf45fa591c18a183f3b99997bf46) passed its exact-head CI. Run 45870721374 at 5590db2535622c4e26055ba1cb493d1c027f897f passed the cumulative ReconstructionBase build and transitive axiom audit. The unchanged audited reconstruction sources were promoted to main at 4a4f261bde521a16e513a48e06e8ee0c1cb1eab1; manuscript markers have been updated with [skip ci].

CopySpaceTopology separates the native characteristic-function subspace from the analytic transfer, proves continuity in both directions using the existing finite-coordinate bounds, and packages an actual Homeomorph for the discrete AR^omega topology and literal 2^P subspace topology. It also states the exact inclusion identification. NativeRamsey transfers recurrence to actual functional-reduct self-embeddings and code-set IRT to finite native substructure embeddings, including the empty case, using increasing tuple enumeration and rigidity by height. These are new proof implementations, not yet verified. The parent validation has completed; this commit requests a new exact-head run. No new axioms or sorry declarations introduced. The manuscript PDF is checked manually by the author.

The completed parent run 45870721374 recorded 4638 audited declarations (only standard axioms). Its full build compiled CodingIdentification, AmbientPigeonhole, CodingTopology, RelevantReservoirs and ExpandedCopyLanguage. Thus both concrete A.3(2) and ambient A.4, and the native embedding equivalence and finite-cylinder estimates, have compiled. The remaining failures were the implicit argument interface of ofPublishedAxioms, a dependent branch-prefix length rewrite, and the actual namespace of the diagonal Souslin closure theorem (with a cascading error). All three root causes are corrected. ConcreteEndpointBase independently audits the entire assembled concrete Ramsey-space endpoint and native embedding identification before the full topology/analytic/native-Ramsey build. The previous newly triggered validation is superseded by this correction batch; the next exact-head run is required. No change to theorem statements or proof axioms.

## Nineteenth batch

Exact-head run 45871958136 at ebc4a920ebde792970709c8d60c667eff08d163d
successfully built ConcreteEndpointBase and audited 4709 declarations.
In particular the unconditional concrete A.1--A.4 package, concrete_ellentuck,
and the identification with native expansion self-embeddings all passed,
using only propext, Classical.choice and Quot.sound. The full build stopped
on four elaboration errors in CopySpaceTopology (bounded-subtype finiteness,
the point type in continuity, the discrete cylinder type and dependent
Sigma equality), and one local-definition rewrite in NativeRamsey.
This batch addresses those five errors without changing the statement,
including explicit projection at the fixed approximation level rather than
rewriting through a dependent Sigma constructor. The final homeomorphism,
analytic-set transfer and native IRT endpoints still await exact-head
compilation and the full namespace-wide audit. No new axioms or sorry
declarations are introduced. The validated main branch remains untouched
pending that check.

## Twentieth batch

Exact-head run 45887624247 at 13f370540c512a3efc7a6e23382e9fd33912027f
again audited 4709 declarations using only the standard axioms.
CopySpaceTopology, NativeRamsey and AnalyticApproximation all compiled.
AnalyticCopies failed on duplicate local instance names, recovery of
one branch coordinate, and two rewrites through the semireducible
system.Point projection. This batch repairs these five errors with
distinct local instance names, explicit list-coordinate recovery and
typed maps into and out of the actual approximation system.

The independent anchored branch run 45888156631 at
dd0e53135f290151edb0700d24ddac1e2a6c978a compiled AnchoredOscillation.
NoInfiniteCanonical reported only two coercion/rewrite errors in
anchored_embeddings; explicit inequalities in the ambient carrier
repair them. The anchored and copy-partition-transfer sources (the latter
from 71808dcb328bd454e1173600dd21e8b468ee740d) are incorporated in this
branch in one batch to avoid duplicate CI dependency builds. The final
analytic, native Ramsey and noncanonization endpoints await the combined
full build and transitive audit. No new assumptions or admissions.

## Twenty-first batch

Run 45892677344 at a349109f87f35a94fa46da6f11fd9b607115b2e7
again passed the 4709-declaration concrete audit, and compiled
AnchoredOscillation, NoInfiniteCanonical, CopySpaceTopology, NativeRamsey
and AnalyticApproximation. Only two modules failed: CopyPartitionTransfer
(one elaboration of a subtype extensionality argument), and AnalyticCopies
(doc-comment placement and implicit Ramsey quantifier application).
These three errors are addressed directly. The next independent audit
includes all the previously compiled endpoints and explicitly checks
the transitive dependencies of the abstract analytic-image theorem.

GenericAvoidance implements the remaining structural finite-set avoidance
argument for countable ultrahomogeneous meet-trees with no endpoints:
adjoin a formal bottom, embed every finite substructure by replacing bottom
with a common strict lower bound, and use the existing mathlib extension-pair
construction to embed the enlarged countable tree with prescribed bottom.
The resulting self-embedding avoids the finite forbidden set above a chosen
point not below any forbidden point. Both embedding and literal-copy
noncanonization endpoints are stated without a finite-avoidance hypothesis.
These new implementations await compilation and audit; no new assumptions
except the explicit usual structural hypothesis of no minimal points.
A separate concrete Fraisse identification of the countably branching
pseudotree remains outside the verified model scope.

## Twenty-second batch

Exact-head run 45894948513 at 48ba4c1df26d091ab7a52359bdae8519002960a0
passed the expanded independent audit of 4794 declarations, including
the homeomorphism, native IRT and recurrence, abstract analytic-image
argument, anchored oscillation and the binary embedding obstruction.
Both AnalyticCopies and CopyPartitionTransfer compiled successfully in
the full build. The only failing module was GenericAvoidance. The errors
were constructor alternatives for WithBot (bot/coe rather than none/some),
the inline tactic layout for the constant singleton embedding, and the
coercion from the composed embedding into the finite forbidden set.
This batch repairs these causes, and includes both compiled adapters
in the independent audit.

The previously audited module blobs have been promoted to main at
f7d8286dfde16b5239ebcb754ffed934d8d45755 without a duplicate build. This commit incorporates that
promotion as an additional parent, preserving the new work in the branch.
Generic finite-avoidance and countable-model endpoints await compilation.
No new axioms or admissions.

## Twenty-third batch (source only; previous CI retained)

The manuscript defines Psi_omega as the Fraisse limit of all finite
meet-trees, not as a particular explicit word model. OmegaFraisseApplication
specifies this age intrinsically, derives comparable predecessors from
membership of a finitely generated substructure in the age, and derives
nonemptiness, no endpoints, density and the second-branch property using
only the one-, two- and three-point chains and the fork in the age.
It invokes the existing generic profile and no-universal-copy-partition
theorems at the actual defining Fraisse-limit interface, without requiring
the caller to establish those geometric properties. The ambient order
and meet remain explicitly interpreted, as in the manuscript.
This is not a new construction or proof of existence of the Fraisse limit
of the full class. Compilation and the transitive audit are pending.

The literal FIFO queue in the current manuscript has the same schedule
and passing digits as the existing Lean queue; changing the binary
in-order relation is not literally a coordinate swap on that fixed queue.
The coordinate-swap observation identifies the full word models and
reflected diary shapes, but the concrete revised sparse model and its
transport require separate verification. Relative/partial markers
must remain until that is checked. No new proof assumptions or admissions
are introduced in this batch. It does not interrupt run 45896002915.

## Literal revised sparse convention batch

RevisedSparseGeometry implements the literal comparison 0 < end < 2
and proves its conjugacy with the original word model by reflection.
The meet-closure argument uses the existing queue separator-origin
invariant, independent of order. The local geometry is ported from
SparseOrder with the first and third queue children exchanged in their
roles (not in their literal positions); the fork uses the middle and
third children. The queue, coding lengths and passing digits are exactly
the existing source. RevisedSparseModel then applies the checked generic
finite-extension argument to this actual revised range, including native
Fraisse identification and the self-embedding with that precise range.
These are new proof implementations, pending compilation and audit.
The generalized diary grammar, normalization and native expansion
transport to the new orientation are not yet checked as literal
revised statements. No new axioms or admissions.

Run 45896002915 at 598926e3b3e35cf28cd4d47172c09ca4ab948c1b
passed the independent audit of 4822 declarations, including the native
analytic and copy-level endpoints. The audited sources are promoted
to main at efb60dce0916937b3575fd01648f2c4490a8dded. The full build reported only one error in
GenericAvoidance, proving that bottom belongs to the literal singleton
substructure. The proof is now explicitly changed to singleton set
membership. This batch triggers one CI run for that repair together
with OmegaFraisseApplication and the revised sparse model. No
admissions or new mathematical axioms.

## Revised native diary expansion batch

The raw finite diary grammar, normalized code-set Ramsey theorem,
critical-copy reconstruction, approximation system and Ellentuck
axioms depend only on the literal tree and its FIFO queue. They are
reused unchanged. RevisedCodingRelations proves conjugation of a
ray-preserving strong map by digit reflection, and supplies the revised
meet operation, finite meet hull, closure reflection and named-diary
restriction bridge. RevisedDiaryExpansion interprets the literal
meet-closed diary language on the revised sparse model. The native
embedding equivalence, finite IRT, metric homeomorphism and analytic
copy-set theorem are then adapted from the checked native interfaces.
The old proofs are not modified. No additional Ramsey assumptions are
introduced. Recurrence in arbitrary revised reduct copies, the exact
rightmost-chain diary characterization, and the finite age Ramsey
corollary remain separate tasks. All revised adapters await the compiler
and axiom audit. This source-only batch preserves run 45897025781.

## Repairs and consolidated CI

Run 45897025781 (job 140173342358) at 10cbfc073920893973c36a9e8740b6fa3143dd26
again passed the 4822-declaration independent audit. GenericAvoidance
compiled, including the countable embedding and literal-copy
noncanonization endpoints without the auxiliary avoidance premise.
It is now imported by the independent audit entry point.
The full build reported one simplification error in RevisedSparseGeometry
(the binary comparison induction hypothesis, after unfolding flipBits)
and errors in OmegaFraisseApplication (implicit bundled structures,
the change through a bundled carrier, and missing decidability of the
fork order). The repairs give explicit bundles, use the age witness
directly, prove fork comparability by its defining root/equality
relation, and prove the two strict inequalities by le and ne.
The next full CI also includes the source-only revised native adapters.
Their compilation and the transitive audit remain pending.
No new admitted declarations or new proof axioms have been added.

## Chart-independent recurrence batch

The independent 4822-declaration audit at 10cbfc073920893973c36a9e8740b6fa3143dd26 passed; GenericAvoidance compiled. The parallel revised-native-expansion and six-error repair batch at e2c321f161b88315b73ac874e27495eb17d72f1f has been retained unchanged. LowerSplit factors the existing ray splitting proof through the prefix-antichain property; the original sparse_split remains a specialization. ReservoirChart discharges revised common-prefix, split and turn geometry by reflection, without reflecting the actual FIFO tree. ChartReservoir is the common generalization of the audited transitions and recurrence, reusing the exact source, frontier indices and ordered-child proof. The previously checked orientation-specific implementation is retained while the generalized version is checked; the duplicated orientation-independent proof body is temporary migration scaffolding. RevisedRecurrence proves recurrence of all normalized finite code sets and implements the native recurrence endpoint in the revised expansion. These new proofs await compilation and audit; the already checked A.1--A.4 on critical maps do not need to be duplicated, because their approximation system and tree geometry are unchanged. No new axioms or admissions. This source-only batch uses [skip ci] to preserve the in-flight run 45897989735. Manuscript PDF verification remains manual.

## Revised endpoint audit and finite age compactness

Exact-head run 45897989735 (job 140176540455) at
e2c321f161b88315b73ac874e27495eb17d72f1f passed the independent audit
of 4832 declarations, including generic finite-set avoidance and the
countable noncanonization endpoints. All seven revised geometry/model/
native expansion adapters compiled in the subsequent full build.
The only failing module was OmegaFraisseApplication: three occurrences
of the inferred subtype LE were inconsistent with the semilattice
witness supplied by age membership. The repair explicitly uses that
witness's LE and both semilattice instances in embedding_le_iff.
The independent audit is extended to the already compiled revised
endpoints. The separate recurrence batch at 305f063f930ca3863ddedfda239f32241371fa9f
is retained.

RevisedAgeRamsey implements the remaining finite Ramsey-age corollary
by compactness of the space of colourings, with finite discrete
codomain. Native IRT covers it by open sets indexed by actual B
embeddings. A finite subcover and finite meet hull give a finite
witness C, in the literal revised expanded language. This works even
when the expansion has infinitely many symbols, and includes the
empty substructures. The new proof and chart recurrence await CI.
No new admissions or mathematical axioms.

## Rightmost chain-diary batch

RevisedChainDiaries implements reflection of raw finite generalized
diagrams, including the actual lexicographic passing rule at each level.
The revised order forces the rightmost-original condition: if a
continuing critical word had an earlier zero, it would have a coding
descendant containing a later one, and a coding descendant on the
right side of that earlier split (or the critical node to its right).
Their two prefixes of equal length are lex-separated and the later
one-turn makes the two coding points incomparable. The right-original
node is unique at each level; the generalized adjacent-turn rule
therefore forces the original chain turn restriction. Reflection
identifies the resulting literal generalized chain diaries bijectively
with the independently enumerated PaperDiary, giving the exact count.
This does not reflect or replace the actual FIFO queue. All new proof
implementations await Lean and the axiom audit. Source-only commit
preserves the current CI run. No new axioms or admissions.

## Revised normalized chain degree assembly

Run 45899356350 at 1026d1d6021999d5acaec3b64f11c0276787dac1
audited 5110 declarations; both OmegaFraisseApplication and
RevisedAgeRamsey compiled. The sole failure was the unqualified
.one literal in ReservoirChart.opposite_continuation. It is now
explicitly typed. The audited exact blobs have been promoted to
main at 5ef68d4a56f6aba5d963021c4905a56a75aca186. The independent audit now additionally imports
the two compiled modules above.

RevisedChainDegrees implements the exact literal normalized
chain partition on the actual revised sparse model. It obtains
matching bounds directly from generalized finite-fragment
canonization, the finite chain-diary equivalence, and recurrence.
The normalized type map has the exact code set, realizes every
chain diary, and each class is unavoidable. No abstract
isomorphism is used to identify the two literal queues. This
proof and the revised rightmost characterization and recurrence
remain to be compiled. No new axioms or admitted declarations.

## Compiled recurrence and literal copy partition

Run 45901118297 (job 140186851626) at fb35337011cb34c20f581dfd0eb863cc08bd73b4
passed the independent audit of 5142 declarations, including the
countable Fraisse application and revised finite Ramsey-age theorem.
Those exact sources are now on main at 9890506e49cc431e30c63c584531aa1fd001e453.
ReservoirChart, ChartReservoir and RevisedRecurrence compiled.
The only failing source was RevisedChainDiaries, with errors at five
locations: decidability of PaperKind.special, two dependent-if
simplifications, the explicit prefix-length argument, and a numeral
coercion. All five are repaired in this batch. The exact chain
degree assembly remains downstream of that module. The independent
audit now includes the already compiled revised recurrence.

RevisedCopyCanonization implements the manuscript's minimal
unavoidable diary partition on literal copies of arbitrary nonempty
finite functional A. It proves range independence of the coding
sets, recurrence of every realized label, simultaneous finite
fragment canonization inside an arbitrary prescribed reduct copy,
impossibility of a proper unavoidable refinement, and a finite
colouring witnessing sharpness. It works for nonrigid A as well.
The endpoint uses realized labels (rather than a separate proof
that every abstract diary of type A is realized). The new proofs
and exact chain assembly await compilation and cumulative audit.
No admissions or new axioms are introduced.

## Audited recurrence and the abstract diary realization interface

Run 45902825240 (job 140192444532) at d1468d3c52b06441405b56c75fbc5ccbbdf9c463
passed the independent audit of 5336 declarations, including native
revised recurrence. The audited blobs are promoted to main at bc373c870701090b29a8fa05fe406224e08ba1c7.
RevisedChainDiaries and RevisedCopyCanonization compiled in the same run.
The sole failing module, RevisedChainDegrees, required an explicit
Point membership witness and the GenericIncomparables import.
Both underlying issues have been repaired. The next independent
audit imports the already compiled chain-diary and copy partition
modules as well.

RevisedDiaryRealization implements the abstract pair (D,iota) in the
manuscript. Every pair with the correct code-set range is realized
with its prescribed labels using the finite FIFO lift. Conversely,
the normalization inverse factors the original finite embedding
through an actual revised-model ray embedding, recovering the
normalized labeled embedding. The realized copy-label range equals
the abstract diary code sets of A. Nonprecompactness for every
nonchain follows directly from the checked oscillation colourings
and finite-fragment canonization: finitely many labels would bound
the palette of every image-invariant colouring. This avoids a
separate infinite-fork diagram enumeration. These new endpoints
and the repaired exact degree theorem await CI. Identification
of equality of the entire induced expanded relational structure
with equality of the labeled pair remains a separate packaging
step. No new admissions or mathematical axioms.

## Final labeled expansion classification batch

Run 45908856042 (job 140212066348) at 189d10e5cea245d1ece626f046311ad2c59c9037
audited 5403 declarations using only the standard axioms, including
the revised chain-diary count and native minimal unavoidable copy
partition. Those exact audited blobs are now on main at fd3a32fbf1e649253583280df4e756652644facd.
RevisedChainDegrees compiled. The sole error in RevisedDiaryRealization
was an equality in the wrong direction in a Finset.mem_image witness;
it is repaired. The independent audit now includes both modules.

RevisedExpansionClassification implements the induced expanded
first-order structure on the fixed finite reduct. Equality of the
full named diary relation and the coding-height order determines
every normalized label. Conversely the restriction identity and
ray-map recovery show that the full set of labeled normalized
words determines the interpretation of every relation, including
on non-meet-closed tuples. Realization and normalization then
provide an explicit equivalence between independently specified
labeled diary pairs and actual induced expanded structures on A.
The proof is drafted, awaiting compilation and cumulative audit.
No new mathematical axioms or explicit admissions.

## Audited exact revised degrees; classification repair

Run 45921125425 (job 140251844386) at ec8cff90e6ea471e6101b6c37e43e9818a20d3f4 passed the
5439-declaration independent audit. The exact revised chain degree,
abstract labeled realization and normalized pair, characterization
of realized labels, and infinitely many labels for each nonchain
are checked; those exact blobs have been promoted to main at 43dcece03adbdb21a8f1a1832b04fe2cfb978a7a.
The classification module reported missing noncomputable on
the label definition and unqualified FirstOrder.Language.Structure.RelMap.
Both underlying errors are repaired. The next run checks the repaired
full induced-expansion classification. No new axioms or admissions.

The statement-level adapters RevisedChainCopyDegree and RevisedLocalBRS
compare actual literal-copy palette bounds with the embedding bounds
(using rigidity of chains), and derive labeled unavoidability and
canonization on a fixed expansion fiber inside any prescribed reduct
copy. Both await compilation. The latter uses no additional Ramsey
assumptions, only the audited finite-fragment result and classification.

RevisedWordLex states the lexicographic and separator-prefix clauses
directly in the literal revised order. GeneralizedSubsetNormalization
extends the checked sparse normalization statement to subsets of any
abstract generalized diary: lift that whole diary using the checked
FIFO construction, normalize the subset image, and use naturality.
These are direct manuscript-facing adapters, not new mathematical
assumptions; compilation and audit are pending. This commit triggers
one consolidated run of the repairs and adapters.

## Final compiler repairs (2026-11-27)

Exact-head run [45983941867](https://github.com/janhubicka/lean-pseudotree/actions/runs/45983941867)
(job 140454619748) at 58307f5464e4164deec7afbf7a1e39bdf1bbc08d passed
the independent 5439-declaration transitive audit. The core job audited
1312 declarations. The full build compiled RevisedChainCopyDegree and
GeneralizedSubsetNormalization. The remaining source errors were at
two locations: RevisedExpansionClassification's equality of relation
projections needs its implicit arity binder retained (explicit @);
RevisedWordLex's reflected singleton needed direct rewriting instead
of broad simplification (which expanded the singleton to a cons with
a reflected empty tail). Both are repaired. The next independent audit
includes the two successfully compiled adapter modules. The local BRS
module remains downstream of the classification. No proof obligations
were weakened, and no new axioms or admissions were introduced.

## Completed final validation

The exact-head [full CI run 45985075218](https://github.com/janhubicka/lean-pseudotree/actions/runs/45985075218)
(job 140458485649) at `fce8813d6341f029520e697eefed1d3e451205f2` succeeded. Both builds completed with
9,312 jobs. The independent endpoint audit covered 5,446 declarations
and the final cumulative audit covered **5,498 declarations**. Only
`propext`, `Classical.choice` and `Quot.sound` were permitted.
The exact audited commit was fast-forwarded to main. The core run
45985075053 also passed.

The last five adapters are all compiled and included in the final
audit: literal-copy chain degree, arbitrary-diary subset normalization,
revised word order and separator-prefix clauses, induced-expansion
classification, and local labeled generalized BRS. The manuscript
at `32ff5e7e1f09323aa6bdc9f2c10cbca83fe04963` pins this exact audited Lean commit. The
[statement map](Pseudotree-Manuscript-Validation.md) records the final
scope. The countably branching application uses the defining Fraisse
age, not a separately constructed concrete model; the abstract
explanatory BRS equivalences are not independently formalized.
All concrete main theorem endpoints are audited. No pending compiler
errors or new axioms in the full aggregate.

This documentation-only commit leaves the audited Lean files,
toolchain, dependency pins and workflow unchanged.

## Post-validation consolidation

The exact audited replacement `09b7edf67a466e97f52a4d946d17bb86e88c9fca` passed full CI
[45991877707](https://github.com/janhubicka/lean-pseudotree/actions/runs/45991877707):
5,113 independent endpoint declarations and 5,165 cumulative
declarations, only standard logical axioms. The former 5,498
declaration total included superseded chain-only and duplicated
reservoir proof assemblies. See [Post-Validation-Audit.md](Post-Validation-Audit.md)
for the cleanup history, independent import-patch integrity check,
and remaining scope qualifications. The manuscript pins the new
verified source at `fe3ed30e12dbee44ac093cc04a045a3abfe3d7a3`. Concurrent Boolean-algebra
companion additions are preserved in the merge to main.
