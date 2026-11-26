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
