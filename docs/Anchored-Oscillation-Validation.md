# Anchored oscillation and the no-universal-canonization theorem

This independent branch is based on the green main checkpoint 4a4f261bde521a16e513a48e06e8ee0c1cb1eab1.
It deliberately does not interrupt the in-flight critical-copy-space build.

* AnchoredOscillation: prove a final segment of oscillations for two
  nonempty independently end-extensible finite-set families; show that each
  fixed cone inherits the existing RichSubset conditions, and cross-cone
  meets remain equal to the prescribed anchor.
* NoInfiniteCanonical: elementary binary digit prescription with arbitrary
  lower bound; anchored realization by actual functional embeddings; the
  four-colour diagonal contradiction for unavoidable Nat-valued partitions.
  The generic theorem states rank avoidance explicitly. For the concrete
  ternary model rank avoidance is derived from literal prefix shifts.

The native embedding obstruction and anchored lemma are proof implementations,
not yet Lean-verified. The transfer from copy partitions to embedding partitions
and the generic countably branching model's finite-avoidance argument remain
to be formalized. No admissions or new mathematical axioms are intended.

## Copy-level transfer batch

CopyPartitionTransfer defines copies as literal embedding ranges, constructs
the factor through a containing embedding using mathlib's equivRange, and
indexes the fibre over any copy by self-embeddings of the finite pattern.
This proves the exact image-level obstruction using a finite tuple of
four-colour values. It does not assume rigidity or require that the chosen
representatives commute with ambient embeddings. The generic transfer
works independently of the pseudotree geometry and the concrete endpoint
uses ternary_no_universal_partition. All added proofs await compilation.
The generic countably branching application still requires finite-set
avoidance or a concrete model construction. The prior CI is intentionally
not cancelled by this source-only batch.
