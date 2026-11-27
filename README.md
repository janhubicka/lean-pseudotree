# Lean verification of the pseudotree paper

Companion to the pseudotree manuscript in `janhubicka/pseudotree`.

This repository contains the complete existing pseudotree formalization migrated from `janhubicka/lean-all-those-big-Ramsey-degrees` at commit `44585ec2fb84d6cd2cbc1a4ec35a378dc9f5f26c`. The maintained main results retain their declaration names; superseded intermediate proof assemblies are removed in the post-validation refactor. The small shared `AllThoseBigRamsey/Relational.lean` module is copied unchanged to make the project independent; its original stays in the source repository. The `all_those_big_ramsey` Lake package name is retained for compatibility with the nested package's lockfile.

## Build and audit

- Lean/Std core: `lake build` and `lake env lean PseudotreeChecks.lean`.
- Full model, exact chain big Ramsey degrees, and infinite-degree theorem for nonchains: follow the [mathlib/Milliken build instructions](validation/pseudotree/README.md).
- [Manuscript statement map](docs/Pseudotree-Manuscript-Validation.md) and [mathematical audit](docs/Pseudotree-Audit.md).

The historical verification logs and hashes under
`validation/pseudotree/verification/` describe older checkpoints.
The revised development now covers the literal unchanged FIFO queue,
exact chain degrees, generalized diary realization, recurrent native
expansion, IRT, finite Ramsey age, non-precompactness, minimal unavoidable
copy partition, the concrete Ellentuck theorem and the native analytic
copy-space theorem. The consolidated proof development passed the cumulative audit of **5,165 pseudotree declarations**
at [09b7edf67a46](https://github.com/janhubicka/lean-pseudotree/commit/09b7edf67a466e97f52a4d946d17bb86e88c9fca),
including exact literal-copy chain degrees, the induced-expansion
bijection and local generalized BRS, with only standard logical axioms.
[Full CI passed](https://github.com/janhubicka/lean-pseudotree/actions/runs/45991877707).
See [the current statement map](docs/Pseudotree-Manuscript-Validation.md)
and [the cumulative audit ledger](docs/Generalized-Pseudotree-Validation.md)
for statement-level scope and exact-head build results. See also the [post-validation audit and refactor](docs/Post-Validation-Audit.md).

## Boolean algebra companion

The same repository now also contains the initial finite interface for the Boolean algebra companion: boundary-event coarsening, support/germ types, and signed-word identities. See [Boolean algebra validation](docs/Boolean-Algebra-Validation.md) for the 42 proved finite lemmas, build commands, and the exact limits of what is formalized. The unrestricted recurrent Boolean diary theorem is not claimed.

