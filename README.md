# Lean verification of the pseudotree paper

Companion to the pseudotree manuscript in `janhubicka/pseudotree`.

This repository contains the complete existing pseudotree formalization migrated from `janhubicka/lean-all-those-big-Ramsey-degrees` at commit `44585ec2fb84d6cd2cbc1a4ec35a378dc9f5f26c`. Existing module paths and declaration names are preserved. The small shared `AllThoseBigRamsey/Relational.lean` module is copied unchanged to make the project independent; its original stays in the source repository. The `all_those_big_ramsey` Lake package name is retained for compatibility with the nested package's lockfile.

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
copy-space theorem. The last independent audit checked 5,439 pseudotree
declarations at [43dcece03adb](https://github.com/janhubicka/lean-pseudotree/commit/43dcece03adbdb21a8f1a1832b04fe2cfb978a7a).
See [the current statement map](docs/Pseudotree-Manuscript-Validation.md)
and [the cumulative audit ledger](docs/Generalized-Pseudotree-Validation.md)
for remaining statement-level obligations and exact-head build results.
