# Lean verification of the pseudotree paper

Companion to the pseudotree manuscript in `janhubicka/pseudotree`.

This repository contains the complete existing pseudotree formalization migrated from `janhubicka/lean-all-those-big-Ramsey-degrees` at commit `44585ec2fb84d6cd2cbc1a4ec35a378dc9f5f26c`. Existing module paths and declaration names are preserved. The small shared `AllThoseBigRamsey/Relational.lean` module is copied unchanged to make the project independent; its original stays in the source repository. The `all_those_big_ramsey` Lake package name is retained for compatibility with the nested package's lockfile.

## Build and audit

- Lean/Std core: `lake build` and `lake env lean PseudotreeChecks.lean`.
- Full model, exact chain big Ramsey degrees, and infinite-degree theorem for nonchains: follow the [mathlib/Milliken build instructions](validation/pseudotree/README.md).
- [Manuscript statement map](docs/Pseudotree-Manuscript-Validation.md) and [mathematical audit](docs/Pseudotree-Audit.md).

The historical verification logs and hashes under `validation/pseudotree/verification/` describe the original validation checkpoint, not a fresh run in this repository. The imported proofs are unchanged; new CI runs check the migrated package. The audited generalized development includes the concrete Ellentuck theorem, native expanded-copy homeomorphism, native IRT and recurrence, and the native analytic-set theorem and the binary copy-level noncanonization theorem. The literal revised orientation's sparse Fraisse model, native IRT, homeomorphism and analytic Ramsey theorem have also passed the independent audit. See [generalized validation checkpoints](docs/Generalized-Pseudotree-Validation.md) for exact coverage and outstanding adapters.
