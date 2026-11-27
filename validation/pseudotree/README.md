# Pseudotree validation with mathlib and lean-milliken

This package extends the Lean/Std core with the actual first-order models
in the language `{≤, ∧}`, the proved Halpern–Läuchli input from lean-milliken,
and the generalized diary and copy-space results of the manuscript.

## Main interfaces

See the [statement map](../../docs/Pseudotree-Manuscript-Validation.md)
for the manuscript-to-Lean correspondence and precise scope.

- `RevisedChainDegrees.exact_copy_degree` and `exact_degree`: exact
  degrees for literal copies and embeddings of positive-length chains.
- `RevisedChainDiaries.chainDiary_card`: the count of generalized
  rightmost chain diaries; the independent enumeration is retained.
- `GenericIncomparables.no_finite_bound_of_countable`: the infinite-degree
  theorem under the structural hypotheses. `OmegaFraisse` derives those
  hypotheses from the defining age; there is no separately constructed
  concrete countably branching model.
- The generalized realization, recurrent expansion, IRT, finite Ramsey age,
  minimal unavoidable partition, and native analytic copy-space results
  are mapped in the statement map.

The first five chain degrees are 1, 7, 157, 7,927 and 727,741.

The [audited baseline](https://github.com/janhubicka/lean-pseudotree/commit/fce8813d6341f029520e697eefed1d3e451205f2)
passed the full build and transitive audit of 5,498 declarations.
The [post-validation refactor](../../docs/Post-Validation-Audit.md)
consolidates the reservoir transition arguments and removes the superseded
finite-chain-only assembly. Historical endpoints and their proofs remain
available at the audited baseline. The refactor requires its own full CI
before being treated as a validated replacement.

## Build

From this directory:

```sh
lake update
lake exe cache get
LEAN_NUM_THREADS=2 lake build PseudotreeValidation
lake env lean Checks.lean
```

Apply the documented [import-only dependency patches](import-patches/README.md)
after fetching dependencies and before building, as in CI. These reduce the
memory cost of blanket mathlib imports without changing definitions,
theorems or proofs. Exact dependency revisions are in `lake-manifest.json`;
the compiler is Lean 4.35.0-rc3.

`Checks.lean` audits all declarations in the pseudotree namespace,
including their transitive axiom dependencies. The allowlist is
`propext`, `Classical.choice`, and `Quot.sound`.

## Additional finite checks

```sh
python3 scripts/check_sparse.py
python3 scripts/enumerate_diaries.py
```

These independent finite checks complement the Lean proofs; they do not
establish any infinite Ramsey statement. Historical verification logs
record their original checkpoints, not the current head.
