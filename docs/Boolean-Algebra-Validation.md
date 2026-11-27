# Boolean algebra companion: formal validation

This development accompanies [boolean-algebra.tex](https://github.com/janhubicka/pseudotree/blob/main/boolean-algebra.tex).

## Scope

The three modules contain **42 proved theorems** over Lean/Std:

| Module | Theorems | Mathematical content |
| --- | ---: | --- |
| Boundary | 6 | Boundary-event filtering under atom quotients, composition, and extraction from interval-label words |
| Frontier | 7 | Finite support/germ states, preservation of valid states, splits and terminal cells under coarsening |
| SignRuns | 29 | Signed-word concatenation, reversal, sign change, reflected blocks, and run-count lower bounds |

A frontier support is represented as a finite list and interpreted through membership. Order and repeated labels in that list are semantically irrelevant. Validity of states and legality of splits are explicit predicates; these files do not assume every abstract infinite path represents a clopen element.

## Relation to the manuscript

- Functorial Boolean coarsening: checked by Boundary.coarsenEvent_comp, Boundary.coarsenWord_comp, boundaryFrom_coarsen, and the Frontier coarsening lemmas.
- The growth in the high-run cut construction: the finite word inequality is SignRuns.remove_block_growth.
- The invariant for new Boolean unions in relative avoidance: the finite subword inequality is SignRuns.middle_runs_le.
- The reflected-block example: SignRuns.reflected_blocks_runs proves the exact multiplication of runs per depth; flatten_runs_lower proves the possible loss when depth blocks are concatenated.

Namespace prefixes are AllThoseBigRamsey.BooleanAlgebra. Boundary declarations are directly in that namespace.

These are finite semantic and word-algebra checks. **Not yet formalized:** the interval representation, finite interval realization, high-endpoint selection, modular residue theorem, atomless partition fusion, Devlin's theorem and its Boolean transfer, the infinite reflected embedding, and the requested recurrent diary Ramsey theorem.

In particular no checked theorem asserts that the proposed raw endpoint records are recurrent. The manuscript proves that exact signed-run types are avoidable.

## Local validation

Compiler: Lean 4.35.0-rc3, matching lean-toolchain.

From this repository:

    lake build
    lake env lean BooleanAlgebraChecks.lean

The twelve principal declarations audited in BooleanAlgebraChecks.lean depend only on propext and, where needed, Quot.sound. There are no sorry, admit, new axioms, or mathematical assumptions replacing unproved Ramsey theorems. The recorded output is in verification/boolean-algebra/axioms.txt.

The full root build completed successfully with 31 jobs, including the existing root pseudotree modules and the new Boolean imports. The separate BooleanAlgebraChecks.lean run and the Boolean umbrella module also exited successfully.

The Boolean modules are imported by AllThoseBigRamsey.BooleanAlgebra and by the root library, so the normal root build includes them. The existing nested pseudotree validation package has not been changed.

## Remaining development

The next infinite proof should use actual compatible finite Boolean partitions, with explicit splitting of every nonzero element and finite supports for every chosen element. A Ramsey theorem for an unwitnessed tree section cannot replace the missing Boolean transfer.

The upper target remains one-type canonization for unavoidable normalized types, hence finite-family canonization. No simultaneous canonization of a countably infinite family is claimed.

## Assistance

This initial formalization was produced with ChatGPT and locally checked by Lean. The finite theorem scope above is separate from the independent mathematical audit of the English draft.

