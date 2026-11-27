# Boolean algebra companion: formal validation

This development accompanies [boolean-algebra.tex](https://github.com/janhubicka/pseudotree/blob/main/boolean-algebra.tex).

## Scope

The five modules contain **61 proved theorems** over Lean/Std:

| Module | Theorems | Mathematical content |
| --- | ---: | --- |
| Boundary | 6 | Boundary-event filtering under atom quotients, composition, and extraction from interval-label words |
| Frontier | 7 | Finite support/germ states, preservation of valid states, splits and terminal cells under coarsening |
| SignRuns | 29 | Signed-word concatenation, reversal, sign change, reflected blocks, and run-count lower bounds |
| DevlinTransfer | 4 | Abstract equivariant transport of IRT, preservation under composition, finite iteration, and a finite palette factorization |
| BlockSchemes | 15 | Triangular Boolean block products, the scalar-product criterion under coefficient uniqueness, and composition of incidence and base-character profiles |

A frontier support is represented as a finite list and interpreted through membership. Order and repeated labels in that list are semantically irrelevant. Validity of states and legality of splits are explicit predicates; these files do not assume every abstract infinite path represents a clopen element.

## Relation to the manuscript

- Functorial Boolean coarsening: checked by Boundary.coarsenEvent_comp, Boundary.coarsenWord_comp, boundaryFrom_coarsen, and the Frontier coarsening lemmas.
- The growth in the high-run cut construction: the finite word inequality is SignRuns.remove_block_growth.
- The invariant for new Boolean unions in relative avoidance: the finite subword inequality is SignRuns.middle_runs_le.
- The reflected-block example: SignRuns.reflected_blocks_runs proves the exact multiplication of runs per depth; flatten_runs_lower proves the possible loss when depth blocks are concatenated.
- The native endpoint Ramsey theorem: DevlinTransfer.transfer_irt proves the abstract transport once the source Ramsey theorem, occurrence equivalence, and equivariance are supplied. The concrete Boolean correspondence remains an English proof.
- Finite-family upper bounds: DevlinTransfer.finite_family and finite_family_factorization prove iteration under a common composition action and factorization through the chosen type index.

- The Boolean block presentation: BlockSchemes.triangular_product_expansion computes the coefficients of a product of two block sums. The scalar-product converse explicitly assumes coefficient uniqueness; independent bases supply it.
- Block substitutions: BlockSchemes.uniformProfiles_comp and baseProfiles_comp prove compatibility under composition. condensed_base_products and condensed_triangular prove the resulting actual Boolean multiplication identities.

Namespace prefixes are AllThoseBigRamsey.BooleanAlgebra. Boundary declarations are directly in that namespace.

These are finite semantic, word-algebra, and block-product checks together with an abstract Ramsey transfer. BlockSchemes uses actual Boolean characteristic functions with XOR addition and conjunction multiplication; its finite list identities do not assume an infinite Ramsey principle. **Not yet formalized:** the interval representation, finite interval realization, high-endpoint selection, modular residue theorem, atomless partition fusion, cofinal Boolean block embeddings and fair splitting, Hindman/Milliken--Taylor, Devlin's theorem, the concrete interval/endpoint occurrence equivalence and embedding correspondence, the infinite reflected embedding, and the requested recurrent diary Ramsey theorem. The source IRT, occurrence equivalence, and action laws in DevlinTransfer are explicit hypotheses, not new axioms or claimed formalizations of those results.

In particular no checked theorem asserts that the proposed raw endpoint records are recurrent. The manuscript proves that exact signed-run types are avoidable.

## Local validation

Compiler: Lean 4.35.0-rc3, matching lean-toolchain.

From this repository:

    lake build
    lake env lean BooleanAlgebraChecks.lean

The twenty-five principal declarations audited in BooleanAlgebraChecks.lean depend only on propext and, where needed, Quot.sound. The two basic transport lemmas are axiom-free. There are no sorry, admit, or new mathematical axioms. The recorded output is in verification/boolean-algebra/axioms.txt.

The local root build includes the existing root pseudotree modules and the Boolean imports. The build and principal-axiom results for this checkpoint are recorded in verification/boolean-algebra/validation.json.

The Boolean modules are imported by AllThoseBigRamsey.BooleanAlgebra and by the root library, so the normal root build includes them. The existing nested pseudotree validation package has not been changed.

## Remaining development

The manuscript now proves a native IRT theorem for a coherent Devlin endpoint expansion, with full coverage of its finite occurrences. Its exact endpoint types are avoidable in arbitrary bare Boolean copies.

The manuscript now supplies cofinal block embeddings over frozen finite prefixes, exact tail-reservoir coverage, and a local Hindman theorem for splitting diagrams. These are English proofs. The unrestricted Ramsey construction must additionally preserve colour decisions through both child reservoirs and retain fairness and full occurrence coverage. Every two-atom copy is a block image of the first split, so all block maps cannot be taken as the diary-preserving monoid. Coarsening endpoint types requires additional Boolean embeddings: any two distinct fine types remain unavoidable if outputs are restricted to interval-generated copies.

The upper target remains one-type canonization for unavoidable normalized types, hence finite-family canonization. No simultaneous canonization of a countably infinite family is claimed.

## Assistance

This initial formalization was produced with ChatGPT and locally checked by Lean. The finite theorem scope above is separate from the independent mathematical audit of the English draft.

