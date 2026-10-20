# Eventual periodicity of linear generalized Stone–Wales paths in affine fullerene families with convex lattice-face decompositions

**Tatsuhiko Takimoto** (independent researcher)

This repository contains a paper and its verification packet. It is the second of two papers. The first, on the family $\mathrm{GC}(k,l)[C_{20}]$, is at [tkmt-lab/a3-gsw-classification](https://github.com/tkmt-lab/a3-gsw-classification).

> **Theorem 1a (convex lattice-face rays).** Consider a fullerene dual that, for all sufficiently large integers $t$, decomposes into a fixed finite number of embedded convex lattice polygons with sides in the six triangular-lattice directions. The corner coordinates and gluing translations are integer affine in $t$, the rotations and side pairings are fixed, and all degree-five vertices are marked corners. Then the set of $t$ for which a literal linear generalized Stone–Wales path exists is eventually periodic.
>
> **Corollary 1b.** Path existence is eventually periodic on every integer affine ray in the valid domain of each of eleven catalogue families: A1, A2, B2, C1, K3, E10, D12, D14, D1, O2, and A3 (the last by the first paper's classification).

The contribution is a uniform reduction of path existence to a fixed monadic second-order sentence over unary words. The final step, from MSO to eventual periodicity, is a known consequence of the MSO–regular-language equivalence. It is not claimed as a new principle.

- Archived on Zenodo: [doi:10.5281/zenodo.23491204](https://doi.org/10.5281/zenodo.23491204) (all versions; this release v1.3.1 is [doi:10.5281/zenodo.23491205](https://doi.org/10.5281/zenodo.23491205)).
- Paper: [`paper/paper-lines-en.pdf`](paper/paper-lines-en.pdf) (LaTeX source alongside).
- Packet: [`packet/`](packet/). Start with [`packet/AGENTS.md`](packet/AGENTS.md).
- Lean statements, written before the proofs (Mathlib only). Each ends in an intentional `sorry`: it is the statement only, and is not imported by any proof. Theorem 1a, formal version: [`statement/Challenge2.lean`](statement/Challenge2.lean), proved in [`Claude3ComparatorSolution.lean`](packet/formal/Formal/Claude3ComparatorSolution.lean). K3 on rays: [`statement/ChallengeK3.lean`](statement/ChallengeK3.lean), proved in [`Claude4K3ComparatorSolution.lean`](packet/formal/Formal/Claude4K3ComparatorSolution.lean).
- The header comments of these statement files were written before the proofs. `ChallengeK3.lean` says `Valid` and `TrianglesInCharts` would have to be proved; the actual proof goes instead through the K3 classification, boundary paths and ray arithmetic. `Challenge2.lean` says everything to check is in the file; for the paper's Theorem 1a the prose correspondence lemma in the paper must also be checked.
- Comparator records: [Theorem 1a](packet/evidence/theorem1a/comparator-thm1a-2026-10-20.md.original.log), [K3](packet/evidence/k3/comparator-k3.md.original.log).

## What has been checked, and how

| Item | Status |
|---|---|
| Theorem 1a | The **formal version is Lean-proved** ([`statement/Challenge2.lean`](statement/Challenge2.lean), declaration `ClaudeChallenge2.main`; residue-class variant `ClaudeChallenge2.main_residue` in [`Claude3Residue.lean`](packet/formal/Formal/Claude3Residue.lean), which assumes that on each residue class the decision agrees with path existence for a fixed signature). Its hypotheses are weaker than the paper's (it does not assume a sphere or exactly twelve cones), so it is a stronger theorem. The step from the paper's geometric hypotheses to the formal hypotheses is a **prose lemma** in the paper, not Lean. A paranoid Comparator run with six kernels confirmed that the proof proves exactly the formal statement. An earlier prose proof by a separate verification team is kept in the paper. No human peer review. |
| Corollary 1b | **K3: Lean-proved with no prose bridge** ([`statement/ChallengeK3.lean`](statement/ChallengeK3.lean), `ClaudeChallengeK3.main`, on every ray in r, s ≥ 1; paranoid Comparator, six kernels). A3: from the first paper's classification. The other nine families: from Theorem 1a through explicit convex decompositions, so they rely on the prose lemma. |
| Closed conditions for K3, E10, B2, C1, A1, A2 | K3: **Lean-proved** (`Claude4K3.k3_statement`: for r, s ≥ 2 a path exists iff s ≡ ±1 mod r), besides the prose proofs. E10, B2, C1, A1, A2: prose proofs (Section 5 of the paper). |
| Other Lean results | Arithmetic eventual periodicity of the family predicates on all affine rays; exact decisions on two example rays for every $t$. All Lean results use only the standard axioms. The 17 declarations checked in [`ci/Axioms.lean`](ci/Axioms.lean) are the entry points; `packet/claims.json` records 25 declarations in all. The Lean proofs were written by Claude workers; the statements were written beforehand by a different agent and compared with the paper by independent AI readers (their findings and the resulting corrections are recorded in the packet) and by computation. |
| Fixed oblique directions | Proof sketch only (Section 8); four obligations remain open. |
| Novelty | Not settled; see Section 9.3. |

Corrections: [`packet/P006-corrections.md`](packet/P006-corrections.md).

## How this work was done

The research was carried out with AI systems (OpenAI Codex and Anthropic Claude Code) working as separate teams for exploration, independent verification, literature search and formalization. The author directed the work and is responsible for this release, its provenance and the stated limits of verification. AI systems are not listed as authors.

## Re-checking the Lean results

```bash
cd packet/formal
lake exe cache get
lake build Formal.Claude2FamilyRays Formal.Claude2FamilyExamples Formal.Claude2K3Sufficient Formal.ClaudeCorRays \
  Formal.Claude3ComparatorSolution Formal.Claude3Residue Formal.Claude4K3ComparatorSolution
lake env lean ../../ci/Axioms.lean      # prints the axioms of the 17 entry-point declarations
```

The same steps run automatically on every push.

## Acknowledgements

This work extends the question of A. Bille, V. Buchstaber and E. Spodarev on linear generalized Stone–Wales paths to the fullerene families of J. E. Graver's catalogue. It relies on K. Kutnar and D. Marušič's work on cyclic edge-connectivity of fullerenes, and its last step is the theorem of J. R. Büchi, C. C. Elgot and B. A. Trakhtenbrot linking logic on words with finite automata. The proofs were checked with Lean 4, mathlib and the Comparator tool. Their work made this one possible. The author is grateful to them, and hopes this modest work adds a little to the field they opened. Full citations are in the paper.

## Licence

Text, figures and data: CC BY 4.0. Code and Lean sources: Apache-2.0. See [`packet/LICENSING.md`](packet/LICENSING.md).

## Contact

Please open an issue in this repository.
