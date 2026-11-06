# Eventual periodicity of linear generalized Stone–Wales paths in affine fullerene families with convex lattice-face decompositions

**Packet v1.10.1 — released 2026-11-09; article v6.3 unchanged.**
DOI [10.5281/zenodo.23491204](https://doi.org/10.5281/zenodo.23491204) identifies all versions; specify packet 1.10.1 when citing this release.

**Tatsuhiko Takimoto** (independent researcher)

This repository contains a paper and its verification packet. It is the second of two papers. The first, on the family $\mathrm{GC}(k,l)[C_{20}]$, is at [tkmt-lab/a3-gsw-classification](https://github.com/tkmt-lab/a3-gsw-classification).

> **Theorem 1a (convex lattice-face rays).** Consider a fullerene dual that, for all sufficiently large integers $t$, decomposes into a fixed finite number of embedded convex lattice polygons with sides in the six triangular-lattice directions. The corner coordinates and gluing translations are integer affine in $t$, the rotations and side pairings are fixed, and all degree-five vertices are marked corners. Then the set of $t$ for which a literal linear generalized Stone–Wales path exists is eventually periodic.
>
> **Corollary 1b.** Path existence is eventually periodic on every integer affine ray in the valid domain of each of eleven catalogue families: A1, A2, B2, C1, K3, E10, D12, D14, D1, O2, and A3 (the last by the first paper's classification).

The contribution is a uniform reduction of path existence to a fixed monadic second-order sentence over unary words. The final step, from MSO to eventual periodicity, is a known consequence of the MSO–regular-language equivalence. It is not claimed as a new principle.

- Archived on Zenodo: [doi:10.5281/zenodo.23491204](https://doi.org/10.5281/zenodo.23491204) (all versions; releases are listed there).
- Paper: [`paper/paper-lines-en.pdf`](paper/paper-lines-en.pdf) (LaTeX source alongside).
- Packet: [`packet/`](packet/). Start with [`packet/AGENTS.md`](packet/AGENTS.md).
- Verification record (who checked what, Comparator scope, independence limits, correction history): [`packet/VERIFICATION-RECORD.md`](packet/VERIFICATION-RECORD.md). The paper itself states the mathematics and the current proof scope.
- Lean statements, written before the proofs (Mathlib only). Each ends in an intentional `sorry`: it is the statement only, and is not imported by any proof. Theorem 1a, formal version: [`statement/Challenge2.lean`](statement/Challenge2.lean), proved in [`Claude3ComparatorSolution.lean`](packet/formal/Formal/Claude3ComparatorSolution.lean). K3 on rays: [`statement/ChallengeK3.lean`](statement/ChallengeK3.lean), proved in [`Claude4K3ComparatorSolution.lean`](packet/formal/Formal/Claude4K3ComparatorSolution.lean). C1 (classification and rays): [`statement/ChallengeC1.lean`](statement/ChallengeC1.lean), proved in [`Claude4C1ComparatorSolution.lean`](packet/formal/Formal/Claude4C1ComparatorSolution.lean). O2 (absence for t, d ≥ 2, and rays): [`statement/ChallengeO2.lean`](statement/ChallengeO2.lean), proved in [`Claude5O2ComparatorSolution.lean`](packet/formal/Formal/Claude5O2ComparatorSolution.lean). D14 on rays: [`statement/ChallengeD14.lean`](statement/ChallengeD14.lean), proved in [`Claude5D14ComparatorSolution.lean`](packet/formal/Formal/Claude5D14ComparatorSolution.lean). E10 (classification for r ≥ 2, and rays): [`statement/ChallengeE10.lean`](statement/ChallengeE10.lean), proved in [`Claude5E10ComparatorSolution.lean`](packet/formal/Formal/Claude5E10ComparatorSolution.lean). D12 (classification and rays): [`statement/ChallengeD12.lean`](statement/ChallengeD12.lean), proved in [`Claude7D12ComparatorSolution.lean`](packet/formal/Formal/Claude7D12ComparatorSolution.lean).
- The header comments of these statement files were written before the proofs. `ChallengeK3.lean` says `Valid` and `TrianglesInCharts` would have to be proved; the actual proof goes instead through the K3 classification, boundary paths and ray arithmetic. `Challenge2.lean` says everything to check is in the file; for the paper's Theorem 1a the prose correspondence lemma in the paper must also be checked.
- Comparator records: [Theorem 1a](packet/evidence/theorem1a/comparator-thm1a-2026-10-20.md.original.log), [K3](packet/evidence/k3/comparator-k3.md.original.log), [C1](packet/evidence/c1/comparator-c1.md.original.log), [O2](packet/evidence/o2/comparator-o2.md.original.log), [D14](packet/evidence/d14/comparator-d14.md.original.log), [E10](packet/evidence/e10/comparator-e10.md.original.log), [D12](packet/evidence/d12/comparator-paranoid.txt.original.log) (raw output).

## What has been checked, and how

| Item | Status |
|---|---|
| Theorem 1a | The **formal version is Lean-proved** ([`statement/Challenge2.lean`](statement/Challenge2.lean), declaration `ClaudeChallenge2.main`; residue-class variant `ClaudeChallenge2.main_residue` in [`Claude3Residue.lean`](packet/formal/Formal/Claude3Residue.lean), which assumes that on each residue class the decision agrees with path existence for a fixed signature). Its hypotheses are weaker than the paper's (it does not assume a sphere or exactly twelve cones), so it is a stronger theorem. The step from the paper's geometric hypotheses to the formal hypotheses is a **prose lemma** in the paper, not Lean. A paranoid Comparator run with six kernels confirmed that the proof proves exactly the formal statement. An earlier prose proof by a separate verification team is kept in the paper. No human peer review. |
| Corollary 1b | **K3, C1, O2, D12, D14 and E10: Lean-proved with no prose bridge** ([`statement/ChallengeK3.lean`](statement/ChallengeK3.lean), `ClaudeChallengeK3.main`; [`statement/ChallengeC1.lean`](statement/ChallengeC1.lean), `ClaudeChallengeC1.main`; [`statement/ChallengeO2.lean`](statement/ChallengeO2.lean), `ClaudeChallengeO2.main`; [`statement/ChallengeD14.lean`](statement/ChallengeD14.lean), `ClaudeChallengeD14.main`; [`statement/ChallengeE10.lean`](statement/ChallengeE10.lean), `ClaudeChallengeE10.main`, including r = 1 through the formal Theorem 1a; [`statement/ChallengeD12.lean`](statement/ChallengeD12.lean), `ClaudeChallengeD12.main`; every ray in the positive domain; paranoid Comparator, six kernels). A3: from the first paper's classification. A1, A2 and B2: from the displayed classifications and affine-ray arithmetic. D1: from the prose convex decomposition and Theorem 1a, including its prose correspondence lemma. See the paper sections “Applying the theorem to the specified families”, “Closed conditions and the scope of partial results”, and “Arithmetic on affine rays and exact examples” ([source](paper/paper-lines-en.tex)). |
| Closed conditions for K3, E10, B2, C1, A1, A2, D12 | K3: **Lean-proved** (`Claude4K3.k3_statement`: for r, s ≥ 2 a path exists iff s ≡ ±1 mod r). C1: **Lean-proved** (`ClaudeChallengeC1.classification`: for a, b ≥ 1 a path exists iff b = 1; the IPR clause of the C1 row is not formalized). Both besides the prose proofs. E10: **Lean-proved** for r ≥ 2 (`ClaudeChallengeE10.classification`: a path exists iff p ≡ d ± 1 mod 2r+s for some d ∈ {0, r, r+s}); the r = 1 closed form is outside Lean. D12: **Lean-proved** for r, s ≥ 1 with no prose step (`ClaudeChallengeD12.classification`: a path exists iff r | s−1, r | s+1 or |r−3s| = 1; paranoid Comparator, six kernels); the two earlier, separately developed prose/computer-assisted proofs are kept in Section 12 as additional evidence. The Lean proof was written with knowledge of those two proofs, so it is not a third independent derivation; the kernel check makes it correct regardless. As for the other families, the Lean statement concerns the explicit quotient model; its identification with Graver's catalogue family is checked by computation and by an independent AI reader, not in Lean (the reader also notes that the source wording of Definition 1(a) was not compared verbatim). B2: prose/computer-assisted proof; the referenced B2 certificates and checking scripts are not bundled, so this packet alone does not support their full replay. A1, A2: prose proofs. See “Closed conditions and the scope of partial results” in the [paper](paper/paper-lines-en.pdf). O2: absence of paths for t, d ≥ 2 is **Lean-proved** (`ClaudeChallengeO2.classification`), besides the prose proof; existence at (1,1), (1,2), (2,1) is outside Lean. D14: absence of paths for r, s ≥ 2 is Lean-proved as a supporting lemma (`Claude5D14.d14_no_path`, checked for axioms but not a Comparator target); the paper states no closed condition for D14. |
| Other Lean results | Arithmetic eventual periodicity of the family predicates on all affine rays; exact decisions on two example rays for every $t$. All Lean results use only the standard axioms. The 27 declarations checked in [`ci/Axioms.lean`](ci/Axioms.lean) and [`ci/AxiomsD14.lean`](ci/AxiomsD14.lean) are the entry points; `packet/claims.json` records 36 declarations in all. The Lean proofs were written by Claude workers; the statements were written beforehand by a different agent and compared with the paper by independent AI readers (their findings and the resulting corrections are recorded in the packet) and by computation. |
| Fixed oblique directions | Proof sketch only (“An extension to fixed oblique directions (proof sketch)”); four obligations remain open. |
| Novelty | Not settled; see “Novelty and remaining obligations”. |

Corrections: [`packet/P006-corrections.md`](packet/P006-corrections.md).

## How this work was done

The research was carried out with AI systems (OpenAI Codex and Anthropic Claude Code) working as separate teams for exploration, independent verification, literature search and formalization. The author directed the work and is responsible for this release, its provenance and the stated limits of verification. AI systems are not listed as authors.

## Re-checking the packet records

From a fresh checkout, with Python 3 and Poppler (`pdftotext` and `pdfinfo`) on PATH:

```bash
(cd packet && python3 -B check_closure.py)
```

Expected output is a JSON object with `"status": "PASS"`. Run all four checks before Lean creates `.lake`:

```bash
cd packet
python3 -B check_closure.py
python3 -B check_claims.py
python3 -B check_paper.py
python3 -B check_sources.py
cd ..
```

These check stored records and file consistency; they do not rerun Lean or the missing B2 certificates.

## Re-checking the Lean results

Install [elan](https://github.com/leanprover/elan#installation) first, and put `$HOME/.elan/bin` on PATH. CI uses:

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"
```

`packet/formal/lean-toolchain` selects Lean 4.35.0; `lake-manifest.json` pins mathlib and its dependencies. Downloads require network access. No toolchain or cached mathlib objects are bundled.

The full build below matches [.github/workflows/lean.yml](.github/workflows/lean.yml), including its memory-setting change. The committed lakefile uses `-j1 -M4096` (one Lean thread, 4096 MiB per file); CI raises the latter to 12288 MiB because the existing CI configuration reports that K3 classification needs more than 4096 MiB. Allow at least the CI runner's 16 GiB RAM for this route. **These are per-file limits, not a total memory or process cap:** Lake may schedule multiple Lean processes. A machine with a strict aggregate budget must additionally enforce its own process/memory limit; the full route is not a verified 12 GiB procedure. The 495-file closure, especially `Formal.Claude2K3Classify` and the graph-classification targets, is substantially heavier than a small syntax check.

For a small check, after downloading the pinned toolchain, from `packet/formal` run:

```bash
lake env lean -j1 -M4096 --stdin <<'LEAN'
import Init
example (n : Nat) : n = n := rfl
LEAN
```

Exit 0 with no output checks only this Lean example. It does not check the family proofs. To check a small project target after `lake exe cache get`, use `lake build Formal.Claude3MsoSyntax`; its imported dependencies may still take time.

For the full route, start at the repository root in a Bash shell. Run the packet checks above first. The following temporarily changes the working copy of `lakefile.toml`, just as CI does:

```bash
set -euo pipefail
cd packet/formal
lake exe cache get
python3 -c 'from pathlib import Path; p=Path("lakefile.toml"); s=p.read_text(); assert "-M4096" in s or "-M12288" in s; p.write_text(s.replace("-M4096", "-M12288"))'
lake build Formal.Claude2FamilyRays Formal.Claude2FamilyExamples Formal.Claude2K3Sufficient Formal.ClaudeCorRays \
  Formal.Claude3ComparatorSolution Formal.Claude3Residue Formal.Claude4K3ComparatorSolution \
  Formal.Claude4C1ComparatorSolution Formal.Claude5O2ComparatorSolution Formal.Claude5D14ComparatorSolution \
  Formal.Claude5E10ComparatorSolution Formal.Claude7D12ComparatorSolution
lake env lean ../../ci/Axioms.lean      # prints the axioms of 25 entry-point declarations
lake env lean ../../ci/AxiomsD14.lean   # and of the 2 D14 declarations (separate file: the O2 and D14 proofs
                                        # both define a helper tactic named peq, so one file cannot import both)
```

CI runs the four packet checks, toolchain installation, cache download, memory change, full target list and axiom gate on pushes, pull requests and manual dispatches. Its gate requires exactly 27 lines, each reporting `[propext, Classical.choice, Quot.sound]`. To reproduce that gate after the build:

```bash
set -euo pipefail
lake env lean ../../ci/Axioms.lean | tee axioms.txt
lake env lean ../../ci/AxiomsD14.lean | tee -a axioms.txt
test "$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' axioms.txt)" -eq 27
test "$(wc -l < axioms.txt)" -eq 27
```

The gate is a Lean axiom report, not a rerun of the separately saved Comparator checks. Use another fresh checkout for the packet's strict inventory check after a build; `.lake`, build outputs and the temporary memory setting are not distributed packet files.

## Acknowledgements

This work extends the question of A. Bille, V. Buchstaber and E. Spodarev on linear generalized Stone–Wales paths to the fullerene families of J. E. Graver's catalogue. It relies on K. Kutnar and D. Marušič's work on cyclic edge-connectivity of fullerenes, and its last step is the theorem of J. R. Büchi, C. C. Elgot and B. A. Trakhtenbrot linking logic on words with finite automata. The proofs were checked with Lean 4, mathlib and the Comparator tool. Their work made this one possible. The author is grateful to them, and hopes this work adds something new to the field they opened. Full citations are in the paper.

## Licence

Text, figures and data: CC BY 4.0. Code and Lean sources: Apache-2.0. See [`packet/LICENSING.md`](packet/LICENSING.md).

## Contact

Please open an issue in this repository, or write to research@tatsuhikotakimoto.com.
