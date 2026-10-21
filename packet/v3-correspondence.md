Current local candidate1.8.0 / article6.1; publication is separate under the author's decision.

# Japanese v3 to English v6.0 correspondence

The fixed Japanese source is supplied as an original receipt. Translation and receipt updates are not an independent proof of prose equivalence. Theorem 1a now has a specification-level Lean proof; the geometric representation bridge remains prose and owner statement meaning was confirmed on 20 October 2026; proof and bridge review remain open.

| Japanese v3 | English v4 label | Machine claims | Treatment |
|---|---|---|---|
| 1.1 | sec:definitions | def:literal, prop:forced | English presentation/condensation; original receipt scope retained |
| 1.2 | sec:definitions | def:signature | English presentation/condensation; original receipt scope retained |
| 1.3 | sec:main | cor:catalog | English presentation/condensation; original receipt scope retained; C2/K4/O1 prospects moved exclusively to extension; no new D12 classification; v6.0 receives exact Theorem 1a Lean proof; geometry bridge remains prose; owner statement meaning confirmed in v6.0; proof/bridge review still open |
| 2.1 | sec:extension | claim:oblique | Moved to extension; skeleton review updated by next-80b, four obligations remain |
| 2.2 | sec:main | thm:aligned, cor:catalog | English presentation/condensation; original receipt scope retained; v6.0 receives exact Theorem 1a Lean proof; geometry bridge remains prose; owner statement meaning confirmed in v6.0; proof/bridge review still open |
| 3.1 | sec:evidence | prop:cylinder | English presentation/condensation; original receipt scope retained |
| 3.2 | sec:evidence | prop:cylinder | English presentation/condensation; original receipt scope retained |
| 3.3 | sec:evidence | prop:cylinder | English presentation/condensation; original receipt scope retained |
| 4.1 | sec:extension | claim:oblique | Moved to extension; skeleton review updated by next-80b, four obligations remain |
| 4.2 | sec:extension | claim:oblique | Moved to extension; skeleton review updated by next-80b, four obligations remain |
| 4.3 | sec:extension | claim:oblique | Moved to extension; skeleton review updated by next-80b, four obligations remain |
| 4.4 | sec:extension | claim:oblique | Moved to extension; skeleton review updated by next-80b, four obligations remain |
| 4.5 | sec:proof | lem:rows, lem:restricted, lem:folding, lem:mso-path | English presentation/condensation; original receipt scope retained; v6.0 receives exact Theorem 1a Lean proof; geometry bridge remains prose; owner statement meaning confirmed in v6.0; proof/bridge review still open |
| 4.6 | sec:families | prop:family-decompositions | English presentation/condensation; original receipt scope retained |
| 5.1 | sec:conditions | prop:closed | English presentation/condensation; original receipt scope retained; completed arithmetic/K3 sufficiency formal results received separately |
| 5.2 | sec:conditions | prop:partial | English presentation/condensation; original receipt scope retained; C2/K4/O1 prospects moved exclusively to extension; no new D12 classification |
| 5.3 | sec:arithmetic | ex:exact-rays | English presentation/condensation; original receipt scope retained |
| 5.4 | sec:families | cor:catalog | English presentation/condensation; original receipt scope retained |
| 6.1 | sec:arithmetic | lem:divisibility | English presentation/condensation; original receipt scope retained; completed arithmetic/K3 sufficiency formal results received separately |
| 6.2 | sec:arithmetic | thm:a3-arithmetic | English presentation/condensation; original receipt scope retained; completed arithmetic/K3 sufficiency formal results received separately |
| 6.3 | sec:arithmetic | ex:exact-rays, ex:k3-formal, ex:e10-formal | English presentation/condensation; original receipt scope retained; completed arithmetic/K3 sufficiency formal results received separately |
| 7.1 | sec:formal | lem:historical-kernels | English presentation/condensation; original receipt scope retained; completed arithmetic/K3 sufficiency formal results received separately; v6.0 receives exact Theorem 1a Lean proof; geometry bridge remains prose; owner statement meaning confirmed in v6.0; proof/bridge review still open |
| 7.2 | sec:formal-records | lem:historical-kernels | English presentation/condensation; original receipt scope retained; completed arithmetic/K3 sufficiency formal results received separately; v6.0 receives exact Theorem 1a Lean proof; geometry bridge remains prose; owner statement meaning confirmed in v6.0; proof/bridge review still open |
| 8.1 | sec:finite | sec:finite | English presentation/condensation; original receipt scope retained |
| 8.2 | sec:formal | thm:k3-sufficient, claim:oblique | English presentation/condensation; original receipt scope retained; completed arithmetic/K3 sufficiency formal results received separately; v6.0 receives exact Theorem 1a Lean proof; geometry bridge remains prose; owner statement meaning confirmed in v6.0; proof/bridge review still open |
| 9 | sec:novelty | sec:novelty | English presentation/condensation; original receipt scope retained; next-80c literature boundary: geometric-to-unary-MSO reduction versus known periodicity consequences |
| A | app:domains | app:domains | English presentation/condensation; original receipt scope retained; C2/K4/O1 prospects moved exclusively to extension; no new D12 classification |
| B | app:correspondence | lem:historical-kernels | English presentation/condensation; original receipt scope retained |

## Current E10 proof scope (article6.1 / packet1.8.0)

Classification: `ClaudeChallengeE10.classification` proves the graph iff for natural p,s>=1 and r>=2, with m=2r+s and p congruent to d+1 or d-1 modulo m for d in {0,r,r+s}. `ClaudeChallengeE10.main` proves actual-path eventual periodicity for every positive natural start and nonnegative natural slope, including r=1. That branch applies formal Theorem1a `ClaudeChallenge2.State.main_statement` after proving `Valid` and `TrianglesInCharts` on the E10 model; it uses no prose geometric bridge. It does not prove a closed r=1 classification. The general prose bridge and the separate r=1 sufficient conditions/converse remain unchanged. Named catalogue correspondence retains its statement-reader caveat.

Both listed E10 declarations, and only those listed E10 targets, share the coordinator's saved six-kernel paranoid Comparator acceptance. This is a receipt readback, not a new run or independent mathematical derivation. Read `e10-manifest.json`, `VERIFICATION-RECORD.md` and `CI-AXIOM-SPLIT.md` for chronology, statement correspondence, axiom-report basis and the O2/D14 tacticPeq import collision. No owner-confirmation procedure, human review or novelty promotion is added. Current total:412 Lean files =407 proof/specification files plus five inert benchmarks. The E10 closure has166 files, including111 new proof/specification files (110 proof + one spec) and55 inherited files; its separate inert challenge has two placeholders. All300 predecessor Lean sources and old payloads retain exact bytes. No current Lean, external-kernel or scientific execution, no upload.
