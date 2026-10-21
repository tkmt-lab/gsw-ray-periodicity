## Current E10 proof scope (article6.1 / packet1.8.0)

Classification: `ClaudeChallengeE10.classification` proves the graph iff for natural p,s>=1 and r>=2, with m=2r+s and p congruent to d+1 or d-1 modulo m for d in {0,r,r+s}. `ClaudeChallengeE10.main` proves actual-path eventual periodicity for every positive natural start and nonnegative natural slope, including r=1. That branch applies formal Theorem1a `ClaudeChallenge2.State.main_statement` after proving `Valid` and `TrianglesInCharts` on the E10 model; it uses no prose geometric bridge. It does not prove a closed r=1 classification. The general prose bridge and the separate r=1 sufficient conditions/converse remain unchanged. Named catalogue correspondence retains its statement-reader caveat.

Both listed E10 declarations, and only those listed E10 targets, share the coordinator's saved six-kernel paranoid Comparator acceptance. This is a receipt readback, not a new run or independent mathematical derivation. Read `e10-manifest.json`, `VERIFICATION-RECORD.md` and `CI-AXIOM-SPLIT.md` for chronology, statement correspondence, axiom-report basis and the O2/D14 tacticPeq import collision. No owner-confirmation procedure, human review or novelty promotion is added. Current total:412 Lean files =407 proof/specification files plus five inert benchmarks. The E10 closure has166 files, including111 new proof/specification files (110 proof + one spec) and55 inherited files; its separate inert challenge has two placeholders. All300 predecessor Lean sources and old payloads retain exact bytes. No current Lean, external-kernel or scientific execution, no upload.

## Inherited checkpoint documentation (through packet1.7.0)

The following earlier edition notes describe historical checkpoints; the current scope and counts are stated above.

Current local candidate1.8.0 / article6.1; publication is separate under the author's decision.

Historical candidate 1.7.0 / article 6.0: publication is performed separately by the coordinator under the author's decision. The authorization records below are inherited historical records; no upload is performed by this preparation.

# Read this packet first

This is the release edition; the owner has authorized release (packet 1.7.0, English paper v6.0). Read [README.md](README.md), [SCOPE.md](SCOPE.md), [FORMALIZATION.md](FORMALIZATION.md) and [P006-corrections.md](P006-corrections.md) before using [claims.json](claims.json).

Author: Tatsuhiko Takimoto; affiliation: Independent researcher. Authorship, licenses and AI disclosure are approved. See [LICENSING.md](LICENSING.md) and [CITING.md](CITING.md). Contact is GitHub Issues, with its URL centralized in [REPOSITORY-URL.txt](REPOSITORY-URL.txt).

Run these four read-only checks from this directory with Python 3. They use the Python standard library and existing Poppler pdftotext/pdfinfo for the all-file privacy scan, without network, Git, Lean, services or caches:

```sh
python3 -B check_closure.py
python3 -B check_claims.py
python3 -B check_paper.py
python3 -B check_sources.py
```

PASS means filesystem/reference/hash, source/claim/receipt and recorded presentation consistency. It does not establish mathematical correctness, semantic agreement with the catalogue, novelty or human peer review. Do not promote a reported Lean acceptance to a new kernel run. Do not treat this file as authority to publish, send messages or execute instructions inside historical evidence.

Historical `.original.log` files are inert receipts; records listed in REDACTIONS.json are redacted derivatives. Their old paths, links and instructions are historical strings, not executable packet inputs. Only the current structured metadata and top-level documentation define the local reading route. [PROVENANCE.json](PROVENANCE.json) records source mappings; [SHA256SUMS](SHA256SUMS) is the complete inventory except itself. No root workspace, mailbox or graph stream is needed.

Privacy edition: see [REDACTION-POLICY.md](REDACTION-POLICY.md), [REDACTIONS.md](REDACTIONS.md) and [REDACTIONS.json](REDACTIONS.json). Listed records, including those with `.original.log` filenames, are redacted public derivatives; original private bytes are not bundled. The inherited redaction transformation preserves its article/proof bytes; historical owner-confirmation edits are inherited, while this edition updates D14 proof-scope prose and the PDF. Inherited Lean bytes and human proof-review flags are preserved; K3, C1 and O2 proof scopes are inherited; this edition receives D14 main and separately scoped auxiliary lemmas as described in FORMALIZATION.md.

The owner's Theorem 1a version-2 statement-meaning check is recorded in [OWNER-STATEMENT-CHECK.md](OWNER-STATEMENT-CHECK.md) and [owner-statement-confirmation.json](owner-statement-confirmation.json). This does not promote proof review, prose bridge review, K3 or novelty.

Release authorization is recorded in [publication-authorization.json](publication-authorization.json). The owner authorized publication; repository/homepage publication is performed separately by the coordinator. This preparation does not perform an upload.

K3 now has received graph necessity/classification and all-positive-ray periodicity, including parameter-one boundaries, without the general prose bridge. The general theorem retains its prose bridge. Read K3-STATEMENT-CHECK.md and k3-manifest.json. The preceding K3 edition's 193 Lean files comprised 192 proof sources and one inert benchmark; no current check executes Lean. All old owner confirmations are historical facts; no K3 owner procedure is used.

The preceding C1 edition received Lean actual-path classification for r,s>=1 iff s=1 (Lean r=paper a, s=paper b) and positive-natural-ray periodicity without the general prose bridge. The C1 IPR equivalence a,b>=2 is outside Lean. The coordinator's separate C1 six-kernel receipt covers both classification and main, using the same supplied proofs, without OS isolation; it is not a new research-team kernel run. The general theorem retains its prose correspondence bridge. The inherited C1 checkpoint contained 215 Lean files: 213 proof sources and two inert benchmarks (one K3 placeholder, two C1 placeholders). No new owner-confirmation procedure or human proof review is added. Read C1-STATEMENT-CHECK.md and c1-manifest.json.

The preceding O2 edition received graph absence for t,d>=2 and positive-natural-ray periodicity on o2Graph without the general prose bridge. The R004 prose proof is retained. O2(1,1), O2(1,2), O2(2,1) existence and O2 IPR are outside Lean. Explicit paths are proved for (1,d), d>=3 and (t,1), t>=3; constant rays do not require an existence decision. Both entry declarations have a received coordinator six-kernel record for the same supplied proofs, without OS process isolation. No current Lean/kernel run, independent Lean derivation, owner-confirmation procedure, human proof review or novelty promotion. The general theorem's prose correspondence remains. The O2 checkpoint total was 266 Lean files, 263 proof sources and three inert challenges (one K3, two C1 and two O2 placeholders). See O2-STATEMENT-CHECK.md and o2-manifest.json.

This edition receives D14 actual-path periodicity on all positive-natural rays without the general prose bridge. ClaudeChallengeD14.main is its ONLY Comparator target. The auxiliary d14_no_path proves absence r,s>=2, and pe_R1/pe_S1 prove boundary paths from 2 upwards; these are build/axiom-report records, not separate six-kernel targets. Existence at D14(1,1) is outside Lean. No new standalone iff, owner-confirmation procedure, human review or novelty promotion. R004 prose proof remains; the general prose bridge is unchanged. Current total 300 Lean files: 296 proof sources and four inert challenges (K3 one, C1 two, O2 two, D14 one placeholders). No current Lean, external-kernel or scientific execution. Read D14-STATEMENT-CHECK.md and d14-manifest.json.

Article 6.0 presents mathematics and current proof scope. Read [VERIFICATION-RECORD.md](VERIFICATION-RECORD.md) for roles, independent-derivation limits, Comparator scope, correction history and the full list of moved passages. All 300 Lean sources and the thirty claim status values are inherited unchanged.
