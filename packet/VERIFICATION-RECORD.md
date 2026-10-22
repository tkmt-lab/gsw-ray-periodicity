# Article6.3 / packet1.10.0 verification record

## D12 Lean reception and current verification boundary

Source pin: e2c2b460d1708f78739aa8d18064814f98aab317 (proof); research merge 38b386fc606b1a1417f7593bac7f48b6062cc16c (proof and coordinator Comparator log). Prior challenge/specification pin: 6785c4a809bab0507b96d23a7e38bf7ca4bba7a2; the challenge and Claude7D12Spec.lean are byte-identical at both pins. Packaging statically compared 22 copied definitions plus PathExists and both exact theorem signatures (challenge vs solution). All 86 closure fingerprints agree; 82 files are new (81 proof and one specification), 4 inherited. The separate challenge has two intentional sorry placeholders, is outside dependencies and was not used as proof. Current totals 495 Lean files: 489 proof/specification sources and six inert challenges. All 412 predecessor Lean source bytes are preserved.

`thm:d12-classification`: `lean-result-received` (ClaudeChallengeD12.classification). `cor:catalog` adds ClaudeChallengeD12.main. Both are the targets of the coordinator's paranoid Comparator run with six kernels (Lean paranoid, lean4lean, nanoda, con-leche, con-ron, Lean default), all accepting the same supplied proof: 1637.79 seconds, 2,954,018,816 maximum-RSS bytes (inherited measurements, not current execution; sandbox disabled, no OS process isolation). This is not six independent derivations. The claims.json receipts of both D12 declarations point to this raw coordinator Comparator output. Standard-three-axiom results (propext, Classical.choice, Quot.sound) for both targets and for the intermediate d12_no_path and path_gm are worker-reported. Chronology: the worker's own Comparator attempt stopped at its 3 GB guard during export (kept as comparator-worker-stopped.txt.original.log); the coordinator then ran it to completion. The worker rebuilt all D12 modules one at a time (d12-rebuild.log.original.log). The release preparation of the public repository ran its CI-equivalent build check and axiom query once on the same sources (27 standard-axiom lines); that output is outside the packet and is not a receipt here.

Independence: the Lean proof was written after its author read the route-A report and the article 6.2 D12 section; it searched strip decompositions with its own Python model and did not use the route-A executor or route-B certificates. It is therefore not an independent third derivation. Its correctness rests on the kernel check, not on the routes; the routes remain additional evidence. The article says this in one sentence.

Statement correspondence: one independent AI statement reader returned FAITHFUL WITH CAVEATS. Caveats: the all-parameter identification with Graver's catalogue family is not formalized (the chart data agree with the article's explicit quotient convention); Definition 1(a) of the cited source was not supplied verbatim, so exact agreement of LiteralPath with the source wording is not independently certified. The writer's saved mirror covers 240 cases r<=20, s<=12 (144 with isomorphism to the earlier constructor): 78 positive, 162 negative, zero disagreements with the classification. These are finite readbacks, not a universal catalogue-isomorphism theorem. No owner-confirmation procedure, human proof peer review or novelty establishment is claimed.

CI/query layout: D12 helper tactics (d12om, d12peq, d12peq2, d12glue_tac) do not collide with the O2/D14 peq; D12 is queried in the O2-side Axioms.lean. See CI-AXIOM-SPLIT.md.

Article 6.3 edits: 17 passages of article 6.2 changed (lines-v6.3-edit-map.json), including one new subsection (12.1, a formal proof) inside the D12 section and two cross-references. The article 6.3 text was revised once before release after an independent AI referee report (verdict MINOR): catalogue identification outside the Lean statement made explicit in Section 12, the kernel check named in Section 12.1, the limitations sentence qualified, and the cross-references added. Before release, one related-work sentence and bibliography entry were also added to the Introduction, crediting I. Dorofeev's public verification package (Zenodo doi:10.5281/zenodo.22143505, v1.0.1, 2026-08-28) of certificates for reported counterexamples to the BBS cut-partition and character conjectures; source: the literature team's related-work survey. No AI-use or priority claim is made about it. Numbered statements, displayed formulae, domains and claim identifiers are unchanged. The 6.2 passages are archived at the end of this record.


## Historical D12 addition, article 6.2 / packet 1.9.0 (no-Lean statement superseded by 1.10.0)

Positive integer r,s: a literal path exists iff r divides s-1 or s+1, or abs(r-3s)=1. See d12/README.md and the two full proof routes in d12/proof-notes.tex. This classification has two separately derived universal prose/computer-assisted proof routes and NO Lean proof. D12 ray periodicity separately follows from Theorem1a with its prose model correspondence, or conditionally from the arithmetic classification. Earlier 30 claim statuses, 34 Lean declaration references and all412 Lean sources remain unchanged. This is a local candidate; publication of this revision requires a separate author/coordinator decision. The inherited authorization record concerns the earlier release checkpoint and is not a new approval of D12. No Lean, kernel, graph census or upload was run to prepare this revision.

`thm:d12-classification`: `two-separately-derived-universal-proof-routes-received`; no Lean and no human proof review. See d12/VERIFICATION-RECORD.md for the full unchanged draft-v2 limitations, including failed strict blind outcome isolation. The authoring agent checked stored rational certificate arithmetic and packaging, not a third independent proof.

# Verification record: affine fullerene ray periodicity

## E10 reception and current verification boundary

Source pin: e0b0f1eb3ac84e1f793f98aaf7bacd76a9bd27fe. Prior challenge/specification pin: 5b29fee0e77b7c639cebc77885937d1ed8b1af0f. The research session statically compared23 copied definitions plus PathExists and both exact theorem signatures. All166 closure fingerprints agree;111 files are new (110 proof and one specification),55 inherited. The separate challenge has two intentional sorry placeholders, is outside dependencies and was not used as proof. Current totals412 Lean files:407 proof/specification sources and five inert challenges. All300 predecessor Lean source bytes are preserved.

The received E10 Comparator targets are ClaudeChallengeE10.classification and ClaudeChallengeE10.main, BOTH in the saved six-kernel paranoid run. Lean paranoid, lean4lean, nanoda, con-leche, con-ron and Lean default accepted the same supplied proofs. This is not six independent derivations. The coordinator records595.42 seconds and3,205,365,760 maximum-RSS bytes; those are inherited measurements, not current execution. Standard-three-axiom queries (propext, Classical.choice, Quot.sound) are coordinator/worker-reported, not new raw kernel output. The worker's earlier Comparator-not-run and no-clean-rebuild notes remain intact, preceding the later coordinator run. No current Lean or external kernel was run; macOS OS process isolation was absent.

The iff domain is natural p,s>=1,r>=2. The literal-path ray domain is positive natural starts and nonnegative natural slopes in all three coordinates, including constant rays and r=1. On r=1, formal ClaudeChallenge2.State.main_statement applies to the E10 affine signature after Valid and TrianglesInCharts are proved in Lean. This is a formal use of the general theorem, NOT use of its prose geometric bridge. No formal r=1 closed classification is received; the earlier sufficient conditions and open converse are unchanged. The general paper-to-specification bridge remains prose, and no formal named-catalogue correspondence certificate is asserted.

The independent AI statement reader returned FAITHFUL WITH CAVEATS, covering143 triples (103 in the classification domain). The writer mirror saved702 known triples (620 with r>=2,82 with r=1); counts, chart/seam safety, path results and graph isomorphism agree with aligned and original non-aligned R004 constructors. There are zero classification mismatches on r>=2. The old six-congruence formula disagrees at positive r=1 points (3,1,4),(3,1,5),(4,1,5), outside that iff's domain. These are finite readbacks, not graph regeneration or a universal catalogue-isomorphism theorem. Reader and writer ranges overlap;143 and702 must not be summed as disjoint independent evidence. No new owner-confirmation procedure, human proof peer review or novelty establishment is claimed.

CI/query layout: O2 and D14 collide on peq / tacticPeq; keep O2-side Axioms.lean and D14-side AxiomsD14.lean separate. E10 can be added to either side. No combined import or new Lean query was attempted; see CI-AXIOM-SPLIT.md.

All30 claim IDs and status values persist. Only cor:catalog and prop:closed acquire E10 declaration/evidence/scope records; the other28 claim payloads are unchanged apart from the shared correction-log fingerprint. The current total is34 Lean declaration references across15 claims. The two E10 additions do not change the historical scope of any earlier kernel receipt. The historical sections and100-item editorial archive below describe the preceding checkpoint except where this section explicitly updates E10.


This supplement accompanies article 6.1 and local packet candidate 1.8.0.
It records who supplied arguments, how declarations and finite evidence
were checked, historical corrections and the limits of those checks.
The article gives the mathematics and one present-scope table. The
source of exact types is the Lean source and structured claims ledger.
This supplement is a verification record, not a new proof or publication authorization.

## Present evidence by claim

The thirty claim IDs and their status values are unchanged from packet1.7.0. All human proof-review flags remain false. Current total412 Lean files:407 proof/specification sources and five inert challenges. The E10 proof dependency root is added; no Lean or external kernel is run for this reception.

| Claim | Status | Lean declaration records | Evidence and review trail |
|---|---|---:|---|
| `def:literal` | `source-definition` | 0 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/sources/S0047-fullerene-open-problems.json.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `prop:forced` | `lean-result-received` | 1 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/logs/T0519.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `def:signature` | `scope-definition` | 0 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `thm:aligned` | `lean-result-received` | 3 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/extra/AH-literature-comparison.md.original.log`, `evidence/extra/S2047-behmaram-boutillier.json.original.log`, `evidence/extra/S2073-li-chen-quasipolynomial.json.original.log`, `evidence/extra/S2180-aixiv-guide.json.original.log`, `evidence/extra/S2181-dd2004-next27.json.original.log`, `evidence/extra/S2182-dd-zigzag-next27.json.original.log`, `evidence/extra/S2183-zigzag-complexes.json.original.log`, `evidence/extra/S2184-book-next27-access.json.original.log`, `evidence/extra/S2185-ddf2004-fulltext-next28.json.original.log`, `evidence/extra/S2186-book-archive-access-next28.json.original.log`, `evidence/extra/S2187-book-official-access-next28.json.original.log`, `evidence/extra/S2188-mso-strings-next28.json.original.log`, `evidence/extra/S2189-fischer-makowsky-spectra.json.original.log`, `evidence/extra/S2190-kotek-makowsky-biiterative.json.original.log`, `evidence/extra/S2191-periodic-counter-graphs.json.original.log`, `evidence/extra/S2192-wanke-periodic-graphs.json.original.log`, `evidence/extra/S2193-courcelle-finite-contexts.json.original.log`, `evidence/extra/S2194-thomas-unary-binary.json.original.log`, `evidence/extra/S2195-octagonal-acceleration.json.original.log`, `evidence/extra/S2196-mine-octagon-domain.json.original.log`, `evidence/extra/next80c.original.log`, `evidence/extra/report-next28-2026-10-19.md.original.log`, `evidence/theorem1a/Challenge2.lean.original.log`, `evidence/theorem1a/ComparatorChallenge.lean.original.log`, `evidence/theorem1a/challenge2-reading-guide-ja.md.original.log`, `evidence/theorem1a/comparator-thm1a-2026-10-20.md.original.log`, `evidence/theorem1a/comparator-thm1a-paranoid-2026-10-20.txt.original.log`, `evidence/theorem1a/comparator-thm1a.json.original.log`, `evidence/theorem1a/fold-report-2026-10-20.md.original.log`, `evidence/theorem1a/initial-lean-execution.failed.original.log`, `evidence/theorem1a/initial-proof-source-inventory.original.log`, `evidence/theorem1a/lean-execution.json`, `evidence/theorem1a/main-axioms.original.log`, `evidence/theorem1a/mso-report-2026-10-20.md.original.log`, `evidence/theorem1a/next85.original.log`, `evidence/theorem1a/next85a.original.log`, `evidence/theorem1a/proof-source-inventory.json`, `evidence/theorem1a/response-ja.md.original.log`, `evidence/theorem1a/review.md.original.log`, `evidence/theorem1a/serial-build-output.original.log`, `evidence/theorem1a/spec-comparison.json`, `evidence/theorem1a/thm1a-final-report-2026-10-20.md.original.log`, `evidence/theorem1a/thm1a-geo-report-2026-10-20.md.original.log`, `evidence/theorem1a/thm1a-ident-report-2026-10-20.md.original.log`, `evidence/theorem1a/thm1a-state-report-2026-10-20.md.original.log`, `owner-statement-confirmation.json`, `owner-copy-comparison.json`, `owner-copy-diff.txt`, `owner-decision-extract.original.txt`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `cor:catalog` | `mixed-prose-and-formal-results` | 6 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/k3/k3-bridge-report.md.original.log`, `evidence/c1/comparator-c1.md.original.log`, `evidence/o2/comparator-o2.md.original.log`, `evidence/d14/comparator-d14.md.original.log`, `evidence/e10/comparator-e10.md.original.log`, `evidence/d12/comparator-paranoid.txt.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12, P006-L14, P006-L15, P006-L16, P006-L17, P006-L18, P006-L19 |
| `lem:rows` | `independent-prose-proof-ai-reviewed` | 0 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `lem:restricted` | `independent-prose-proof-ai-reviewed` | 0 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `lem:folding` | `independent-prose-proof-ai-reviewed` | 0 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `lem:mso-path` | `independent-prose-proof-ai-reviewed` | 0 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/extra/AH-literature-comparison.md.original.log`, `evidence/extra/S2047-behmaram-boutillier.json.original.log`, `evidence/extra/S2073-li-chen-quasipolynomial.json.original.log`, `evidence/extra/S2180-aixiv-guide.json.original.log`, `evidence/extra/S2181-dd2004-next27.json.original.log`, `evidence/extra/S2182-dd-zigzag-next27.json.original.log`, `evidence/extra/S2183-zigzag-complexes.json.original.log`, `evidence/extra/S2184-book-next27-access.json.original.log`, `evidence/extra/S2185-ddf2004-fulltext-next28.json.original.log`, `evidence/extra/S2186-book-archive-access-next28.json.original.log`, `evidence/extra/S2187-book-official-access-next28.json.original.log`, `evidence/extra/S2188-mso-strings-next28.json.original.log`, `evidence/extra/S2189-fischer-makowsky-spectra.json.original.log`, `evidence/extra/S2190-kotek-makowsky-biiterative.json.original.log`, `evidence/extra/S2191-periodic-counter-graphs.json.original.log`, `evidence/extra/S2192-wanke-periodic-graphs.json.original.log`, `evidence/extra/S2193-courcelle-finite-contexts.json.original.log`, `evidence/extra/S2194-thomas-unary-binary.json.original.log`, `evidence/extra/S2195-octagonal-acceleration.json.original.log`, `evidence/extra/S2196-mine-octagon-domain.json.original.log`, `evidence/extra/next80c.original.log`, `evidence/extra/report-next28-2026-10-19.md.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `prop:family-decompositions` | `independent-prose-proof-ai-reviewed` | 0 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `prop:closed` | `mixed-prose-and-formal-results` | 3 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/R004/R004-c1-proof.md.txt.original.log`, `evidence/R004/R004-b2-proof.md.txt.original.log`, `evidence/R004/R004-gc-proof.md.txt.original.log`, `evidence/R004/R004-k3-positive-proof.md.txt.original.log`, `evidence/R004/R004-k3-necessity-proof.md.txt.original.log`, `evidence/R004/R004-e10-positive-proof.md.txt.original.log`, `evidence/R004/R004-e10-necessity-proof.md.txt.original.log`, `evidence/k3/k3-bridge-report.md.original.log`, `evidence/c1/comparator-c1.md.original.log`, `evidence/o2/comparator-o2.md.original.log`, `evidence/e10/comparator-e10.md.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12, P006-L14, P006-L15, P006-L16, P006-L18 |
| `prop:partial` | `mixed-prose-and-formal-results` | 2 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/R004/R004-report-004.md.txt.original.log`, `evidence/R004/R004-o2-proof.md.txt.original.log`, `evidence/R004/R004-d12-positive-proof.md.txt.original.log`, `evidence/o2/comparator-o2.md.original.log`, `evidence/d14/comparator-d14.md.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12, P006-L16, P006-L17 |
| `lem:divisibility` | `prose-proof-received` | 0 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `thm:k3-arithmetic` | `lean-result-received` | 3 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/second-paper-report-2026-10-19.md.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `thm:e10-arithmetic` | `lean-result-received` | 3 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/second-paper-report-2026-10-19.md.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `thm:other-arithmetic` | `lean-result-received` | 4 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/second-paper-report-2026-10-19.md.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `thm:a3-arithmetic` | `lean-result-received` | 2 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/second-paper-report-2026-10-19.md.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `ex:exact-rays` | `mixed-prose-and-formal-results` | 0 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/R004-v2/R004-affine-rays-report.txt.original.log`, `evidence/R004-v2/coordinator-D12-s58.txt.original.log`, `evidence/R004-v2/R004-d12-rays-proof.txt.original.log`, `evidence/R004-v2/R004-affine-rays-proof.txt.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `ex:k3-formal` | `lean-result-received` | 1 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/second-paper-report-2026-10-19.md.original.log`, `evidence/k3/k3-bridge-report.md.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12, P006-L14 |
| `ex:e10-formal` | `lean-result-received` | 1 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/second-paper-report-2026-10-19.md.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `thm:k3-sufficient` | `lean-result-received` | 3 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/k3-sufficiency-report-2026-10-19.md.original.log`, `evidence/k3/k3-bridge-report.md.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12, P006-L14 |
| `lem:k3-corners` | `lean-result-received` | 1 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/k3-sufficiency-report-2026-10-19.md.original.log`, `evidence/k3/k3-bridge-report.md.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12, P006-L14 |
| `lem:k3-hex-interior` | `lean-result-received` | 1 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/k3-sufficiency-report-2026-10-19.md.original.log`, `evidence/k3/k3-bridge-report.md.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12, P006-L14 |
| `lem:k3-tri-interior` | `lean-result-received` | 1 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/k3-sufficiency-report-2026-10-19.md.original.log`, `evidence/k3/k3-bridge-report.md.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12, P006-L14 |
| `lem:historical-kernels` | `partial-formal-correspondence` | 0 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `claim:oblique` | `proof-sketch-ai-skeleton-reviewed` | 0 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/research/fixed-direction-ray-theorem-AN.md.original.log`, `evidence/research/affine-rauzy-AH.md.original.log`, `evidence/research/finite-word-lemma-AM.md.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `prop:cylinder` | `ai-reviewed-prose-argument` | 0 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/research/cylinder-theorem-AD.md.original.log`, `evidence/extra/AH-literature-comparison.md.original.log`, `evidence/extra/S2047-behmaram-boutillier.json.original.log`, `evidence/extra/S2073-li-chen-quasipolynomial.json.original.log`, `evidence/extra/S2180-aixiv-guide.json.original.log`, `evidence/extra/S2181-dd2004-next27.json.original.log`, `evidence/extra/S2182-dd-zigzag-next27.json.original.log`, `evidence/extra/S2183-zigzag-complexes.json.original.log`, `evidence/extra/S2184-book-next27-access.json.original.log`, `evidence/extra/S2185-ddf2004-fulltext-next28.json.original.log`, `evidence/extra/S2186-book-archive-access-next28.json.original.log`, `evidence/extra/S2187-book-official-access-next28.json.original.log`, `evidence/extra/S2188-mso-strings-next28.json.original.log`, `evidence/extra/S2189-fischer-makowsky-spectra.json.original.log`, `evidence/extra/S2190-kotek-makowsky-biiterative.json.original.log`, `evidence/extra/S2191-periodic-counter-graphs.json.original.log`, `evidence/extra/S2192-wanke-periodic-graphs.json.original.log`, `evidence/extra/S2193-courcelle-finite-contexts.json.original.log`, `evidence/extra/S2194-thomas-unary-binary.json.original.log`, `evidence/extra/S2195-octagonal-acceleration.json.original.log`, `evidence/extra/S2196-mine-octagon-domain.json.original.log`, `evidence/extra/next80c.original.log`, `evidence/extra/report-next28-2026-10-19.md.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `sec:finite` | `finite-evidence-only` | 0 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `sec:novelty` | `unresolved` | 0 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`, `evidence/extra/AH-literature-comparison.md.original.log`, `evidence/extra/S2073-li-chen-quasipolynomial.json.original.log`, `evidence/research/review-AW-R005-report12-snapshot.txt.original.log`, `evidence/extra/S2047-behmaram-boutillier.json.original.log`, `evidence/extra/S2180-aixiv-guide.json.original.log`, `evidence/extra/S2181-dd2004-next27.json.original.log`, `evidence/extra/S2182-dd-zigzag-next27.json.original.log`, `evidence/extra/S2183-zigzag-complexes.json.original.log`, `evidence/extra/S2184-book-next27-access.json.original.log`, `evidence/extra/S2185-ddf2004-fulltext-next28.json.original.log`, `evidence/extra/S2186-book-archive-access-next28.json.original.log`, `evidence/extra/S2187-book-official-access-next28.json.original.log`, `evidence/extra/S2188-mso-strings-next28.json.original.log`, `evidence/extra/S2189-fischer-makowsky-spectra.json.original.log`, `evidence/extra/S2190-kotek-makowsky-biiterative.json.original.log`, `evidence/extra/S2191-periodic-counter-graphs.json.original.log`, `evidence/extra/S2192-wanke-periodic-graphs.json.original.log`, `evidence/extra/S2193-courcelle-finite-contexts.json.original.log`, `evidence/extra/S2194-thomas-unary-binary.json.original.log`, `evidence/extra/S2195-octagonal-acceleration.json.original.log`, `evidence/extra/S2196-mine-octagon-domain.json.original.log`, `evidence/extra/next80c.original.log`, `evidence/extra/report-next28-2026-10-19.md.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |
| `app:domains` | `finite-evidence-only` | 0 | `evidence/R004/R004-aligned-periodicity-proof.md.txt.original.log`, `evidence/R004/R004-claim14-aligned-families.md.txt.original.log`, `evidence/R004/coordinator-claim14-review.txt.original.log`, `evidence/AN-5-6-review.original.log`; review rows P006-L01, P006-L02, P006-L03, P006-L04, P006-L05, P006-L06, P006-L07, P006-L08, P006-L09, P006-L10, P006-L11, P006-L12 |

## Roles and independence

The research team (R002, with Codex and Claude Code) developed the
geometric programme, constructions, arithmetic and finite checks. A
separate verification session (R004) derived the common six-direction
convex-face proof from the statement and its own prior work without
reading the research team's proof, construction or code. The two
derivations concern the same six-direction domain. They do not constitute
two Lean developments or human proof peer review.

The statement was supplied in advance. The independence record also
discloses prior O2 mapping-metadata exposure and D12 single-point outcomes;
strict blind outcome isolation is not claimed. Reading and translating
the verifier's argument afterwards is editorial work, not a third
independent derivation. Same-agent alternative arithmetic implementations
are distinguished from another reviewer.

Claude workers supplied the general specification theorem and the K3,
C1, O2 and D14 Lean proofs against prior specifications. The research
session received and statically checked sources and records. Independent
AI statement readers and finite model comparisons support the
catalogue/parameter interpretation. The named catalogue correspondence
has its stated specification and geometric caveats.

## Formal declarations and Comparator scope

The general theorem's entry declarations are `ClaudeChallenge2.main`,
`ClaudeChallenge2.State.main_statement` and `ClaudeChallenge2.main_residue`.
The signature is `ClaudeChallenge2.Sig`; the article uses the neutral
notation `Sig`, `Valid`, `TrianglesInCharts`, `PathExists`, `graph` and
`LiteralPath` for these exact mathematical objects. The paper-to-specification
supporting-line/cone-angle argument is prose. The formal specification's
local assumptions are weaker than requiring a sphere, twelve cones and
nondegenerate polygon disks. The fixed-residue theorem also assumes
agreement between each branch and the original decision.

The historical research build/axiom queries for these three declarations
found `propext`, `Classical.choice` and `Quot.sound`. The coordinator's
six-kernel paranoid Comparator target was the same supplied `main`
proof; that record is not a six-kernel test of `main_residue`.

K3's completed graph iff and common-neighbour declarations are
`Claude4K3.k3_statement` and `Claude4K3.noThree`; its Comparator target
is `ClaudeChallengeK3.main` only. Separate build/axiom reports support
the other declarations. C1's Comparator covers both
`ClaudeChallengeC1.classification` and `ClaudeChallengeC1.main`.
O2's Comparator similarly covers `ClaudeChallengeO2.classification`
and `ClaudeChallengeO2.main`. D14's only Comparator target is
`ClaudeChallengeD14.main`: `Claude5D14.d14_no_path`, `pe_R1` and
`pe_S1` have separately scoped build/axiom reports. They are not
additional Comparator targets or a new standalone D14 iff.

Each six-kernel record checks a single supplied proof for each listed
target, not six independent mathematical derivations. The saved runs
lacked OS process isolation on macOS. Worker not-run notes predate
the coordinator's subsequent runs and remain historical originals.
All sources, exact statement types, axioms, toolchain, dependency pins
and raw/public-derivative receipt fingerprints remain in the packet.

## Boundary and conditional-result limits

K3's modular iff has domain r,s>=2, while its ray theorem includes
positive parameter-one boundaries. C1's path iff has a,b>=1 and b=1;
the C1 IPR condition is prose. O2 absence has t,d>=2; Lean boundary
paths have (1,d), d>=3 and (t,1), t>=3. Existence at (1,1), (1,2),
(2,1) has finite evidence outside Lean. D14 absence has r,s>=2 and
Lean boundary paths begin at the other parameter 2. D14(1,1) existence
is outside the Lean statements. Constant-ray periodicity needs no
existence decision. Eventually positive integer rays are shifted to
the positive natural domain in explanatory arithmetic, rather than
being separately received all-integer declarations.

The conditional auxiliary research lemmas include finite first-repeat
decision with its two-common-neighbour hypothesis, scaled-lattice
transport, cylinder displacement with divisibility assumptions and
finite branching with decreasing lexicographic rank. The concrete IET
component models equal-final-label removal only. The older count of
57 research declarations, or 98 including 41 A3 arithmetic entries,
is not a formalization percentage or the current library size.

The general E10 r=1 necessity argument remains open. The eighteen-region
E10 geometric table has the earlier independent-review limits. The D1
belt absence argument remains a draft. The D12 two-ray proof and
selected partial branches are distinct from the separate full D12
classification manuscript. The oblique-direction extension remains a
proof sketch with its four transfer obligations.

## Finite checks, corrections and source-reading scope

T0770 records 1,809 arithmetic values on nine known A3 rays; T0771
records fourteen independent-constructor graph decisions on known
inputs, not unseen predictions. T0887 checks tail coefficients beyond
64. T0888 covers the E10 descriptor's eight charts, 36 inverse gluings,
108 intervals, 156 connections, 120 descriptors and twelve labels.
T0889 covers 71 charts, 342 edges and 21 single-zero boundaries.
The AM audit has 6,564 inputs and 67,312 states; the AN phase audit
has 48 directions, 14,904 entrances, 4,005 intervals (1,013 empty),
5,496 lifts and 40,380 conjugacy cells.

R004 report 14 has 378 coefficient representations and 13,430 pairs,
with observed maximum period 44 and threshold 69. Report 15 has
7,056 strips, 2,255 nonempty outputs, 16,212 subintervals, 99,225
ordered row pairs and 509,160 folded-point comparisons. The output-row
upper bound x+y<=U_s+epsilon was corrected by hand, followed by a
new finite check; the check did not discover the error originally.
Earlier type/key failures remain in the historical records. Numerical
agreement alone does not replace the universal geometric argument.

C1's 36 model pairs contain the reader's 25 samples; O2's 80 contain
the reader's 36; D14's 81 contain the reader's 25. These are overlapping
known finite ranges. Generated Lean degree/strip formulas may be
fitted from data, but their universal correctness is established by
the Lean proof, not by extrapolation from samples. No graph constructor,
scientific audit or Lean/kernel is rerun for article 6.0.

The D12 two-ray certificate has 2,058 nonnegativity and 756
no-integer-solution conditions. Same-verifier arithmetic rereading is
not another reviewer; the coordinator's s=58 construction checks one
graph and a 3,260-vertex witness, not all 2,814 conditions.

The prior literature lane (R005) read the theorem statements and
specified sections listed in source records, not every full proof.
For the counter-language and finite-periodic-graph papers (source
IDs S2191/S2192), only official abstracts and bibliographic data were
obtained. Their full hypotheses are not inferred from unread theorems.
The cyclic-edge-connectivity fact is cited as known in Kutnar--Marusic;
its original proof was not newly audited. The MFCS elimination and
Li--Chen records retain their exact reading scopes. The MSO source's
HTML Theorem 3.2 is numbered Theorem 14 in its v1 PDF. No priority proof
or newly verified executable geometric-to-MSO compiler is supplied.

## Historical specification and edition changes

The coordinator fixed the general specification before proof and
amended it to version 2 to include `TrianglesInCharts`. On 20 October 2026,
the owner confirmed its statement meaning using the Japanese guide;
this was not proof review or review of the prose correspondence.
The owner-confirmation procedure ended that day. Those records are
preserved as historical facts; no new owner procedure is introduced.
K3's earlier statement omitted parameter-one rays; an AI reader found
the omission and version 2 corrected it before proof. C1/O2/D14 use
prior specifications, AI reading and finite correspondence checks.

Article 4.3/packet 1.1.0 added the specification-level theorem; later
editions incorporated K3, C1, O2 and D14 at their exact recorded scopes.
Article 5.0/packet 1.6.0 added D14 main-only Comparator evidence and
separately scoped auxiliary lemmas. Article 6.1/packet 1.8.0 separates
this process record from the article; mathematical claim IDs and
status values are unchanged. The complete prior chronology is retained
in CHANGELOG and P006-corrections, and declaration/source navigation
is in FORMALIZATION. Historical owner and publication authorization
records are not new permissions inferred from this supplement.

For optional local Lean reproduction, use the pinned `lean-toolchain`
and `lake-manifest.json`; `lake exe cache get` retrieves mathlib build
artifacts. Caches, compiled binaries and raw graph streams are
intentionally omitted. There is no separately delivered artifact
collection. The four advertised packet checks are static consistency
checks and do not execute Lean. Contact is GitHub Issues using the
canonical REPOSITORY-URL.txt.

## Editorial accounting

The TeX-prose estimate changes from 9,602 to 7,317 words. The extracted-PDF alphabetic-token count changes from 11,015 to 8,394. The first method removes math, comments and identifiers before tokenization; the second includes headings, running headers and mathematical letters. Both include bibliography. These are explicit text-count conventions, not scientific metrics.

The internal-name/commit/trial/delivery-history scan finds zero matches outside the single public AI-use paragraph. That paragraph names Codex and Claude Code once each as explicitly requested. There are no mathematical-symbol exceptions. Current version/date and bibliographic version designations remain. Displayed math blocks, the three numbered definition/theorem/corollary blocks and all thirty claim IDs retain exact bytes.

## Paragraphs moved or rewritten

Each entry gives its predecessor line where available and retains the exact original text. Mixed paragraphs are rewritten in the article with their mathematical content retained; provenance clauses move here. Later edits to an already rewritten passage have no predecessor line and are explicitly identified that way. The original article remains bundled, so every change can also be read as a conventional diff.

### Edit 1: predecessor line 23

Move verification history; retain current mathematics and scope.

```tex
Version 5.0, 20 October 2026
```

### Edit 2: predecessor line 26

Move verification history; retain current mathematics and scope.

```tex
We study literal linear generalized Stone--Wales paths in fullerene
duals. Our main result concerns an integer affine family admitting a
fixed decomposition into embedded convex lattice polygons with sides
in the six triangular-lattice directions. With fixed gluing and affine
corner coordinates, we give a uniform reduction of literal-path
existence to a fixed monadic second-order sentence over unary finite
words, using maximal face passages, their two-row outputs and all
vertex collisions. Eventual periodicity on every eventually valid
integer affine ray then follows from the known equivalence between
MSO and regular languages. This is a geometric definability reduction,
not a new general periodicity principle. We record
the resulting ray statements for eleven specified catalogue families,
alongside closed conditions on their stated domains. Existing Lean
results establish arithmetic periodicity of several family predicates
and determine two example rays for every ray parameter. For K3, C1 and O2, stated-domain graph classifications are Lean-proved;
these families and D14 also have Lean actual-path periodicity on positive
integer affine rays, on explicit quotient specifications without the
general prose bridge. Parameter-one
rays are included; the O2 absence domain is $t,d\ge2$. The separate
C1 and O2 IPR conditions are outside Lean. The general
eventual-periodicity statement is now proved
in Lean against a specification written by the coordinator before the
proof. Its correspondence to the geometric hypotheses is an explicit
prose lemma, not a Lean theorem. The proof was supplied by Claude
workers; no independent Lean proof by the research team is claimed.
The separate R004 prose derivation is retained. Prior owner confirmation of the general specification is retained as a
historical record, not a new verification procedure. Human proof peer review
and novelty remain open;
no executable geometric-to-MSO compiler or period algorithm is supplied.
```

### Edit 3: predecessor line 58

Move verification history; retain current mathematics and scope.

```tex
\noindent\textbf{Editorial and evidence status.}
This English edition continues Japanese v3, with convex-face Theorem 1a
and catalogue Corollary 1b as its main results. The fixed-oblique-direction
extension remains a proof sketch outside the abstract's claims.
Section~\ref{sec:novelty} separates the geometric reduction from known
MSO, parametric Presburger and fixed-boundary periodicity results.
R004 derived the convex-face proof without reading the research team's
proof, construction or code; the statement was known. The O2 mapping
metadata and D12 single-point disclosures remain: strict blindness is
not claimed. One AI coordinator reviewed the route. Translation and
packaging supply neither a third derivation nor human peer review.
The coordinator-written Theorem 1a specification has a Lean proof and
saved six-kernel acceptance. On 20 October 2026, the owner read version 2
with the Japanese guide and addendum and confirmed its statement meaning,
not its proof or prose correspondence. Earlier authorship, affiliation,
licensing and statement records remain factual; owner statement-meaning
checks ended as a procedure that day. K3, C1, O2 and D14 correspondence instead
uses prior specifications, independent AI statement readers and finite
comparisons. No new owner-confirmation procedure is added. A3's
classification and 816-class census belong to the separate first paper.
A new D12 classification is not incorporated.

\clearpage
```

### Edit 4: predecessor line 105

Move verification history; retain current mathematics and scope.

```tex
The conditional finite-graph statement is formalized as
\record{R002.finite_literal_path_decision}. Its hypotheses and fixed
start must be supplied by geometry. The noncomputable construction
is not a certified executable Python or C classifier. For fullerene
duals, the nonfacial-three-cycle exclusion in the received prose route
uses the established cyclic edge-connectivity result cited in
\cite{Connectivity}; the original proof of that external result was
not rechecked by the editor.
```

### Edit 5: predecessor line 151

Move verification history; retain current mathematics and scope.

```tex
for all $t\ge t_0$. The received theorem proves existence. No practical
threshold, least period or implemented geometric-to-MSO/DFA compiler
is supplied. The specification-level existence theorem is now
Lean-proved; the prose correspondence lemma below transfers it to
these geometric hypotheses. Section~\ref{sec:proof} retains the
independent prose route; its original proof, corrections and
coordinator review are fixed in the packet. The hypotheses describe the objects
to which it applies, not a generic validity-testing algorithm.
```

### Edit 6: predecessor line 161

Move verification history; retain current mathematics and scope.

```tex
\paragraph{Prose correspondence lemma (not formalized in Lean).}
```

### Edit 7: predecessor line 163

Move verification history; retain current mathematics and scope.

```tex
\record{ClaudeChallenge2.Sig}
```

### Edit 8: predecessor line 198

Move verification history; retain current mathematics and scope.

```tex
prose, not a theorem certified by the Lean kernel. Thus sites
```

### Edit 9: predecessor line 213

Move verification history; retain current mathematics and scope.

```tex
These geometric identifications and the
external fullerene fact are part of this prose bridge, not additional
Lean-proved declarations or a fresh audit of the cited proof.
```

### Edit 10: predecessor line 217

Move verification history; retain current mathematics and scope.

```tex
Apply \record{ClaudeChallenge2.main} on the resulting tail.
```

### Edit 11: predecessor line 219

Move verification history; retain current mathematics and scope.

```tex
branch. The received Lean declaration \record{ClaudeChallenge2.main_residue}
then combines the branches in the original parameter, assuming eventual
```

### Edit 12: predecessor line 224

Move verification history; retain current mathematics and scope.

```tex
The owner confirmed the version-2 specification's meaning on
20 October 2026; the check is recorded in \record{OWNER-STATEMENT-CHECK.md}.
It is not proof peer review or review of this prose correspondence lemma.
```

### Edit 13: predecessor line 253

Move verification history; retain current mathematics and scope.

```tex
This section presents R004's second derivation on the common
six-direction domain. It does not use the uncompleted oblique-direction
transfer conditions. Its arithmetic-to-word reduction is specific;
arbitrary Presburger relations are not claimed to be finite-word MSO.
```

### Edit 14: predecessor line 302

Move verification history; retain current mathematics and scope.

```tex
The last constant was corrected by hand in the received proof, followed
by a new finite check; the check did not originally discover that error.
```

### Edit 15: predecessor line 438

Move verification history; retain current mathematics and scope.

```tex
Theorem~\ref{thm:aligned}. The geometric reduction belongs to the
received R004 proof, not to the cited automata theorem. Neither the
full proof of that external theorem nor an MSO compiler was newly
verified by this manuscript's editor.
```

### Edit 16: predecessor line 445

Move verification history; retain current mathematics and scope.

```tex
The applicability evidence is R004's fixed family-decomposition report
and its coordinator review. D12 uses two subdivided hexagons and D14
```

### Edit 17: predecessor line 475

Move verification history; retain current mathematics and scope.

```tex
Family and domain & Received reason for all valid affine rays
```

### Edit 18: predecessor line 488

Move verification history; retain current mathematics and scope.

```tex
This proves Corollary~\ref{cor:catalog} using the stated geometric
receipts and the separate arithmetic results. It does not cover all
112 catalogue entries or every zero-boundary degeneration.
```

### Edit 19: predecessor line 493

Move verification history; retain current mathematics and scope.

```tex
The following are received classifications of valid catalogue graphs.
The R004 prose arguments are retained; K3, C1 and O2 now additionally
have Lean graph classifications on their respective stated domains. Independent derivation of the same conclusion is distinct
from checking every coordinate convention in the research team's
tables. Lean arithmetic for a predicate does not by itself prove its
equivalence to a graph property.
```

### Edit 20: predecessor line 504

Move verification history; retain current mathematics and scope.

```tex
Received scope
```

### Edit 21: predecessor line 505

Move verification history; retain current mathematics and scope.

```tex
Integer GC for $r\ge2$; at 1 no degree-six vertex. R004 report 4 and GC proof.
```

### Edit 22: predecessor line 506

Move verification history; retain current mathematics and scope.

```tex
Existing $C_{60}$ witness and integer GC. R004 report 14 does not supply a new $p=1$ witness.
```

### Edit 23: predecessor line 507

Move verification history; retain current mathematics and scope.

```tex
R004 prose proof retained; Lean graph iff received for paths only. The IPR condition is outside Lean.
```

### Edit 24: predecessor line 508

Move verification history; retain current mathematics and scope.

```tex
R004 report 4 and B2 proof, whole positive domain.
```

### Edit 25: predecessor line 509

Move verification history; retain current mathematics and scope.

```tex
R004 positive and necessary prose proofs retained; full Lean graph iff now received, without a prose bridge.
```

### Edit 26: predecessor line 510

Move verification history; retain current mathematics and scope.

```tex
R004 prose absence retained; Lean graph absence received, without a prose bridge. IPR remains outside Lean.
```

### Edit 27: predecessor line 511

Move verification history; retain current mathematics and scope.

```tex
R004 reports 5--6 and both prose directions. Predicate-ray arithmetic formalized; full graph iff not formalized.
```

### Edit 28: predecessor line 519

Move verification history; retain current mathematics and scope.

```tex
The research
team's full table of eighteen E10 regions, walls and witnesses is not
all independently reviewed.
```

### Edit 29: predecessor line 525

Move verification history; retain current mathematics and scope.

```tex
For O2, absence on $t,d\ge2$ now also has a Lean graph proof, while
IPR on that domain remains a received prose result. The mapping-metadata
disclosure is retained. Boundary paths for O2$(1,d)$ with $d\ge3$ and
O2$(t,1)$ with $t\ge3$ are Lean-proved; existence at O2$(1,1)$,
O2$(1,2)$ and O2$(2,1)$ is outside the received Lean results. The ray
theorem nevertheless covers these constant rays without deciding their
path existence. For D14, the auxiliary Lean lemma
\record{Claude5D14.d14_no_path} now proves absence for $r,s\ge2$.
It is not a Comparator target: the six-kernel D14 receipt covers only
\record{ClaudeChallengeD14.main}. Boundary paths at $(1,s)$, $s\ge2$,
and $(r,1)$, $r\ge2$, are also received Lean lemmas. Existence at
D14$(1,1)$ remains outside Lean. No new standalone D14 iff is asserted
here. R004's separate D14 prose ray proof is retained.
For D1 with both parameters at least two, the research team retains
a belt-based absence draft; R004's all-ray
periodicity receipt is not a new independent proof of that closed
absence claim. Common integer scaling by at least two gives absence
in the specified leapfrog domains, but does not classify their
primitive points.
```

### Edit 30: predecessor line 545

Move verification history; retain current mathematics and scope.

```tex
For E10$(p,1,s)$, $m=s+2$, the research team's witnesses give
```

### Edit 31: predecessor line 552

Move verification history; retain current mathematics and scope.

```tex
These three examples are non-IPR. R004's report 4 independently
constructed and checked them. This is minimality only inside the
$r=1$ E10 family, not a general iff.
```

### Edit 32: predecessor line 556

Move verification history; retain current mathematics and scope.

```tex
The pre-existing D12 branches are retained as historical scope:
```

### Edit 33: predecessor line 559

Move verification history; retain current mathematics and scope.

```tex
research team's $|r-3s|=1$ and $r\ge4s$ branches have their earlier
review limitations. A full D12 classification, including newer work,
is outside this paper and this packet.
```

### Edit 34: predecessor line 579

Move verification history; retain current mathematics and scope.

```tex
theory. The received Lean files establish the exact predicates below.
```

### Edit 35: predecessor line 587

Move verification history; retain current mathematics and scope.

```tex
\record{Claude2.k3_ray_all} proves eventual periodicity of
```

### Edit 36: predecessor line 591

Move verification history; retain current mathematics and scope.

```tex
\record{k3_ray_const} gives eventual constancy.
```

### Edit 37: predecessor line 592

Move verification history; retain current mathematics and scope.

```tex
constant, \record{k3_ray_period} gives period $b$ from any specified
```

### Edit 38: predecessor line 595

Move verification history; retain current mathematics and scope.

```tex
\record{Claude2.e10_ray_all} proves the corresponding all-ray statement
```

### Edit 39: predecessor line 598

Move verification history; retain current mathematics and scope.

```tex
constant; when it is constant, \record{e10_ray_period} gives that
```

### Edit 40: predecessor line 599

Move verification history; retain current mathematics and scope.

```tex
positive modulus as a period on the given domain tail.
```

### Edit 41: predecessor line 601

Move verification history; retain current mathematics and scope.

```tex
\record{b2_ray_all}, \record{c1_ray_all}, \record{a1_ray_all} and
\record{a2_ray_all} give eventual constancy of their domain-qualified
```

### Edit 42: predecessor line 620

Move verification history; retain current mathematics and scope.

```tex
The first paper proves the full graph classification. Its
\record{ClaudeCor.criterion_ray}, restated as \record{Claude2.a3_ray},
formalizes the arithmetic existence of a threshold and positive
period. A separate release bridge gives graph-path periodicity.
Neither result certifies an executable threshold/period algorithm.
R004's separate arithmetic argument permits period $|\Delta|$ for
nonconstant $\Delta\ne0$ rays and period 1 otherwise. This is not a
least-period statement or formalization of the general geometric
theorem. After classification, eventual periodicity is also a
consequence of \cite[Theorem 1.15]{BGW} and is not a separate novelty claim.
```

### Edit 43: predecessor line 642

Move verification history; retain current mathematics and scope.

```tex
The original compressed-word calculations did not use the known
family congruences. Later independent prose arguments recover all
$t$ from independently derived family conditions, or from explicit
D12 blocks. The expected statements were known, not blind predictions.
```

### Edit 44: predecessor line 647

Move verification history; retain current mathematics and scope.

```tex
\record{Claude2.k3_example} now proves for every $t\in\N$
```

### Edit 45: predecessor line 650

Move verification history; retain current mathematics and scope.

```tex
\record{Claude2.e10_example} proves the corresponding E10 predicate
```

### Edit 46: predecessor line 656

Move verification history; retain current mathematics and scope.

```tex
The earlier D12 two-ray receipt covers every $s\ge41$:
D12$(3s+2,s)$ is negative and D12$(3s+1,s)$ has a path with
$56s+12$ distinct vertices. Its reported computer-assisted proof checks
2,058 nonnegativity conditions and 756 no-integer-solution conditions,
2,814 in total. A separately coded reread by the same verifier is not
a further reviewer. The coordinator's independent construction at
$s=58$ agrees, with a 3,260-vertex positive witness; it does not audit
all 2,814 conditions. These records are neither Lean proofs nor a
full D12 classification.
```

### Edit 47: predecessor line 666

Move verification history; retain current mathematics and scope.

```tex
\section{Received formalization and what it does not cover}\label{sec:formal}
\subsection{Theorem 1a on the coordinator's specification}
The current entry points are \record{ClaudeChallenge2.main} in
\record{Formal/Claude3ComparatorSolution.lean} and
\record{ClaudeChallenge2.State.main_statement} of type
\record{ClaudeChallenge2.MainStatement} in \record{Formal/Claude3Thm1a.lean}.
For every fixed signature $S$ and $t_1$, they prove that if
\record{Valid} $S\,t$ and \record{TrianglesInCharts} $S\,t$ hold for all
$t\ge t_1$, then some $t_0$ and positive $P$ satisfy
\record{PathExists} $S\,t\leftrightarrow$ \record{PathExists} $S\,(t+P)$
for every $t\ge t_0$. The independent challenge was written by the
coordinator before the proof and amended to version 2 to include
\record{TrianglesInCharts}. The paper-to-specification passage is the
prose lemma following Theorem~\ref{thm:aligned}; it is not formalized.
The Lean assumptions are weaker than the paper's geometric hypotheses:
they do not require a sphere, exactly twelve cones, or nondegenerate
polygon disks. With the same conclusion, the exact formal result is
therefore a stronger sufficient theorem, not a literal restatement
of the paper's geometric objects.
\record{ClaudeChallenge2.main_residue} in \record{Formal/Claude3Residue.lean}
proves the fixed-residue variant after the decision-to-branch agreements
are supplied.

The proof was supplied by Claude workers, through finite-word MSO,
height folding, chart geometry, quotient identifications, state
reduction and sentence assembly. It is not an independent Lean
proof by the research team. The research team's serial build and
fresh axiom queries for all three declarations found only
\record{propext}, \record{Classical.choice} and \record{Quot.sound}.
The saved coordinator Comparator receipt reports six kernels
accepting the proof of \record{ClaudeChallenge2.main} in paranoid mode;
that receipt is not a separate six-kernel check of the residue declaration.
This edit does not rerun external kernels or provide OS process isolation.
The owner's version-2 statement-meaning confirmation is recorded
separately. Human proof peer review remains unrecorded. Neither this formalization nor
R004's separate prose proof establishes novelty or an executable
geometric compiler, practical threshold, or least period.
```

### Edit 48: predecessor line 706

Move verification history; retain current mathematics and scope.

```tex
The new entry declarations are
\begin{quote}\small\noindent
\record{Claude4K3.k3_statement} : \record{Claude2Aligned.K3Statement};\\
\record{Claude4K3.noThree};\\
\record{ClaudeChallengeK3.main}.
\end{quote}
For natural $r,s\ge2$, the first proves the full iff between an actual
literal path in \record{Claude2Aligned.k3Graph}$(r,s)$ and
$s\equiv\pm1\pmod r$. The second proves that no edge has three common
neighbours, using a classification of graph triangles in the cap or tube.
Together with the earlier necessity machinery, this supplies the missing
necessity direction. R004's positive and necessary prose proofs remain
separate evidence.

The third proves eventual periodicity of literal-path existence on every
ray $(r,s)=(r_0+at,s_0+bt)$ with $r_0,s_0\ge1$ and $a,b\ge0$.
There are no \record{Valid} or \record{TrianglesInCharts} hypotheses.
The K3 gap previously filled by the general prose correspondence lemma is
therefore closed in Lean on this explicit quotient specification. The
proof constructs the needed common-neighbour property directly and does
not construct a signature isomorphism into Theorem 1a.
Nonconstant parameter-one boundary rays use explicit eventual paths;
constant rays are periodic because their decision never changes. The
modular iff itself is still restricted to $r,s\ge2$.
```

### Edit 49: predecessor line 734

Move verification history; retain current mathematics and scope.

```tex
 definitions are those of the first paper's specification.
The earlier sufficient declaration \record{Claude2K3.k3_sufficient}
of type \record{Claude2Aligned.K3Sufficient} is retained.
```

### Edit 50: predecessor line 738

Move verification history; retain current mathematics and scope.

```tex
The proof follows R004's tube construction.
```

### Edit 51: predecessor line 754

Move verification history; retain current mathematics and scope.

```tex
\record{Claude2K3.deg_corner} proves degree five for all twelve labelled
```

### Edit 52: predecessor line 755

Move verification history; retain current mathematics and scope.

```tex
corner representatives. It does not by itself prove they exhaust all
degree-five vertices or all global vertex types.
```

### Edit 53: predecessor line 758

Move verification history; retain current mathematics and scope.

```tex
\record{deg_hex_interior} proves degree six in hexagon interiors.
```

### Edit 54: predecessor line 760

Move verification history; retain current mathematics and scope.

```tex
\record{deg_tri_interior} proves degree six in the six noncentral cap-triangle interiors.
```

### Edit 55: predecessor line 761

Move verification history; retain current mathematics and scope.

```tex
General seam interiors and the central cap triangles are not covered
by those older partial degree lemmas alone. The new necessity proof
uses the cap/tube triangle classification and common-neighbour bound;
the K3 iff in Section~\ref{sec:conditions} is now formalized. This does
not relabel the partial degree lemmas as a global degree classification.

The older graph definitions were written by a Claude worker. Before
the new proof, the coordinator copied them into a separate K3 challenge.
Static comparison confirms the copied definitions and the version-2
challenge/solution statement agree. An independent AI reader of version 1
found the missing parameter-one boundaries; version 2 corrected them
before the proof. The reader's finite checks and a separate Python mirror
support the catalogue correspondence, without constituting a universal
catalogue-isomorphism proof or human proof review. No owner-confirmation
field or procedure is used for K3. Shared specification files contain
unused D12 definitions, but no new D12 classification is a root or
claimed result of this package.
```

### Edit 56: predecessor line 780

Move verification history; retain current mathematics and scope.

```tex
The two received entry declarations are
\begin{quote}\small\noindent
\record{ClaudeChallengeC1.classification};\\
\record{ClaudeChallengeC1.main}.
\end{quote}
On \record{Claude2Aligned.c1Graph}$(r,s)$, natural $r,s\ge1$ admit a
literal path if and only if $s=1$. Lean's $r,s$ are the paper's $a,b$;
this is the path condition $b=1$ in Section~\ref{sec:conditions},
including $a=1$. The separate IPR equivalence $a,b\ge2$ is not stated
or proved by these declarations. R004's C1 prose proof remains separate
evidence. The second declaration proves actual-path eventual periodicity
on every ray $(r_0+ut,s_0+vt)$ with $r_0,s_0\ge1$ and $u,v\ge0$,
including constant rays. Eventually positive integer rays are covered
after shifting their starting index; this reindexing is explanatory
arithmetic, not a separately received all-integer Lean declaration.
```

### Edit 57: predecessor line 797

Move verification history; retain current mathematics and scope.

```tex
The vertex bijection
\record{Claude4C1.vEquiv} and adjacency theorem \record{adj_iff} identify
```

### Edit 58: predecessor line 801

Move verification history; retain current mathematics and scope.

```tex
The transfer \record{Claude4C1.c1_iff_g4} preserves literal-path
existence.
```

### Edit 59: predecessor line 804

Move verification history; retain current mathematics and scope.

```tex
and an explicit path for $s=1$. It does not use the external cyclic
edge-connectivity theorem of the R004 prose argument. C1 thus needs
no general prose geometric-to-specification bridge for these path claims.
```

### Edit 60: predecessor line 808

Move verification history; retain current mathematics and scope.

```tex
The coordinator fixed the specification and challenge before the proof.
One independent AI statement reader returned ``faithful with caveats'',
checking the parameter correspondence by the area formula
$8r^2+16rs+4s^2$ and identifying IPR as outside the challenge.
The saved mirror agrees with the R004 construction on counts, degree
sequence and the path decision for 36 pairs $1\le r,s\le6$; the reader's
25 finite pairs lie within that range and are not a second disjoint census.
These finite checks are not a universal catalogue-isomorphism certificate
or human proof review. No owner-confirmation field or procedure is added.
The challenge has two intentional placeholders and is excluded from proof
dependencies; the solution proves both statements. Exact sources and
receipt hashes are supplied in the machine packet.
```

### Edit 61: predecessor line 822

Move verification history; retain current mathematics and scope.

```tex
The received declarations are
\begin{quote}\small\noindent
\record{ClaudeChallengeO2.classification};\\
\record{ClaudeChallengeO2.main}.
\end{quote}
The first proves that \record{Claude2Aligned.o2Graph}$(t,d)$ has no literal
path for natural $t,d\ge2$. The second proves actual-path eventual
periodicity on every ray $(t_0+an,d_0+bn)$ with $t_0,d_0\ge1$ and
$a,b\ge0$, including parameter-one and constant rays. The parameter
names agree with the paper. Reindexing an eventually positive integer
ray to its positive tail remains explanatory arithmetic. R004's prose
absence proof is retained; these O2 path claims now need no general
prose geometric-to-specification bridge. IPR is not formalized.
```

### Edit 62: predecessor line 838

Move verification history; retain current mathematics and scope.

```tex
of side $t$. The equivalence \record{Claude5O2.o2_iff_gm} identifies it
```

### Edit 63: predecessor line 843

Move verification history; retain current mathematics and scope.

```tex
strips. It does not use the external cyclic edge-connectivity theorem
of the R004 prose argument.
```

### Edit 64: predecessor line 847

Move verification history; retain current mathematics and scope.

```tex
Path existence at $(1,1),(1,2),(2,1)$ is not
proved in Lean by this receipt.
```

### Edit 65: predecessor line 850

Move verification history; retain current mathematics and scope.

```tex
The saved finite mirror finds paths there,
which is finite evidence outside Lean.
```

### Edit 66: predecessor line 853

Move verification history; retain current mathematics and scope.

```tex
The specification and challenge were fixed before the proof by a
separate statement writer. One independent AI statement reader returned
``faithful with caveats'', confirming the path domains and the carbon
order $14t^2+16td+2d^2$, while retaining a caveat about identification
with the named catalogue family. Its 36 known pairs lie within the
saved mirror's 80 pairs $1\le t\le8$, $1\le d\le10$; they are not
a second disjoint census or a universal catalogue-isomorphism theorem.
The received mirror agrees with the verifier's construction on the
recorded graphs and decisions. No new owner-confirmation field,
human proof review or independent Lean derivation is added. The inert
challenge has two intentional placeholders and is excluded from proof
dependencies. Source and record hashes are supplied in the machine layer.
```

### Edit 67: predecessor line 867

Move verification history; retain current mathematics and scope.

```tex
The received entry \record{ClaudeChallengeD14.main} proves actual-path
eventual periodicity on \record{Claude2Aligned.d14Graph}$(r,s)$ for all
natural starts $r_0,s_0\ge1$ and nonnegative slopes, including
parameter-one and constant rays. It is the only D14 Comparator target;
there is no challenge classification theorem. The general prose
geometric-to-specification bridge is not used for this family result.
R004's separate prose route remains evidence for the catalogue-ray claim.
```

### Edit 68: predecessor line 876

Move verification history; retain current mathematics and scope.

```tex
$s,2r+s$, subdividing each long side as $r,s,r$. The equivalence
\record{Claude5D14.d14_iff_gm} maps the quotient to two lattice hexagons
```

### Edit 69: predecessor line 882

Move verification history; retain current mathematics and scope.

```tex
Twelve closed strips cover all 120 starts. No external cyclic
edge-connectivity theorem is used.
```

### Edit 70: predecessor line 885

Move verification history; retain current mathematics and scope.

```tex
The auxiliary \record{Claude5D14.d14_no_path} proves absence for
$r,s\ge2$. The lemmas \record{Claude5D14.pe_R1} and
\record{Claude5D14.pe_S1} give explicit paths at $(1,s)$ for $s\ge2$
and $(r,1)$ for $r\ge2$. They are received build/axiom-report results,
not separate targets of the six-kernel Comparator run. Existence at
$(1,1)$ is not Lean-proved here; the constant-ray result does not need
that decision. We do not add a new standalone iff theorem.

A separate writer fixed the specification and main statement before the
proof. One independent AI reader returned ``faithful with caveats'',
confirming the parameter order and carbon order $8r^2+24rs+12s^2$,
while retaining the named-catalogue correspondence caveat. Its 25 known
pairs are contained in the saved mirror's 81 pairs $1\le r,s\le9$;
these are overlapping finite checks, not a universal catalogue-isomorphism
proof or human review. Exact definition/type/source comparisons and
original-record hashes are supplied in the machine layer. No new
owner-confirmation procedure is used. Eventually positive integer rays
are reindexed to a positive natural tail in exposition, rather than
claimed as a separately received all-integer declaration.
```

### Edit 71: predecessor line 905

Move verification history; retain current mathematics and scope.

```tex
\subsection{Historical conditional kernels}
```

### Edit 72: predecessor line 907

Move verification history; retain current mathematics and scope.

```tex
The earlier research layer supplies conditional pieces:
```

### Edit 73: predecessor line 916

Move verification history; retain current mathematics and scope.

```tex
The geometric hypotheses, all-start coverage, full compressed action
and a certified program are not supplied by those conditional types.
There were historically 57 such research declarations; the former
total 98 also counted 41 A3 arithmetic entries. Neither count is a
formalization percentage or the current library size.

\subsection{Pins, receipt scope and proof dependencies}\label{sec:formal-records}
The received toolchain is Lean 4.35.0 with the fixed mathlib manifest.
The earlier arithmetic and K3 sufficiency reports record only
\record{propext}, \record{Classical.choice}, \record{Quot.sound} as
transitive axioms. Their receipt bytes and scopes are retained.
For Theorem 1a, its separate source closure and the earlier research-team
build/axiom output remain fixed. For the new K3 results, the coordinator
records a successful build and standard-three-axiom queries for all three
entry declarations. The research team receives and hash-checks these
records without running Lean.

The saved six-kernel K3 Comparator receipt checks
\record{ClaudeChallengeK3.main} in paranoid mode only; it is not a separate
six-kernel check of \record{k3_statement} or \record{noThree}.
It is also distinct from the earlier Theorem 1a and A3 receipts.
All six kernels check the same proof, not six independent derivations.
The K3 execution lacked OS process isolation on macOS. For C1, a separate
paranoid Comparator receipt covers both
\record{ClaudeChallengeC1.classification} and \record{ClaudeChallengeC1.main}:
all six kernels accepted the same two supplied proofs. The coordinator
also records a successful build and standard-three-axiom queries for
both declarations. The worker report predates that Comparator run;
its not-run note is retained as historical. C1 likewise lacked OS process
isolation on macOS. A separate O2 paranoid Comparator receipt likewise
covers both \record{ClaudeChallengeO2.classification} and
\record{ClaudeChallengeO2.main}, with all six kernels accepting the same
supplied proofs. The coordinator reports successful builds and
standard-three-axiom queries for both. The worker report precedes the
Comparator run and its not-run note is historical. O2 also lacked OS
process isolation on macOS. For D14, the separate six-kernel receipt
checks only \record{ClaudeChallengeD14.main}. The auxiliary absence and
boundary lemmas are not Comparator targets. The coordinator separately
reports successful builds and standard-three-axiom queries for main and
\record{d14_no_path}; the worker also reports the boundary-lemma queries.
The worker's pre-Comparator not-run note is historical. D14 likewise
lacked OS process isolation. No external kernel or Lean command is rerun
for this edition.
The claims' expository dependencies and Lean's imported proof-term
dependencies are different. A prose statement can remain open for
its coordinate or human-semantic bridge while a separate exact
formal declaration is proved. Conversely the proved arithmetic
predicates do not supply their graph iff interpretation. No human
peer review of the proofs is recorded and novelty is not established.
```

### Edit 74: predecessor line 968

Move verification history; retain current mathematics and scope.

```tex
\textbf{Status.} The coordinator has reviewed the skeleton of AN
Sections 2--6 as a plausible proof sketch. Explicit Section 5 transfer
conditions and numerical validation remain incomplete; no independent
second proof covers this wider domain. Four obligations below remain.
This section is not part of the main theorem or the abstract's result.
```

### Edit 75: predecessor line 987

Move verification history; retain current mathematics and scope.

```tex
The AL/AM/AH proposal
```

### Edit 76: predecessor line 1032

Move verification history; retain current mathematics and scope.

```tex
verify the AH/AM affine tower coefficients
```

### Edit 77: predecessor line 1064

Move verification history; retain current mathematics and scope.

```tex
For the fixed-cylinder argument AD let
```

### Edit 78: predecessor line 1082

Move verification history; retain current mathematics and scope.

```tex
The old D12$(3,3t+4)$ example
```

### Edit 79: predecessor line 1084

Move verification history; retain current mathematics and scope.

```tex
The former general bounded-passage forecast was withdrawn.
```

### Edit 80: predecessor line 1086

Move verification history; retain current mathematics and scope.

```tex
\subsection{Dated finite evidence}
```

### Edit 81: predecessor line 1088

Move verification history; retain current mathematics and scope.

```tex
The packet retains, rather than reruns, the relevant evidence.
T0770 compares 1,809 arithmetic values on nine known A3 rays;
T0771 adds fourteen graph decisions on an independent constructor.
Those fourteen are not unseen tests and the 1,809 values are not counted
twice. T0887 checks fixed tail coefficients beyond 64 on those rays.
T0888 audits E10's fixed descriptor: eight charts, 36 inverse gluings,
108 intervals, 156 connections, 120 descriptors and twelve labels.
T0889 audits 71 charts, 342 edges and 21 single-zero boundaries.
These are finite checks of supplied data, not the general ownership
theorem. The recorded AM audit has 6,564 inputs and 67,312 states;
the AN phase audit has 48 directions, 14,904 entrances, 4,005 intervals
(1,013 empty), 5,496 lifts and 40,380 conjugacy cells.

R004's report-14 finite arithmetic check has 378 coefficient
representations and 13,430 pairs, maximum recorded period 44 and
threshold 69. The report-15 checks include 7,056 strips, 2,255 nonempty
row outputs, 16,212 subintervals, 99,225 ordered row pairs and 509,160
folded-point comparisons. Their hand-found row correction and earlier
type/key failures are kept with their chronology. Numerical agreement
does not replace either general proof or repair its hypotheses.
No graph construction, R004 checker, or historical scientific audit
was rerun for this translation.

The K3 worker's earlier finite mirror agreed with its specification
and the verifier's construction on the stated known samples. The two
constructions and generated Lean text are separate from the kernel
proof. Generated degree formulas were fitted from sample data, but the
received Lean theorem checks their universal statements; samples alone
would not justify sufficiency. The worker's mirror is not a new
independent reviewer of its own specification.
```

### Edit 82: predecessor line 1125

Move verification history; retain current mathematics and scope.

```tex
The HTML numbering is Theorem 3.2; the same v1 PDF calls it Theorem 14.
```

### Edit 83: predecessor line 1181

Move verification history; retain current mathematics and scope.

```tex
For these two sources (S2191, S2192), only the official abstracts and
bibliographic records were obtained. We do not infer their full
hypotheses or claim an application from an unread theorem.
```

### Edit 84: predecessor line 1196

Move verification history; retain current mathematics and scope.

```tex
The received R005 comparison read the theorem statements and specified
sections listed in the packet's source records, not all proofs. Within
that reading, no prior result giving the full claim from the same
geometric hypotheses was located. Novelty is not established.
```

### Edit 85: predecessor line 1206

Move verification history; retain current mathematics and scope.

```tex
The general convex-face proof is received research work, not an
already published theorem cited as external authority. Human proof
peer review and full comparison with catalogue/zigzag theory remain
necessary. The extension's unfinished geometric details do not
disappear on receipt of the convex-face proof.
```

### Edit 86: predecessor line 1221

Move verification history; retain current mathematics and scope.

```tex
The stronger M4/M4-prime
questions remain separate.
```

### Edit 87: predecessor line 1257

Move verification history; retain current mathematics and scope.

```tex
\section{Representative formal statements and source correspondence}\label{app:correspondence}
The accompanying \record{v3-correspondence.md} maps every numbered v3
section to this reorganization, including the moved oblique-direction
sketch. It distinguishes translation, condensation and formal-status
updates; no prose-equivalence theorem is claimed.

The primary received declarations now include
\record{ClaudeChallenge2.main} and
\record{ClaudeChallenge2.State.main_statement} and
\record{ClaudeChallenge2.main_residue}, followed by
\record{Claude2.k3_ray_all}, \record{Claude2.e10_ray_all},
\record{Claude2.k3_example}, \record{Claude2.e10_example}, and
\record{Claude2K3.k3_sufficient}. The new K3 entries are
\record{ClaudeChallengeK3.main}, \record{Claude4K3.k3_statement} and
\record{Claude4K3.noThree}. The new C1 entries are
\record{ClaudeChallengeC1.classification} and \record{ClaudeChallengeC1.main}.
The O2 entries are \record{ClaudeChallengeO2.classification} and
\record{ClaudeChallengeO2.main}. The D14 entry is
\record{ClaudeChallengeD14.main}; its auxiliary absence lemma
\record{Claude5D14.d14_no_path} has a separate build/axiom-report scope.
The machine layer supplies their exact
types, source commit and the kind of proof receipt. The historical
representative kernel types remain:
\begin{quote}\small
\record{finite_literal_path_decision}: finite type, two-common-neighbour
hypothesis, cone predicate and fixed oriented triangle imply a first
repeat at most the number of vertices, and path existence iff a legal
endpoint occurs before it.\par
\record{cylinder_portal_shift}: a B\'ezout witness for primitive $u$
and $g\mid Q/\mathrm{cylHeight}(u,v)$ imply that the stated shifted
displacement is a multiple of $gu$. The integer-division and
divisibility hypotheses are retained.\par
\record{induction_uniform_depth}: a finite-list child relation with a
strictly decreasing lexicographic natural rank has a finite uniform
depth from each starting state.\par
\record{iet_component_uniform_depth}: the concrete equal-final-label
removal component has such a depth; the omitted IET branches are not
thereby formalized.
\end{quote}
The supplied exact sources, not these paraphrases, determine the Lean
types. Dependency revisions are pinned in \texttt{lake-manifest.json}
and the toolchain in \texttt{lean-toolchain}. Caches, compiled binaries
and raw graph streams are intentionally omitted; no separate artifact
collection is supplied. For optional local reproduction, obtain the pinned
dependencies through Lake and use \texttt{lake exe cache get} for mathlib
build artifacts. Contact is through GitHub Issues at the repository
specified in \texttt{REPOSITORY-URL.txt}.
```

### Edit 88: predecessor line 1306

Move verification history; retain current mathematics and scope.

```tex
The author used Codex and Claude Code
to assist with literature organization, mathematical exploration,
proof drafting, implementation, finite verification, formalization of
the explicitly identified arithmetic and graph statements and the
specification-level Theorem 1a, and English exposition. Claude workers
supplied the general theorem's, K3's, C1's, O2's and D14's Lean proofs against the
coordinator's prior specifications. The research team checked the
received sources and records; it did not supply an independent Lean
derivation or rerun Lean for this D14 edition. The author is responsible
for the published account, its provenance, and the stated limits of
verification. AI systems are not listed as authors. AI prose reviews
are identified separately from human review. Only the explicitly
listed Lean propositions are described as formally proved; finite
checks and independently constructed tests have their stated domains.
No claim of complete human checking of every argument is made.
```

### Edit 89: predecessor line 1344

Move verification history; retain current mathematics and scope.

```tex
2007. The received use is the cited established cyclic-connectivity
statement, not a new reading of its original proof.
```

### Edit 90: predecessor line 1357

Move verification history; retain current mathematics and scope.

```tex
The stored reading covers the stated main theorems, not the full proof.
```

### Edit 91: predecessor line 1361

Move verification history; retain current mathematics and scope.

```tex
The stored R005 reading distinguishes its nonzero-denominator hypothesis
from eventual positivity and from the several-interval setting.
```

### Edit 92: predecessor line 1376

Move verification history; retain current mathematics and scope.

```tex
2007, p.~1 only in the stored reading.
```

### Edit 93: predecessor line 1383

Move verification history; retain current mathematics and scope.

```tex
doi:10.1007/s11047-015-9527-0. Official abstract only.
```

### Edit 94: predecessor line 1386

Move verification history; retain current mathematics and scope.

```tex
doi:10.1007/3-540-57182-5\_66. Official abstract only.
```

### Edit 95: predecessor line 240

Move verification history; retain current mathematics and scope.

```tex
The K3, C1, O2 and D14 parts now have direct Lean ray proofs on their
```

### Edit 96: predecessor line 1034

Move verification history; retain current mathematics and scope.

```tex
dependent on the effective elimination result \cite{QE}, whose full
proof was not reaudited;
```

### Edit 97: predecessor line 1036

Move verification history; retain current mathematics and scope.

```tex
None is newly resolved here.
```

### Edit 98: predecessor line 1215

Move verification history; retain current mathematics and scope.

```tex
the stored survey did
not locate an identical general theorem; this is not a novelty proof.
```

### Edit 99: predecessor line 1232

Move verification history; retain current mathematics and scope.

```tex
The stored local coefficient audit gives
```

### Edit 100: predecessor line 1031

Move verification history; retain current mathematics and scope.

```tex
containment and order inequalities of the Section 5 transfer
```


## Article6.0 to6.1 scope-edit archive

The following seven predecessor passages are retained for editorial traceability; the replacement text is recorded in scope-edit-map.json. These are old passages, not current E10 proof assertions.

### E10 scope edit 1

```tex
Version 6.0, 21 October 2026
```

### E10 scope edit 2

```tex
Lean proofs establish K3 and C1 path classifications, O2 absence on
its stated domain, and positive-ray actual-path periodicity for K3,
C1, O2 and D14.
```

### E10 scope edit 3

```tex
K3, C1, O2, D14 & Lean quotient-graph proofs & K3 iff for $r,s\ge2$; C1 iff for $a,b\ge1$; O2 absence for $t,d\ge2$; all four positive-natural ray results.
```

### E10 scope edit 4

```tex
The K3, C1, O2 and D14 parts have direct family-specific ray proofs on their
quotient graphs, including positive boundary parameters, without invoking the
general prose correspondence lemma. Their ray declarations start with
positive natural coordinates and nonnegative slopes;
```

### E10 scope edit 5

```tex
E10, $p,r,s\ge1$ & Arithmetic for $r\ge2$; the five-piece decomposition includes $r=1$.
```

### E10 scope edit 6

```tex
Prose graph iff and Lean predicate-ray arithmetic.
```

### E10 scope edit 7

```tex
\subsection{Conditional auxiliary lemmas}
```

## Article6.2 to6.3 scope-edit archive

The following 17 predecessor passages are retained for editorial traceability; the replacement text is recorded in lines-v6.3-edit-map.json. These are old passages, not current D12 proof assertions.

### D12 scope edit 1

```tex
Version 6.2, 21 October 2026
```

### D12 scope edit 2

```tex
Lean proofs establish K3 and C1 path classifications, O2 absence on
its stated domain, and the E10 classification for $r\ge2$.
Positive-ray actual-path periodicity is Lean-proved for K3, C1, O2,
D14 and E10, including the E10 boundary $r=1$.
```

### D12 scope edit 3

```tex
K3, C1, O2, D14, E10 & Lean quotient-graph proofs & K3 iff for $r,s\ge2$; C1 iff for $a,b\ge1$; O2 absence for $t,d\ge2$; E10 iff for $p,s\ge1,r\ge2$; all five positive-natural ray results, including E10 $r=1$.
```

### D12 scope edit 4

```tex
D12 classification & Two prose/computer-assisted proof routes; no Lean & Positive integer $r,s$, with the quotient, geometric and certificate semantics stated in Section~\ref{sec:d12-classification}.\\
D12 ray consequence & Theorem~\ref{thm:aligned} with prose correspondence; alternatively classification and arithmetic & Every eventually positive integer affine ray. No family-specific Lean proof of D12.\\
```

### D12 scope edit 5

```tex
The K3, C1, O2 and D14 parts have direct family-specific ray proofs on
their quotient graphs, including positive boundary parameters. E10 also
```

### D12 scope edit 6

```tex
hypotheses proved on the E10 model. These five results use no general
```

### D12 scope edit 7

```tex
D12, D1 & The convex decompositions on valid positive integer parameters.\\
```

### D12 scope edit 8

```tex
The full D12 classification is given in Section~\ref{sec:d12-classification}.
```

### D12 scope edit 9

```tex
The D12 classification in Section~\ref{sec:d12-classification} retains its two prose/computer-assisted proof bases.
```

### D12 scope edit 10

```tex
For this positive-parameter quotient convention, the two proof routes
below give a literal path if and only if
```

### D12 scope edit 11

```tex
The all-parameter quotient geometry and catalogue correspondence,
the semantics of the computations and the inductions described below
are prose/computer-assisted premises of these routes. Neither route
is a Lean proof. Complete arguments, explicit strip formulas,
certificate inputs and their checkers accompany the D12 supplement.
```

### D12 scope edit 12

```tex
There is also an elementary arithmetic
consequence conditional on the classification.
```

### D12 scope edit 13

```tex
This arithmetic alternative
and the general ray-theorem application are separate from a
family-specific Lean formalization of D12.
```

### D12 scope edit 14

```tex
construction at $s=58$ gives a 3,260-vertex positive witness.
```

### D12 scope edit 15

```tex
fixed branches after their decisions agree with the original family.
```

### D12 scope edit 16

```tex
existing logical and fixed-boundary periodicity theorems.
```

### D12 scope edit 17

```tex
Report 9607, May 1996; printed pp.~11--12 (PDF pp.~14--15).
```
