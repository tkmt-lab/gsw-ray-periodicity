Current local candidate1.10.0 / article6.3; publication is separate under the author's decision.

## Current D12 proof scope (article 6.3 / packet 1.10.0)

Classification: `ClaudeChallengeD12.classification` proves, for natural r,s>=1, that the D12 quotient graph has a literal path iff r divides s-1 or s+1, or |r-3s|=1 (divisibility and absolute value in the integers). `ClaudeChallengeD12.main` proves actual-path eventual periodicity for every positive natural start and nonnegative natural slope. The ray result comes from the classification and Lean ray arithmetic; it uses neither Theorem 1a nor its prose bridge. No external theorem is used: the two-common-neighbour property is proved on the model. Both declarations depend only on propext, Classical.choice and Quot.sound, and both are the targets of the coordinator's six-kernel paranoid Comparator run (Lean paranoid, lean4lean, nanoda, con-leche, con-ron, Lean default all accept the same supplied proof; this is not six independent derivations).

Statement correspondence: the challenge (written before the proof) was read by one independent AI statement reader, verdict FAITHFUL WITH CAVEATS: the all-parameter identification with Graver's catalogue family is not formalized, and Definition 1(a) of the cited source was not compared verbatim. The writer's saved mirror agrees with the classification on 240 cases (r<=20, s<=12). Independence: the Lean proof was written after reading the route-A report and the article 6.2 D12 section, so it is not an independent third derivation; the kernel check makes it correct regardless. The two earlier prose/computer-assisted routes in d12/ remain as additional evidence.

Read `d12-manifest.json`, `VERIFICATION-RECORD.md` and `CI-AXIOM-SPLIT.md`. Current total: 495 Lean files = 489 proof/specification files plus six inert challenges. The D12 closure has 86 files: 82 new (81 proof + one specification) and 4 inherited; its separate inert challenge has two placeholders. All 412 predecessor Lean sources and old payloads retain exact bytes. Packaging ran no Lean, external kernel or scientific computation and performed no upload.

Historical checkpoint1.9.0 / article6.2.
## Current E10 proof scope (article6.1 / packet1.8.0)

Classification: `ClaudeChallengeE10.classification` proves the graph iff for natural p,s>=1 and r>=2, with m=2r+s and p congruent to d+1 or d-1 modulo m for d in {0,r,r+s}. `ClaudeChallengeE10.main` proves actual-path eventual periodicity for every positive natural start and nonnegative natural slope, including r=1. That branch applies formal Theorem1a `ClaudeChallenge2.State.main_statement` after proving `Valid` and `TrianglesInCharts` on the E10 model; it uses no prose geometric bridge. It does not prove a closed r=1 classification. The general prose bridge and the separate r=1 sufficient conditions/converse remain unchanged. Named catalogue correspondence retains its statement-reader caveat.

Both listed E10 declarations, and only those listed E10 targets, share the coordinator's saved six-kernel paranoid Comparator acceptance. This is a receipt readback, not a new run or independent mathematical derivation. Read `e10-manifest.json`, `VERIFICATION-RECORD.md` and `CI-AXIOM-SPLIT.md` for chronology, statement correspondence, axiom-report basis and the O2/D14 tacticPeq import collision. No owner-confirmation procedure, human review or novelty promotion is added. Current total:412 Lean files =407 proof/specification files plus five inert benchmarks. The E10 closure has166 files, including111 new proof/specification files (110 proof + one spec) and55 inherited files; its separate inert challenge has two placeholders. All300 predecessor Lean sources and old payloads retain exact bytes. No current Lean, external-kernel or scientific execution, no upload.

## Inherited checkpoint documentation (through packet1.7.0)

The following earlier edition notes describe historical checkpoints; the current scope and counts are stated above.

Historical checkpoint1.8.0 / article6.1; publication is separate under the author's decision.

# Citation guidance

The article is Tatsuhiko Takimoto, *Eventual periodicity of linear generalized Stone-Wales paths in affine fullerene families with convex lattice-face decompositions*, version 6.3. Use the [PDF](paper-lines-v6.0-en.pdf) or [source](paper-lines-v6.0-en.tex) for mathematics. The artifact packet is version 1.7.0. [CITATION.cff](CITATION.cff) separates the two records: article CC BY 4.0, code/Lean Apache-2.0, as described in [LICENSING.md](LICENSING.md). No DOI, journal acceptance or date-released is invented.

Affiliation: Independent researcher. Contact: GitHub Issues, with the repository URL centralized in [REPOSITORY-URL.txt](REPOSITORY-URL.txt). The owner-approved release sequence is GitHub then Zenodo; journal/arXiv later.

Privacy edition: see [REDACTION-POLICY.md](REDACTION-POLICY.md), [REDACTIONS.md](REDACTIONS.md) and [REDACTIONS.json](REDACTIONS.json). Listed records, including those with `.original.log` filenames, are redacted public derivatives; original private bytes are not bundled. The inherited redaction transformation preserves its article/proof bytes; historical owner-confirmation and publication-state prose edits remain recorded in CHANGELOG.md. Inherited Lean bytes and human proof-review flags are preserved; K3, C1 and O2 proof scopes are inherited; this edition receives D14 main and separately scoped auxiliary lemmas as described in FORMALIZATION.md.

The owner's Theorem 1a version-2 statement-meaning check is recorded in [OWNER-STATEMENT-CHECK.md](OWNER-STATEMENT-CHECK.md) and [owner-statement-confirmation.json](owner-statement-confirmation.json). This does not promote proof review, prose bridge review, K3 or novelty.

## Historical D12 addition, article 6.2 / packet 1.9.0 (its no-Lean statement is superseded by packet 1.10.0)

Positive integer r,s: a literal path exists iff r divides s-1 or s+1, or abs(r-3s)=1. See d12/README.md and the two full proof routes in d12/proof-notes.tex. This classification has two separately derived universal prose/computer-assisted proof routes and NO Lean proof. D12 ray periodicity separately follows from Theorem1a with its prose model correspondence, or conditionally from the arithmetic classification. Earlier 30 claim statuses, 34 Lean declaration references and all412 Lean sources remain unchanged. This is a local candidate; publication of this revision requires a separate author/coordinator decision. The inherited authorization record concerns the earlier release checkpoint and is not a new approval of D12. No Lean, kernel, graph census or upload was run to prepare this revision.
