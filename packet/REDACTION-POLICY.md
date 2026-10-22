# Public-record redaction policy

Only private execution locations and internal tool/environment names are replaced. Mathematical statements, assumptions, proof source bytes, recorded axioms, outcomes, timing and memory measurements are retained. The current article in this packet is version 6.0. The inherited redactions themselves do not alter article or proof bytes; separate owner-confirmation prose edits are described in CHANGELOG.md.

| Rule | Transformation |
|---|---|
| R01-workdir | Private checkout directory becomes `<WORKDIR>`; relative suffixes remain. |
| R02-tempdir | Individual temporary directory becomes `<TMPDIR>`; relevant suffixes remain. |
| R03-temp-prefix | Internal temporary-name prefix becomes the neutral `review-` prefix. |
| R04-local-tool | Internal wrapper name becomes `local wrapper`. |
| R05-derived-fingerprint | A reference to another redacted record is rebound to that public derivative, while the original record identity is retained in REDACTIONS.json. |

The approved public author identity, affiliation, repository URLs, cited authors and public dependency/tool names are retained. The original private records remain in the custodian's local archive and are **not included** in this packet. Neither the original private strings nor the archive's machine location are disclosed here. Public hashes identify the derived bytes; original hashes identify the prior records. Hashes do not authenticate truth or establish a new kernel execution.

For compatibility some receipt names still end in `.original.log`. **Every record in REDACTIONS.json is a redacted derivative, not the original byte sequence, regardless of its filename.** Unlisted historical receipts remain unchanged. Read the Markdown and JSON correspondence before treating any file as an exact original receipt. The build uses a separate fixed original-hash contract, and the publication check verifies both sides of the correspondence. Reported source commits continue to identify the original proof sources, not this packaging transformation.

The privacy check covers every filename and file's raw/UTF-16 views, plus every historical and current PDF's page text, metadata and deflate streams. It uses Python 3 and locally installed Poppler utilities `pdftotext` and `pdfinfo`; it does not install tools. Generic private path, email, hostname and local-address patterns are rejected by the public check; individual account and internal-name checks were performed separately by the nonpublic internal check. This is a bounded pattern check, not a guarantee that every possible private identifier has been recognized. Approved author-name fields are the narrow documented identity exception. The privacy scanner performs no network, Lean, scientific experiment or publication operation. The current packaging phase inherits the 1.2.0 build receipts; no Lean is run.

The distributed scanner checks only generic path, email, hostname and local-address patterns. Individual private-name checks were performed by a nonpublic internal scanner with an external private table. No private names, their fingerprints or reversible encodings are distributed as a scanner vocabulary. Approved public author fields remain explicit.

The six inherited privacy derivatives remain unchanged. New K3 sources and records are exact copies, with their original identities in k3-manifest.json; they introduce no additional privacy substitutions. K3 proof-scope updates and current article edits are separate from the old redaction-only byte flags.

C1 sources and records are exact pinned copies, with no new privacy substitutions. Their receipt identities are in c1-manifest.json. Current C1 proof-scope/article updates are separate from historical redaction-only byte flags.

O2 sources and records are exact pinned copies, with no new privacy substitutions. Identities are in o2-manifest.json. Current proof-scope/article edits are distinct from historical redaction-only changes.

Packet1.7.0 adds exact D14 proof/receipt copies and article5.0, without new privacy substitutions. Historical derivatives are preserved; D14 scope edits and new PDF are distinct from redaction-only byte identity.

Packet1.7.0 adds article6.0 and VERIFICATION-RECORD.md by editorial separation, without new privacy substitutions. The earlier article5.0 and all inherited proof/evidence payloads retain exact bytes. The inherited paper_bytes_changed=false field refers to privacy transformations, not to the addition of the new article version.

Packet1.8.0 adds exact E10 source/record copies and article6.1 with its current proof-scope edits. No new privacy transformations. Earlier article/proof/evidence bytes preserved; editorial proof-scope edits are distinct from privacy substitutions.

New D12 derivative mappings: d12/derivatives.json; prose identifiers and local paths neutralized, mathematical expressions retained. Earlier records and all Lean source bytes unchanged.

Packet1.10.0 adds exact D12 Lean source/record copies and article6.3 with its current proof-scope edits. No new privacy transformations.
