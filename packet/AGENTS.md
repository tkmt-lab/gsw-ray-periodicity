# Read this packet first

This is the release edition; the owner has authorized release (packet 1.3.1, English paper v4.7). Read [README.md](README.md), [SCOPE.md](SCOPE.md), [FORMALIZATION.md](FORMALIZATION.md) and [P006-corrections.md](P006-corrections.md) before using [claims.json](claims.json).

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

Privacy edition: see [REDACTION-POLICY.md](REDACTION-POLICY.md), [REDACTIONS.md](REDACTIONS.md) and [REDACTIONS.json](REDACTIONS.json). Listed records, including those with `.original.log` filenames, are redacted public derivatives; original private bytes are not bundled. The inherited redaction transformation preserves its article/proof bytes; this edition separately updates owner-confirmation prose and the PDF. Inherited Lean bytes and human proof-review flags are preserved; this edition separately receives the K3 formal-proof scope described in FORMALIZATION.md.

The owner's Theorem 1a version-2 statement-meaning check is recorded in [OWNER-STATEMENT-CHECK.md](OWNER-STATEMENT-CHECK.md) and [owner-statement-confirmation.json](owner-statement-confirmation.json). This does not promote proof review, prose bridge review, K3 or novelty.

Release authorization is recorded in [publication-authorization.json](publication-authorization.json). The owner authorized publication; repository/homepage publication is performed separately by the coordinator. This preparation does not perform an upload.

K3 now has received graph necessity/classification and all-positive-ray periodicity, including parameter-one boundaries, without the general prose bridge. The general theorem retains its prose bridge. Read K3-STATEMENT-CHECK.md and k3-manifest.json. The 193 Lean files comprise 192 proof sources and one inert benchmark; no current check executes Lean. All old owner confirmations are historical facts; no K3 owner procedure is used.
