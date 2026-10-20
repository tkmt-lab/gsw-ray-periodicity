# Public redacted record correspondence

See [REDACTION-POLICY.md](REDACTION-POLICY.md) for the fixed rules and original/derivative distinction. The original bytes are not bundled; only their hashes and sizes are supplied. Every listed file is a public derivative even when its name retains `.original.log`.

| Public file | Original SHA-256 | Public SHA-256 | Original bytes | Public bytes | Rules |
|---|---|---|---:|---:|---|
| evidence/R004/R004-report-005.md.txt.original.log | 863017a492bd2baab9083da35fefaf6f406ef9d5b0fc96eb48a951cb925db360 | 9283345b0b4667732e37c33cd3004cef93159e0b74d1418057efd19199d9ff98 | 5893 | 5893 | R04-local-tool |
| evidence/theorem1a/lean-execution.json | c0cf38c92b36638aa663846db89f798cd5fd9cf3496e7f25c62541e192c412fe | df2b54fb61c506259c738ac24343e1bdaed38014861a8caa0f982f080cc0871e | 18896 | 18847 | R01-workdir |
| evidence/theorem1a/serial-build-output.original.log | 35d804c710d761515a8a5dcf6952457548fc8695f83dcd7bebb1dfc450646eca | 2fda6e38b31e01befb5537d70dc6a9b0c3338e7e57405f0117e02022c4362af2 | 216999 | 216950 | R01-workdir |
| evidence/theorem1a/thm1a-final-report-2026-10-20.md.original.log | d85a2443f811786d1fe523dc1d90498c81e19782f921df259da38251218bc22c | 3d7e536205cc255505f2d609d1a4774487bb35eaf603fd323606cc6d67b81bdd | 13420 | 13318 | R02-tempdir |
| evidence/theorem1a/thm1a-geo-report-2026-10-20.md.original.log | e86b1fcd3d41fab0b26084e82e9a1247d0becb277961d9335ec7cd021834d397 | 4f83f11f5b7875c793591f2fa60d094d4912345a3dddab6431974aeddf7b1b8f | 10053 | 9951 | R02-tempdir |
| evidence/theorem1a/thm1a-state-report-2026-10-20.md.original.log | 91b8498a4e9d9201ff64c60102bad7ea1bc21719c4bb366e391d339375427993 | b4938bdb6a6651dc10877079b9a3f0761386480f36907993869f18aa0a947539 | 18364 | 18262 | R02-tempdir |

Packet 1.2.0 inherits these same six public derivatives and original-hash bindings. The new owner-confirmation records have no private-name/path replacements; the separate article v4.4 prose change is not a redaction.

This edition also removes the old individual-identifier scanner vocabulary. Private-name checks were performed internally; the public scanner contains generic patterns only. Existing historical record transformations in the table above are unchanged.
