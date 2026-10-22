# Separate axiom-query entry points

O2 and D14 currently export colliding tactic names `peq` / `tacticPeq`. Do not import both proof groups into one axiom-query entry point. Keep the O2-side `Axioms.lean` and D14-side `AxiomsD14.lean` separate. E10 can be imported with either side. This is a query/CI import-layout caveat, not an additional mathematical hypothesis or a failed E10 result. This packet records the existing check; preparation did not run Lean, combine these imports or modify any supplied proof bytes.

D12 (packet 1.10.0): the D12 proof defines the helper tactics `d12om`, `d12peq`, `d12peq2` and `d12glue_tac`, none of which collides with the O2/D14 `peq`. The worker imported the D12 solution together with the O2 solution, and separately with the D14 solution, and queried axioms in both layouts. The public CI adds `ClaudeChallengeD12.classification` and `ClaudeChallengeD12.main` to the O2-side `Axioms.lean`; `AxiomsD14.lean` is unchanged. Packaging ran no Lean.
