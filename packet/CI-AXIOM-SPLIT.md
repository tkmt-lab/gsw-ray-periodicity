# Separate axiom-query entry points

O2 and D14 currently export colliding tactic names `peq` / `tacticPeq`. Do not import both proof groups into one axiom-query entry point. Keep the O2-side `Axioms.lean` and D14-side `AxiomsD14.lean` separate. E10 can be imported with either side. This is a query/CI import-layout caveat, not an additional mathematical hypothesis or a failed E10 result. This packet records the existing check; preparation did not run Lean, combine these imports or modify any supplied proof bytes.
