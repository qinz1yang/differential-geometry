# Carrier metric and curvature bounds

Compactness of the fixed reference unit tangent bundle, together with carrier
continuity, bounds both the quadratic form and its reciprocal. Homogeneity
then gives the actual two-sided metric comparison. Curvature continuity is
used in a fixed reference norm before the native tensor comparison transfers
the bound to the moving metric.

These are zero-order bounds. They do not imply spatial derivative continuity.

Elaboration finding: give the composition of normSq0S_total_cont with the
carrier tensor continuity no expected type, then normalize Function.comp_apply
when evaluating the resulting bound. Giving the expanded scalar function as
the expected type caused a deterministic whnf timeout even at800000 heartbeats;
the inferred composition checks at the default200000 limit in about20s.

Verified 2026-09-09: focused7 EMPTY (20.67s), named1 clean (23.42s),
fresh two-public audit1 standard-only (17.47s). External receipts are in
E:/lean-tools/chapter25-terminal-local-20260909/.
