# FamilyDecomposition notes

## 2026-07-17: integrable chart-sum identity

- Added `chart_sum_integral`, which rewrites the global integral of an
  integrable real-valued function as the finite sum of its POU-weighted
  chart-local integrals.
- The proof uses the existing finite measure decomposition and the
  `withDensity` integral formula; it adds no regularity assumption to the
  consumer.
- Focused verification and the targeted module refresh passed.
- For the Noncollapsing Lipschitz weak-gradient lane this producer is complete;
  the final weak-gradient theorem itself remains separate and was not completed
  by this file.
