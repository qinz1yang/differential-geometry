# RicciDiffAffine

## 2026-07-14 family-uniform Ricci estimate

`chartRicci_pou_lip` proves that a pointwise metric-equivalent family with
uniform first and second chart Gram partial bounds has one Ricci-component
Lipschitz constant on every active partition-of-unity chart support.  The
constant controls the Ricci difference by `chartMetricJet2DiffSup` and is
independent of both family indices.

Focused and targeted verification passed.  This closes the Ricci half of the
low-regularity RHS coefficient estimate, not Ricci--DeTurck existence.
