# VariationFieldSmooth

## 2026-08-27: local variation-field smoothness API

- Goal: expose the local smoothness actually needed by Perelman Calabi variations without
  requiring a globally smooth two-parameter variation.
- Native location: the reusable Comparison/Variation layer, next to the existing
  `varField_smooth` theorem.
- Source change: the pointwise core of the old private `velocity_infty` proof is now
  `velocity_smoothAt`. It uses only `ContMDiffAt` of the two-parameter map at the base point;
  the tangent-bundle trivialization neighborhood follows from local continuity.
- Public API: `varField_smoothAt` assumes local smoothness at `(0, t)`, and
  `varField_smoothOn` assumes that pointwise condition for every `t` in the set. The existing
  `varField_smooth` signature is unchanged and now specializes `varField_smoothAt`.
- Verification: the focused file check passed, followed by a successful named module refresh.
- Project scale: this local API task is complete (100%); the downstream Calabi variation
  consumer remains 0% until it imports and verifies the producer. This is a small infrastructure
  step in the broader Perelman reduced-geometry program (well below 1%).
