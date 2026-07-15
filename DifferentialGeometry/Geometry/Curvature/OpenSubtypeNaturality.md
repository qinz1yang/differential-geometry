# OpenSubtypeNaturality

## 2026-06-21

This file contains reusable open-subtype locality lemmas for metric connection
expressions.

What is verified:

- `extDerivFun_restrictOpen` proves scalar directional derivatives are unchanged
  after restricting to an open subtype.  The proof uses the open-subtype
  inclusion derivative as the identity on tangent fibers.
- `restrictOpenTangentField` and `restrictOpenTangentSection` package ambient
  tangent fields and smooth tangent sections as fields/sections on the open
  subtype.
- `mlieBracket_restrictOpen` proves Lie brackets commute with restricting
  ambient smooth tangent sections to an open subtype.
- `koszulScalar_restrictOpen` transfers the Koszul scalar across restriction.
- `metricCov_restrictOpen_apply_section` proves the Levi-Civita restriction
  identity for restricted ambient smooth sections.
- `metricCov_restrictOpen_globalSection` removes the smooth-section direction
  hypothesis by globalizing the point direction.

Verification passed.  The connection restriction endpoint is axiom-clean with
only the standard `[propext, Classical.choice, Quot.sound]` dependencies.
