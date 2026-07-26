# PolarEvaluation notes

## 2026-07-18 Haar polar integration

- Added `lintegral_polar_prod` and the Tonelli form `lintegral_polar` for a
  finite-dimensional real normed space with an additive Haar measure.
- The implementation reuses Mathlib's measure-preserving polar homeomorphism;
  it does not introduce a second polar-coordinate measure API.
- Focused verification and the exported module refresh passed.
