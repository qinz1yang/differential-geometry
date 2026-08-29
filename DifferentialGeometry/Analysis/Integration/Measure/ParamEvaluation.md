# ParamEvaluation

## 2026-08-26: weighted parametrization integral

- Added `riemVol_param_lint`, the generic change-of-variables formula for an
  arbitrary function `F : M → ℝ≥0∞` over a measurable set `B` contained in a
  partial parametrization source. No measurability hypothesis on `F` is needed.
- The proof uses a private measurable embedding of the subtype `B` and a
  private pushforward identity from the density-weighted model measure to the
  Riemannian volume measure restricted to `Ψ '' B`.
- The implementation reuses the existing parametrized-image volume formula,
  continuity of `paramDensity`, subtype `comap`/`map` measure identities, and
  the non-measurable-function `withDensity` lintegral theorem. No new
  assumptions, axioms, or proof placeholders were introduced.
- Focused verification passed without warnings. There is no known blocker.

Progress accounting:

- `riemVol_param_lint`: **100%** (stated, proved, and focused-check verified).
- Dedicated generic weighted-parametrization machinery in this module:
  **100%** for the requested interface.
- The downstream capstone `redVolume_anti`: **0%**; this module does not state
  or prove it. The current project plan keeps dedicated compact ordinary-flow
  L-geometry machinery at about **99%**, P2 below **1%**, and the whole
  Poincare program at approximately **3--5%**.
