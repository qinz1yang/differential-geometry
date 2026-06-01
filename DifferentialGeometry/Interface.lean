import DifferentialGeometry.Interface.Sobolev
import DifferentialGeometry.Interface.Curvature
import DifferentialGeometry.Interface.Heat
import DifferentialGeometry.Interface.Parabolic

/-!
# Public consumption-facing facade

A single-file front door to the project's smooth-Riemannian-manifold
PDE and curvature surface. A downstream consumer can `import` this file
and `open DifferentialGeometry.Interface` to obtain, under one
namespace:

- Smooth scalar ↔ Hilbert-completion ↔ L² adapters: `smoothScalarToH1`,
  `smoothScalarToLp`, plus the underlying primitives `H1Compl`,
  `smoothToH1Compl`, `H1ComplToLp`, and their tensor counterparts.
- Smooth Ricci tensor as a pointwise bilinear function `ricciBilinear`,
  together with `ricciBilinear_symm` and the trace identity
  `ricciBilinear_eq_trace_ricciEndo`, plus the bundled section types
  `Tensor02Section`, `Tensor04Section`, `Tensor13Section` and helpers.
- Heat semigroup `e^{t Δ_g}` applied to smooth scalars via `heatFlow`,
  with `heatFlow_zero` and `heatFlow_norm_le` (`t ≥ 0`).
- Duhamel mild solution of the inhomogeneous heat equation via
  `duhamel` and the smooth-initial-datum adapter `duhamelSmoothInitial`,
  with the homogeneous reductions `duhamel_zero_forcing` and
  `duhamelSmoothInitial_zero_forcing`.
-/
