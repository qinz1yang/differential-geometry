import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionTowerGrid
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.SlotFreeCurvatureOperatorField

/-! # The background-curvature arm coefficient field for the Ricci–DeTurck linearization grid

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g₀)`, this file packages the
**fixed background-curvature endomorphism** of `g₀` as the smooth coefficient field that instantiates
the *proved* differentiated fixed-coefficient metric-contraction grid `fixedCoeffDiffOp`
(`MetricContractionTowerGrid`) for the **order-`0` (curvature) arm** of the mean-value linearization of
the nonlinear Ricci–DeTurck right-hand side.

## Why curvature is the order-`0` arm (not the inverse-Gram difference)

The order-`0` (value-level) symbol of the Lichnerowicz–DeTurck linearization of `−2 Ric(g) + 𝓛_W g` in
the metric is the classical **curvature action** on the perturbation `S`: the contraction of the FIXED
background curvature `2`-jet of `g₀` with `S` (the `2 Rm₀·S − Ric₀·S − S·Ric₀` Lichnerowicz term plus
the DeTurck Christoffel-difference algebraic terms).  It is *zeroth order* in `S` and vanishes on flat
backgrounds.  The inverse-metric-difference multiplier `(g₁⁻¹ − g₀⁻¹)·∂²S` is, by contrast, the
*principal* (order-`2`) symbol of the parabolic Laplacian — it multiplies `∇²S`, not `S` — and so it
belongs to the order-`2` arm (`gInvDiffMetricArmCoeffField`), never the order-`0` arm.

This file supplies the order-`0` curvature coefficient as a single FIXED `g₀`-built smooth
`(2, 2)`-operator field, exactly mirroring `gInvDiffSlotCoeff` / `gInvDiffMetricArmCoeffField`'s
packaging but with the raised background-Ricci endomorphism `ricEndoRaisedFib g₀` (`RicciTraceCarrier`)
in the leading slot.  The Lichnerowicz / Christoffel-difference algebraic refinement of the order-`0`
symbol is a fixed-`g₀` curvature contraction of the same `(2, 2)`-operator shape; the genuine *matching*
of `N`'s order-`0` part with this coefficient is the deep mean-value content posited downstream.  The
single point of this file is that the order-`0` coefficient is a fixed smooth `g₀`-built field whose
`fixedCoeffDiffOp` grid is the proven (coefficient-agnostic) metric-contraction grid.

## The coefficient field

* `ricBackgroundSlotCoeff g₀` — the rank-`2` `(2, 2)`-operator field whose fibre value at `x` is the
  leading-slot insertion `slotInsertEndoFib 2 0 x (ricEndoRaisedFib g₀ x)` of the fixed raised
  background-Ricci endomorphism; smooth by `slotInsertEndoFib_contMDiff` on `ricEndoRaisedFib_contMDiff`,
  compactly supported on the closed manifold.
* `ricBackgroundArmCoeffField g₀` — the per-rank coefficient field `Φ₀` (the background-curvature
  slot-insertion operator at rank `2`, the zero operator elsewhere).
* `ricBackgroundArm_iteratedCovGrad_singleSum_le` — the curvature-arm Moser-tame `rfns` grid obtained
  by instantiating `fixedCoeffDiffOp_iteratedCovGrad_singleSum_le` at
  `Φ₀ = ricBackgroundArmCoeffField`, base rank `2`:
  ```
  rfns(∇^a (op 0 2 W))(x) ≤ C 2 a · ∑_{q ≤ a} rfns(∇^q W)(x).
  ```
  This is the chart-jet-free order-`0` curvature arm the Ricci–DeTurck linearization grid assembles on;
  the background-curvature coefficient's `C⁰` envelope rides inside the engine constant `C 2 a` (through
  `kappa`), exactly as the inverse-Gram coefficient's envelope rides inside the order-`2` arm's constant.
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

/-! ## The background-curvature arm coefficient field -/

set_option backward.isDefEq.respectTransparency false in
/-- **The rank-`2` `(2, 2)`-operator field of the fixed background-curvature endomorphism.**  The fixed
smooth `(2, 2)`-tensor whose fibre value at `x` is the leading-slot insertion
`slotInsertEndoFib 2 0 x (ricEndoRaisedFib g₀ x)` of the raised background-Ricci endomorphism of `g₀`
(an endomorphism of `(0, 2)`-tensors), packaged through `TensorRSSpace.ofCLM` with base-point smoothness
`slotInsertEndoFib_contMDiff` on `ricEndoRaisedFib_contMDiff`; compactly supported on the closed
manifold.  It is a fixed `g₀`-built field (it contracts the FIXED background curvature `2`-jet with the
perturbation), vanishing on Ricci-flat backgrounds. -/
def ricBackgroundSlotCoeff (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        TensorRSSpace.ofCLM
          (slotInsertEndoFib (I := I) (M := M) 2 0 x (ricEndoRaisedFib (I := I) g₀ x))
      contMDiff_toFun :=
        slotInsertEndoFib_contMDiff (I := I) (M := M) g₀ 2 0
          (fun x : M => ricEndoRaisedFib (I := I) g₀ x)
          (ricEndoRaisedFib_contMDiff (I := I) g₀) }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
/-- **The background-curvature arm coefficient field `Φ₀`.**  The per-rank `(r, r)`-operator coefficient
field that instantiates `fixedCoeffDiffOp` for the order-`0` (curvature) arm of the Ricci–DeTurck
linearization: the background-curvature slot-insertion operator `ricBackgroundSlotCoeff` at rank `2`, the
zero operator at every other rank.  Only the rank-`2` arm contracts the order-`0` perturbation difference
`T − T'`. -/
def ricBackgroundArmCoeffField (g₀ : SmoothRiemannianMetric I M) :
    ∀ r : ℕ, SmoothCcTensor g₀ (r + 0) (r + 0) :=
  fun r => match r with
    | 2 => ricBackgroundSlotCoeff (I := I) g₀
    | _ => 0

/-! ## The curvature-arm Moser-tame `rfns` grid -/

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- **The curvature-arm Moser-tame `rfns` grid for the Ricci–DeTurck order-`0` background-curvature
arm.**  The instantiation of `fixedCoeffDiffOp_iteratedCovGrad_singleSum_le` at
`Φ₀ = ricBackgroundArmCoeffField` and base rank `2`: at every base point `x₀`, gradient order `a`, and
order-`2` section `W`, the intrinsic squared Riemannian fibre norm of the `a`-th iterated covariant
gradient of the order-`0` curvature contraction `op 0 2 W` is bounded by a single nonnegative per-order
constant `C 2 a := 4^a · gridWindowSum (fixedCoeffDiffOp Φ₀).kappa 0 2 a` times the order-`≤ a` covariant
jet of `W`:
```
rfns(∇^a (op 0 2 W))(x₀) ≤ C 2 a · ∑_{q ≤ a} rfns(∇^q W)(x₀).
```
The background-curvature coefficient's `C⁰` envelope rides inside `C 2 a` (through `kappa`), exactly as
the inverse-Gram coefficient's envelope rides inside the order-`2` arm's constant. -/
theorem ricBackgroundArm_iteratedCovGrad_singleSum_le
    (g₀ : SmoothRiemannianMetric I M) (x₀ : M) (W : SmoothCcTensor g₀ 0 2) (a : ℕ) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + a) x₀
        ((iteratedCovGrad g₀ 0 2 a
          ((fixedCoeffDiffOp (I := I) (M := M) g₀
            (ricBackgroundArmCoeffField (I := I) g₀)).op 0 2 W)).toSection x₀) ≤
      ((4 : ℝ) ^ a * gridWindowSum
          (fixedCoeffDiffOp (I := I) (M := M) g₀
            (ricBackgroundArmCoeffField (I := I) g₀)).kappa 0 2 a) *
        ∑ q ∈ Finset.range (a + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + q) x₀
            ((iteratedCovGrad g₀ 0 2 q W).toSection x₀) :=
  fixedCoeffDiffOp_iteratedCovGrad_singleSum_le (I := I) (M := M) g₀
    (ricBackgroundArmCoeffField (I := I) g₀) x₀ 2 W a

end Connection
end Integral
end DifferentialGeometry

end
