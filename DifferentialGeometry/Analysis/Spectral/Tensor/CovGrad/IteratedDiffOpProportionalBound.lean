import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.MetricContractionLeibnizGrid
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.UniformProportionalCurvatureSup
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldEvaluationLeibniz

/-! # Combining the order-`0` and high-order proportional fibre bounds for a curvature-operator tower

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled on a real
inner-product space `E`, this file isolates the single genuinely-*abstract* (and sorry-free) step shared
by the two recursively-differentiated *curvature*-operator families in the library — the frame-free
pure-Riemann trace tower `pureRGenuineDiffOp`
(`Geometry/Curvature/CovGradRoughLap/FrozenFramePureRCurvatureTower`) and the metric
curvature-contraction tower `diffCurvOp` (`CurvatureContractionLeibnizGridConstruction`) — namely the
**combination** of a tower's order-`0` section-proportional fibre bound with its high-order
(`p ≥ 1`) section-proportional fibre envelope into a single per-order, per-rank family.

## Why the deep content is per-tower, not abstract

For a recursive covariant-Leibniz-remainder operator family `op` with
```
op (p+1) r W = ∇(op p r W) − (rank-cast) op p (r+1) (∇W),
```
the order-`0` base `op 0 r W (x) = L₀ x (W (x))` is a smooth *fibrewise* curvature operator (the
`IsOrderZeroCurvFactor` fingerprint of `OperatorFieldEvaluationLeibniz`), and the genuine analytic
content is the **high-order layer**: the iterated curvature coefficient `∇ᵖ L₀ = ∇ᵖ(g, R)` is again a
smooth fibrewise operator, uniformly fibre-operator-bounded on the compact `M` by `‖∇^{≤ p} R‖_∞`, so
`op (p+1) r` is itself a section-proportional fibrewise operator
(`rfns(op (p+1) r W)(x) ≤ kappaHigh p r · rfns(W)(x)`).

An earlier design tried to make this high-order boundedness an *abstract* node — derivable from the
order-`0` fingerprint plus the Leibniz remainder identity alone. **That is false** (refuted at
`(p, r) = (1, 0)`): the order-`0` fingerprint constrains `op 0 r` only per-rank, with no inter-rank
coherence, while the recursion mixes ranks, so a value-local-at-order-`0` family can produce a
*one-jet-reading* (hence unbounded) order-`1` operator — see the deleted
`op_perOrder_factorisation_continuous` in `OperatorFieldEvaluationLeibniz` for the explicit
counterexample (`op 0 0 := 0`, `op 0 1 := id`). The high-order boundedness genuinely needs the smooth
`L₀ = g, R` coefficient, available only to the concrete towers; each tower therefore carries its own
posited high-order envelope (`exists_proportional_pureRGenuineDiffOp_highOrder`,
`exists_proportional_diffCurvOp_highOrder`), and consumers transitively depend on `sorryAx` through those
per-tower nodes alone.

## What is abstract and proved here

* `exists_proportional_recCurvDiffOp` (**proved, sorry-free**) — the abstract combination, in **jet**
  form: given a tower's order-`0` proportional fibre bound `hbase0`
  (`rfns(op 0 r W)(x) ≤ kappa0 r · rfns(W)(x)`, the value form — the order-`0` operator is value-local)
  and its high-order proportional fibre **jet** envelope `hhigh`
  (`rfns(op (p+1) r W)(x) ≤ kappaHigh p r · ∑_{q < p + 2} rfns(∇^q W)(x)`), the single per-order,
  per-rank jet family `rfns(op p r W)(x) ≤ kappa p r · ∑_{q < p + 1} rfns(∇^q W)(x)` (order `0` from
  `hbase0`, where the jet window `q < 1` carries only the value; order `p ≥ 1` from `hhigh`).  The jet
  shape is forced because the single-value high-order form is FALSE at the rank-`0`-degenerate base
  (`op 1 0 W = −cast(op 0 1 (∇W))` reads `∇W`); see `MetricContractionLeibnizGrid.DiffBilinOp`.  This is
  pure case-bookkeeping on the order `p`; it introduces no `sorry` and uses no curvature structure
  beyond the two supplied bounds.

The iterated-gradient grid that each tower needs on top of its per-order family is the genuinely-abstract
*and proved* binomial covariant-Leibniz engine `DiffBilinOp.rfns_iteratedCovGrad_grid_at`
(`MetricContractionLeibnizGrid`), consumed directly by the towers; it requires no further posit.
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

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]
variable [CompleteSpace E]

set_option linter.unusedSectionVars false in
/-- **The combined all-order section-proportional fibre envelope for a recursively-differentiated
bundled curvature operator, from its order-`0` and high-order bounds, in JET form** (proved,
sorry-free). Combining a tower's supplied order-`0` proportional fibre bound `hbase0` (value form) with
its supplied high-order (`p ≥ 1`) proportional fibre **jet** envelope `hhigh`, there is a single
nonnegative per-order, per-rank jet envelope `kappa : ℕ → ℕ → ℝ` with
```
rfns(op p r W)(x) ≤ kappa p r · ∑_{q < p + 1} rfns(∇^q W)(x)
```
at every order `p`, rank `r`, section `W` and point `x`. The order-`0` layer is `hbase0` (the
fully-proven curvature-operator order-`0` bound; its jet window `q < 1` carries only the value
`∇^0 W = W`); the order-`p ≥ 1` layer is `hhigh` (each concrete tower's posited high-order jet
envelope, window `q < (p' + 1) + 1`, where the deep `‖∇^{≤ p} R‖_∞`-content lives). The jet shape is
forced because the single-value high-order form is FALSE at the rank-`0`-degenerate base. This step is
pure case-bookkeeping on the order `p`: it introduces no `sorry` and uses no curvature structure beyond
the two supplied bounds. Consumers transitively depend on `sorryAx` only through the per-tower
high-order node supplied as `hhigh`. -/
theorem exists_proportional_recCurvDiffOp
    (g : SmoothRiemannianMetric I M)
    (op : ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p))
    (kappa0 : ℕ → ℝ) (hkappa0_nn : ∀ r, 0 ≤ kappa0 r)
    (hbase0 : ∀ (r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + 0) x ((op 0 r W).toSection x) ≤
        kappa0 r * riemannianFiberNormSq (I := I) (M := M) g 0 r x (W.toSection x))
    (kappaHigh : ℕ → ℕ → ℝ) (hkappaHigh_nn : ∀ p r, 0 ≤ kappaHigh p r)
    (hhigh : ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 (r + (p + 1)) x
          ((op (p + 1) r W).toSection x) ≤
        kappaHigh p r * ∑ q ∈ Finset.range (p + 2),
          riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
            ((iteratedCovGrad g 0 r q W).toSection x)) :
    ∃ kappa : ℕ → ℕ → ℝ, (∀ p r, 0 ≤ kappa p r) ∧
      ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x ((op p r W).toSection x) ≤
          kappa p r * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  classical
  refine ⟨fun p r => match p with | 0 => kappa0 r | (p' + 1) => kappaHigh p' r,
    fun p r => ?_, fun p r W x => ?_⟩
  · cases p with
    | zero => exact hkappa0_nn r
    | succ p' => exact hkappaHigh_nn p' r
  · cases p with
    | zero =>
        rw [show (fun p r => match p with
            | 0 => kappa0 r | (p' + 1) => kappaHigh p' r) 0 r = kappa0 r from rfl]

        rw [Finset.sum_range_one]
        exact hbase0 r W x
    | succ p' =>
        rw [show (fun p r => match p with
            | 0 => kappa0 r | (p'' + 1) => kappaHigh p'' r) (p' + 1) r = kappaHigh p' r from rfl]

        rw [show (p' + 1) + 1 = p' + 2 from rfl]
        exact hhigh p' r W x

end Connection
end Integral
end DifferentialGeometry

end
