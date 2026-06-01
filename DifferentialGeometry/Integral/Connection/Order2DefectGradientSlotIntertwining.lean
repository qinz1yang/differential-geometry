import DifferentialGeometry.Integral.Connection.Order2DefectGradientSlotLeibniz
import DifferentialGeometry.Integral.Connection.CovGradParallelNaturality

/-!
# The gradient-slot parallel naturality of the covariant-gradient bundle equivalence

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product space `E`, the
section-level covariant gradient `covGrad g 0 s` raises the tensor rank `(0, s) ↦ (0, s + 1)`,
currying the new tangent-direction slot as the *leftmost* (gradient) covariant slot. Concretely it
is the fibrewise covariant-gradient bundle equivalence `covGradBundleEquiv 0 s x` applied to the
directional covariant derivative.

This file records the **single-step gradient-slot parallel naturality** of `covGradBundleEquiv 0 2`:
the slot-`0` curry of the unit-`(0, 0)`-evaluation of the `(0, 3)`-tensor
`covGradBundleEquiv 0 2 x (∇^{(0,2)RS}_v σ)` — i.e. the `(0, 3)`-tensor gradient of a smooth
`(0, 2)`-tensor section `σ`, read along the gradient direction `v` — is the abstract `(0, 2)`-tensor
covariant derivative of the unit-evaluated section `y ↦ σ y (unit)`:
```
tensor0S_curry 2 x ((covGradBundleEquiv 0 2 x (∇^{(0,2)RS}_v σ))(unit)) v
  = ∇^{(0,2)abs}_v (y ↦ σ y (unit)) (x).
```
The unit `(0, 0)`-section is `∇`-parallel, so the product rule against it has no correction term;
the gradient slot is read off the leftmost slot by the curry, and the bundle equivalence transports
the directional derivative without curvature. This is the tensor analogue of
`cotangentCov_metricDuality` on the leftmost (gradient) slot, expressed through the parallel unit
`(0, 0)`-evaluation.

The naturality is the keystone single covariant-differentiation identity from which the diagonal
second-order gradient-slot intertwining (and the resulting off-diagonal Riemann curvature reorder of
the canonical order-`2` Gårding defect `covGradRoughLapCurv g T₀`) is assembled.

## Convention

Geometer convention `Δ_∇ = ∑ᵢ ∇²_{Bᵢ, Bᵢ}` (frame trace). The covariant gradient `covGrad g 0 s`
curries the new tangent-direction slot as the leftmost covariant slot. All operators are the
intrinsic Levi-Civita-induced tensor covariant derivatives.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter Tensor0SBundle CovariantDerivative
open scoped Manifold Topology ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Tensor0SNabla
open TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **The slot-`0` curry reads the directional derivative off the gradient slot.** For any
continuous-linear map `Φ : TangentSpace I x →L[ℝ] TensorRSSpace 0 2 I x`, the slot-`0` curry of the
unit-`(0, 0)`-evaluation of the `(0, 3)`-tensor `covGradBundleEquiv 0 2 x Φ`, taken along `v`, is the
unit-`(0, 0)`-evaluation of `Φ v`:
```
tensor0S_curry 2 x ((covGradBundleEquiv 0 2 x Φ)(unit)) v = (Φ v)(unit).
```
The curry reads the tangent direction `v` off the leftmost (gradient) slot, exactly the slot
`covGradBundleEquiv` places the tangent input on. -/
theorem tensor0S_curry_covGradBundleEquiv_unit
    (x : M) (Φ : TangentSpace I x →L[ℝ] TensorRSSpace 0 2 I x)
    (v : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          covGradBundleEquiv (I := I) (M := M) 0 2 x Φ)
          (unitZeroSec (I := I) (M := M) x)) v =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from Φ v)
        (unitZeroSec (I := I) (M := M) x) := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro u
  rw [show Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) 2 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            covGradBundleEquiv (I := I) (M := M) 0 2 x Φ)
            (unitZeroSec (I := I) (M := M) x)) v) u =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          covGradBundleEquiv (I := I) (M := M) 0 2 x Φ)
          (unitZeroSec (I := I) (M := M) x))
        (Fin.cons v u) from
    (TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 2) (b := x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        covGradBundleEquiv (I := I) (M := M) 0 2 x Φ)
        (unitZeroSec (I := I) (M := M) x)) v u)]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) 0 2 x Φ
    (unitZeroSec (I := I) (M := M) x) (Fin.cons v u)]
  have hzero : (Fin.cons v u : Fin 3 → TangentSpace I x) 0 = v := by rw [Fin.cons_zero]
  have htail : Matrix.vecTail (Fin.cons v u : Fin 3 → TangentSpace I x) = u := by
    funext k; rw [Matrix.vecTail, Function.comp_apply, Fin.cons_succ]
  rw [hzero, htail]

/-- **Gradient-slot parallel naturality (unit-evaluated slot-`0` form).** For a smooth `Cₛ^∞`
`(0, 2)`-tensor section `σ`, the slot-`0` curry of the unit-`(0, 0)`-evaluation of the `(0, 3)`-tensor
`covGradBundleEquiv 0 2 x (∇^{(0,2)RS}_·σ(x))` — the `(0, 3)`-tensor gradient of `σ` — read along the
gradient direction `v`, equals the abstract `(0, 2)`-tensor covariant derivative of the unit-evaluated
section `y ↦ σ y (unit)`:
```
tensor0S_curry 2 x ((covGradBundleEquiv 0 2 x (∇^{(0,2)RS}_·σ(x)))(unit)) v
  = ∇^{(0,2)abs}_v (y ↦ σ y (unit)) (x).
```
The slot-`0` curry reads `v` off the gradient slot (`tensor0S_curry_covGradBundleEquiv_unit`), giving
the unit-evaluation of `∇^{(0,2)RS}_v σ`, which transports — with no correction term, the unit
`(0, 0)`-section being `∇`-parallel — to the abstract `(0, 2)` covariant derivative of `y ↦ σ y (unit)`
(`tensorRSCovariantDerivative_zeroS_unit_eval` at `s = 2`). This is the keystone single-step
gradient-slot intertwining: the `(0, 3)`-bundle gradient slot is parallel-transported, the abstract
`(0, 2)` covariant derivative on the unit-evaluated section carries the remaining content. -/
theorem covGradBundleEquiv_tensorCov_unit_curry_eq_abstractCovDeriv
    (g : SmoothRiemannianMetric I M)
    (σ : Cₛ^∞⟮I; TensorRSModel 0 2 ℝ E, (fun y : M => TensorRSSpace 0 2 I y)⟯)
    (x : M) (v : TangentSpace I x) :
    tensor0S_curry (I := I) (M := M) 2 x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
          covGradBundleEquiv (I := I) (M := M) 0 2 x
            (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g)
              (fun y : M => σ y) x))
          (unitZeroSec (I := I) (M := M) x)) v =
      Tensor0SNabla.tensor0SCovariantDerivative I M 2 (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from σ y)
            (unitZeroSec (I := I) (M := M) y))
        x v := by
  rw [tensor0S_curry_covGradBundleEquiv_unit (I := I) (M := M) x
    (tensorRSCovariantDerivative I M 0 2 (LeviCivita (I := I) g) (fun y : M => σ y) x) v]
  exact tensorRSCovariantDerivative_zeroS_unit_eval (I := I) (M := M) g 2 σ x v

end Connection
end Integral
end DifferentialGeometry

end
