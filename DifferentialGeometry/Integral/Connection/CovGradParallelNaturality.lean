import DifferentialGeometry.Integral.Connection.TensorThirdOrderWeitzenbock
import DifferentialGeometry.Integral.Connection.TensorConnLapSecondGradientL2Bound

/-!
# The covariant-gradient bundle equivalence is parallel: the order-`3`/order-`2` bridge

For a closed smooth Riemannian manifold `(M, g)` modelled on a real inner-product
space `E`, the section-level covariant gradient `covGrad g 0 2 T₀` of a smooth
compactly-supported `(0, 2)`-tensor field `T₀` is, fibrewise, the
covariant-gradient bundle equivalence `covGradBundleEquiv 0 2 x` applied to the
directional covariant derivative `∇^{(0,2)} T₀` (an element of the
covariant-gradient bundle fibre `TM →L T^{(0,2)}`).

This file establishes the *naturality* of that construction under one further
covariant differentiation: differentiating `covGrad g 0 2 T₀` along a tangent
direction and reading the result off the leftmost (gradient) slot recovers the
twice-applied covariant derivative of `T₀`. The mechanism is the same as the
metric index-lowering intertwining of `TensorLoweringParallel.lean`: at upper
rank `r = 0`, the value of an `(0, s + 1)`-tensor covariant derivative is
recovered by evaluating against the constant unit `(0, 0)`-tensor, which is
`∇`-parallel; the product rule `tensorRSCovariantDerivative_apply` then reduces
the directional covariant derivative of `covGrad g 0 2 T₀` to a `(0, 3)`-tensor
covariant derivative of the unit-evaluated gradient section.

## Main results

* `covGrad_apply_unit_eval` — the value of `(covGrad g 0 2 T₀)(y)` at the unit
  `(0, 0)`-tensor, evaluated on a `Fin 3`-tuple `(v 0, v 1, v 2)`, reads the
  tangent direction off the leftmost slot: it is the directional covariant
  derivative `∇^{(0,2)}_{v 0} T₀` evaluated on the tail `(v 1, v 2)`.

* `covGrad_covDeriv_at_unit_eq` — the directional `(0, 3)`-tensor covariant
  derivative of `covGrad g 0 2 T₀`, applied to the unit `(0, 0)`-tensor, equals
  the `(0, 3)`-tensor covariant derivative of the unit-evaluated gradient
  section `y ↦ (covGrad g 0 2 T₀)(y)(unit)`. This is the parallel-transport step:
  the unit `(0, 0)`-section is `∇`-parallel, so the product rule has no
  correction term.

## Sign / convention

Geometer convention `Δ_∇ = div ∘ grad` for the rough Laplacian, matching
`TensorThirdOrderWeitzenbock.lean` and `TensorConnLaplacian.lean`. The covariant
gradient `covGrad g 0 s` curries the new (tangent-direction) slot as the leftmost
covariant slot, the convention produced by the directional covariant derivative.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

/-- The constant unit `(0, 0)`-tensor `ofModel (constOfIsEmpty 1)` as a smooth
section of the `(0, 0)`-tensor bundle. Its scalar function is the constant `1`,
so it is `∇`-parallel: this is the parallel-transport input. -/
noncomputable def unitZeroSec :
    Cₛ^∞⟮I; Tensor0SModel 0 ℝ E, (fun y : M => Tensor0SSpace 0 I y)⟯ :=
  ⟨fun _ : M => Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)),
    contMDiff_unitZeroSection (I := I) (M := M)⟩

@[simp] lemma unitZeroSec_apply (y : M) :
    unitZeroSec (I := I) (M := M) y =
      Tensor0SSpace.ofModel
        (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ)) := rfl

/-- **Unit-evaluation of the covariant gradient.** Evaluating the
`(0, 3)`-tensor `(covGrad g 0 2 T₀)(y)` at the unit `(0, 0)`-tensor and on a
`Fin 3`-tuple `v` recovers the directional covariant derivative
`tensorCovDerivAt g 0 2 T₀ y (v 0)` (an element of `T^{(0,2)}_y`) applied to the
unit `(0, 0)`-tensor and evaluated on the tail `(v 1, v 2)`. The tangent
direction is read off the leftmost (gradient) slot. -/
lemma covGrad_apply_unit_eval
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2) (y : M)
    (v : Fin 3 → TangentSpace I y) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
          (covGrad (I := I) (M := M) g 0 2 T₀).toSection y)
          (unitZeroSec (I := I) (M := M) y)) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 2 I y from
          tensorCovDerivAt (I := I) (M := M) g 0 2 T₀ y (v 0))
          (unitZeroSec (I := I) (M := M) y))
        (Matrix.vecTail v) := by
  exact covGrad_toSection_apply_eval (I := I) (M := M) g 0 2 T₀ y
    (unitZeroSec (I := I) (M := M) y) v

/-- **Parallel-transport reduction.** The directional `(0, 3)`-tensor covariant
derivative of `covGrad g 0 2 T₀` along `v`, applied to the unit `(0, 0)`-tensor,
equals the `(0, 3)`-tensor covariant derivative
`tensor0SCovariantDerivative I M 3 (LeviCivita g)` of the unit-evaluated gradient
section `y ↦ (covGrad g 0 2 T₀)(y)(unit)`.

The proof applies the product rule `tensorRSCovariantDerivative_apply` with the
constant unit `(0, 0)`-section, whose covariant derivative vanishes
(`tensor0SCovariantDerivative_unitZero_eq_zero`), so no correction term
survives. -/
lemma covGrad_covDeriv_at_unit_eq
    (g : SmoothRiemannianMetric I M) (T₀ : SmoothCcTensor g 0 2)
    (x : M) (v : TangentSpace I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        tensorRSCovariantDerivative I M 0 3 (LeviCivita (I := I) g)
          (fun y : M => (covGrad (I := I) (M := M) g 0 2 T₀).toSection y) x v)
        (unitZeroSec (I := I) (M := M) x) =
      Tensor0SNabla.tensor0SCovariantDerivative I M 3 (LeviCivita (I := I) g)
        (fun y : M =>
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace 3 I y from
            (covGrad (I := I) (M := M) g 0 2 T₀).toSection y)
            (unitZeroSec (I := I) (M := M) y))
        x v := by
  classical
  rw [tensorRSCovariantDerivative_apply (I := I) (M := M) 0 3
    (LeviCivita (I := I) g) (covGrad (I := I) (M := M) g 0 2 T₀).toSection
    (unitZeroSec (I := I) (M := M)) x v]
  rw [show (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g)
        (fun y : M => unitZeroSec (I := I) (M := M) y) x v) = 0 from
    tensor0SCovariantDerivative_unitZero_eq_zero (I := I) (M := M)
      (LeviCivita (I := I) g) x v]
  rw [map_zero, sub_zero]

end Connection
end Integral
end DifferentialGeometry

end
