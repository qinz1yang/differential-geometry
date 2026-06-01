import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.HeatSemigroupIntrinsic
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.AbstractSemigroup

/-!
# Intrinsic tensor heat semigroup as a `BoundedC0Semigroup`

For a closed Riemannian manifold `(M, g)` and ranks `(r, s)`, this file
packages the **chart-selection-free** intrinsic tensor heat semigroup
`e^{t Δ_∇}` on `TensorL2 r s g` as a bounded strongly continuous
one-parameter contraction semigroup `BoundedC0Semigroup (TensorL2 r s g)`.

The four structural fields are discharged from the established analytic
properties of the intrinsic heat semigroup:

* `apply_zero` from `tensorHeatSemigroup_intrinsic_apply_zero`
  (`e^{0 Δ_∇} = id`);
* `apply_add` from `tensorHeatSemigroup_intrinsic_apply_add` (the
  semigroup law, valid for non-negative times — exactly the hypotheses
  the field requires);
* `opNorm_le_one` from `tensorHeatSemigroup_intrinsic_opNorm_le_one`
  (the operator-norm contraction bound, available for every real time,
  in particular for `t ≥ 0`);
* `continuousOn_apply` from `tensorHeatSemigroup_intrinsic_continuousOn`
  (strong continuity on `[0, ∞)`).

## Main definition

* `tensorBoundedC0Semigroup g r s` — the intrinsic tensor heat
  semigroup as a `BoundedC0Semigroup (TensorL2 r s g)`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

/-- The intrinsic tensor heat semigroup `e^{t Δ_∇}` on `TensorL2 r s g`
packaged as a bounded strongly continuous one-parameter contraction
semigroup, **without any chart-selection hypothesis**. -/
noncomputable def tensorBoundedC0Semigroup
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    BoundedC0Semigroup (TensorL2 r s g) where
  toFun := fun t => tensorHeatSemigroup (I := I) (M := M) g r s t
  apply_zero :=
    tensorHeatSemigroup_intrinsic_apply_zero (I := I) (M := M) g r s
  apply_add := fun _ _ ht hs =>
    tensorHeatSemigroup_intrinsic_apply_add (I := I) (M := M) g r s ht hs
  opNorm_le_one := fun t _ =>
    tensorHeatSemigroup_intrinsic_opNorm_le_one (I := I) (M := M) g r s t
  continuousOn_apply := fun T =>
    tensorHeatSemigroup_intrinsic_continuousOn (I := I) (M := M) g r s T

/-- The underlying one-parameter family of `tensorBoundedC0Semigroup`
is the intrinsic tensor heat semigroup. -/
@[simp]
theorem tensorBoundedC0Semigroup_intrinsic_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (t : ℝ) :
    tensorBoundedC0Semigroup (I := I) (M := M) g r s t =
      tensorHeatSemigroup (I := I) (M := M) g r s t :=
  rfl

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
