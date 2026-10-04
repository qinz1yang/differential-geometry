import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.HeatEquation
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormBridge

/-!
# The flow curvature-derivative tower is the static one

Along a Ricci-flow solution `S`, the iterated covariant derivatives of the curvature are recorded as
`nablaKRm04Field S t k : Tensor0SField (4 + k)` (`IteratedCovariantDerivativeFields.lean`), starting
from `S.base.rm04 t = metricRm04 (S.base.metric t)` and iterating the total covariant derivative of the
connection `S.family.connection t`, which is the Levi-Civita connection of `S.base.metric t`. The
Shi estimates are stated for `nablaKRm04NormSqIntrinsic S k t x`, the fibre norm square of that field.

The compactness interfaces (`SeqBoundedGeometry`) measure the same object as
`CheegerGromovCompactness.curvCovDeriv g k : Tensor0SField (k + 4)` and `curvDerivNorm k g x`.

This file proves that the two towers are *equal as tensor fields*, by induction on `k`, so the norms
agree exactly (no comparison constant):

* `nablaKRm04Field_eq_iteratedCurvatureTensor`: homogeneous equality at arity `4 + k` with the
  static tower `iteratedCurvatureTensor` of `Geometry/Curvature/Metric/DerivativeNorm.lean`;
* `nablaKRm04Field_heq_curvCovDeriv`: heterogeneous equality (arities `4 + k` and `k + 4`) with the
  compactness tower `curvCovDeriv`, through the wave-1 bridge
  `curvCovDeriv_heq_iteratedCurvatureTensor`;
* `nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq`, `nablaKRm04NormSqIntrinsic_eq_curvDerivNorm_sq`,
  `sqrt_nablaKRm04NormSqIntrinsic_eq_curvDerivNorm`: the norm identities.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

omit [SigmaCompactSpace M] in
/-- One step of the flow tower is the Levi-Civita step `covStep` of the time-`t` metric. -/
theorem nablaKRm04Field_succ_eq_covStep (S : SolutionOn (I := I) (M := M) D) (t : ℝ)
    (k : ℕ) :
    nablaKRm04Field (I := I) S t (k + 1) =
      CheegerGromovCompactness.covStep (S.base.metric t) (4 + k)
        (nablaKRm04Field (I := I) S t k) := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [CheegerGromovCompactness.covStep_apply]
  rfl

omit [SigmaCompactSpace M] in
/-- **D1, field equality.** The flow curvature-derivative tower is the static tower of the time-`t`
metric, as tensor fields of arity `4 + k`. -/
theorem nablaKRm04Field_eq_iteratedCurvatureTensor (S : SolutionOn (I := I) (M := M) D)
    (t : ℝ) (k : ℕ) :
    nablaKRm04Field (I := I) S t k = iteratedCurvatureTensor (S.base.metric t) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [nablaKRm04Field_succ_eq_covStep, ih, iteratedCurvatureTensor_succ_eq_covStep]

omit [SigmaCompactSpace M] in
/-- **D1, field equality with the compactness tower** (arities `4 + k` and `k + 4`). -/
theorem nablaKRm04Field_heq_curvCovDeriv (S : SolutionOn (I := I) (M := M) D) (t : ℝ)
    (k : ℕ) :
    HEq (nablaKRm04Field (I := I) S t k)
      (CheegerGromovCompactness.curvCovDeriv (S.base.metric t) k) := by
  rw [nablaKRm04Field_eq_iteratedCurvatureTensor]
  exact (curvCovDeriv_heq_iteratedCurvatureTensor (S.base.metric t) k).symm

omit [SigmaCompactSpace M] in
/-- The Shi-side norm square is the compactness-side norm square. -/
theorem nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq (S : SolutionOn (I := I) (M := M) D)
    (k : ℕ) (t : ℝ) (x : M) :
    nablaKRm04NormSqIntrinsic (I := I) S k t x =
      CheegerGromovCompactness.curvDerivNormSq k (S.base.metric t) x := by
  rw [nablaKRm04NormSqIntrinsic, CheegerGromovCompactness.curvDerivNormSq]
  exact normSq0S_apply_eq_of_heq (S.base.metric t) x (Nat.add_comm 4 k)
    (nablaKRm04Field_heq_curvCovDeriv S t k)

omit [SigmaCompactSpace M] in
/-- **D1, norm form.** `|∇^k Rm|²` along the flow is `curvDerivNorm k g(t) ^ 2`, exactly. -/
theorem nablaKRm04NormSqIntrinsic_eq_curvDerivNorm_sq (S : SolutionOn (I := I) (M := M) D)
    (k : ℕ) (t : ℝ) (x : M) :
    nablaKRm04NormSqIntrinsic (I := I) S k t x =
      CheegerGromovCompactness.curvDerivNorm k (S.base.metric t) x ^ 2 := by
  rw [nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq, CheegerGromovCompactness.curvDerivNorm]
  exact (Real.sq_sqrt (normSq0S_nonneg _ x _ _)).symm

omit [SigmaCompactSpace M] in
/-- **D1, root form.** `√|∇^k Rm|²` along the flow is `curvDerivNorm k g(t)`. -/
theorem sqrt_nablaKRm04NormSqIntrinsic_eq_curvDerivNorm (S : SolutionOn (I := I) (M := M) D)
    (k : ℕ) (t : ℝ) (x : M) :
    Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S k t x) =
      CheegerGromovCompactness.curvDerivNorm k (S.base.metric t) x := by
  rw [nablaKRm04NormSqIntrinsic_eq_curvDerivNormSq]
  rfl

end DifferentialGeometry.PDE.RicciFlow
