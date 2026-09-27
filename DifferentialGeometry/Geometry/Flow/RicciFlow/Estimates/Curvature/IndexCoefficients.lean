import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarHessian

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow
open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

private theorem ricciTower_eq_totalNabla
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M) :
    ricCovTower (I := I) (S.base.metric t) (S.base.metric t) 1 x =
      totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (S.base.connection t)
        (S.ricci t) x := by
  change totalNabla0S (𝕜 := ℝ) (I := I) 2
      (leviCivitaConnectionOfMetric (I := I) (S.base.metric t))
      (metricRicci (I := I) (S.base.metric t)) _ x =
    totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (S.base.connection t)
      (S.ricci t) x
  rfl

theorem sqrt_nablaRicci_le_of_curvDerivNorm
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M) (B : ℝ)
    (hjet : curvDerivNorm (I := I) (M := M) 1 (S.base.metric t) x ≤ B) :
    Real.sqrt (normSq0S (I := I) (S.base.metric t) x 3
      (totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (S.base.connection t)
        (S.ricci t) x)) ≤
      Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) * B := by
  have hsq := ricTower_normSq_le (I := I) S t 1 x
  rw [ricciTower_eq_totalNabla (I := I) S t x] at hsq
  have hsq' :
      Real.sqrt (normSq0S (I := I) (S.base.metric t) x 3
        (totalNabla0SFun (𝕜 := ℝ) (I := I) 2 (S.base.connection t)
          (S.ricci t) x)) ≤
        Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5 *
          nablaKRm04NormSqIntrinsic S 1 t x) :=
    Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul (by positivity)] at hsq'
  have hjet' : Real.sqrt (nablaKRm04NormSqIntrinsic S 1 t x) ≤ B := by
    have heq := curvNormSq_eq (I := I) S 1 t x
    change Real.sqrt (curvDerivNormSq (I := I) (M := M) 1 (S.base.metric t) x) ≤ B at hjet
    rw [heq] at hjet
    exact hjet
  exact hsq'.trans (mul_le_mul_of_nonneg_left hjet' (Real.sqrt_nonneg _))

theorem sqrt_scalarHess_le_of_curvDerivNorm
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M) (B : ℝ)
    (hjet : curvDerivNorm (I := I) (M := M) 2 (S.base.metric t) x ≤ B) :
    Real.sqrt (normSq0S (I := I) (S.base.metric t) x 2
      (hessianSec (I := I) (S.base.connection t)
        (metricCov_smooth (I := I) (S.base.metric t))
        (S.scalar t) (scalarSmoothOfSolution S t) x)) ≤
      (Module.finrank ℝ E : ℝ) ^ 5 * B := by
  have hbase := sqrt_normSq_scalarHess_le_second_curvature (I := I) S t x
  have hjet' : Real.sqrt (nablaKRm04NormSqIntrinsic S 2 t x) ≤ B := by
    have heq := curvNormSq_eq (I := I) S 2 t x
    change Real.sqrt (curvDerivNormSq (I := I) (M := M) 2 (S.base.metric t) x) ≤ B at hjet
    rw [heq] at hjet
    exact hjet
  exact hbase.trans (mul_le_mul_of_nonneg_left hjet' (by positivity))

theorem sqrt_rm04_le_of_curvDerivNorm
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M) (B : ℝ)
    (hjet : curvDerivNorm (I := I) (M := M) 0 (S.base.metric t) x ≤ B) :
    Real.sqrt (normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x)) ≤ B := by
  have heq := curvNormSq_eq (I := I) S 0 t x
  change Real.sqrt (curvDerivNormSq (I := I) (M := M) 0 (S.base.metric t) x) ≤ B at hjet
  rw [heq] at hjet
  simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero] using hjet

end DifferentialGeometry.PDE.RicciFlow
