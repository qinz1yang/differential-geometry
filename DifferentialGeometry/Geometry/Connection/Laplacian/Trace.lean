import DifferentialGeometry.Geometry.Connection.TensorNabla.HomTrace
import DifferentialGeometry.Geometry.Connection.Laplacian.Map
import DifferentialGeometry.Bundle.ClmSectionSmooth
import DifferentialGeometry.Geometry.Connection.Laplacian.Trivial

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Connection
open HomConnectionGen
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I 1 F V]

theorem trace_rawBundleEndomorphismConnLap_of_isMetricCompatible
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    (hcov : cov.IsMetricCompatible) (hsmooth : cov.ContMDiffCovariantDerivative ∞)
    (A : ∀ y, V y →L[ℝ] V y)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) 2
      (fun y => (⟨y, A y⟩ : TotalSpace (F →L[ℝ] F) (fun y => V y →L[ℝ] V y))))
    (x : M) :
    LinearMap.trace ℝ (V x) (rawBundleEndomorphismConnLap g cov A x).toLinearMap =
      rawBundleConnLap g (CovariantDerivative.trivial I M ℝ)
        (fun y => LinearMap.trace ℝ (V y) (A y).toLinearMap) x := by
  let _ : cov.ContMDiffCovariantDerivative ∞ := hsmooth
  let D := homBundleCovariantDerivativeGen I M F V F V cov cov
  let φ : ∀ y, (V y →L[ℝ] V y) →ₗ[ℝ] ℝ := fun y =>
    { toFun := fun B => LinearMap.trace ℝ (V y) B.toLinearMap
      map_add' := by intro B C; simp
      map_smul' := by intro a B; simp }
  have hm (B : ∀ y, V y →L[ℝ] V y)
      (hB : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) 1
        (fun y => (⟨y, B y⟩ : TotalSpace (F →L[ℝ] F) (fun y => V y →L[ℝ] V y))))
      (y : M) (v : TangentSpace I y) :
      CovariantDerivative.trivial I M ℝ (fun z => φ z (B z)) y v = φ y (D B y v) := by
    exact mvfderiv_trace_of_isMetricCompatible cov hcov ((hB y).mdifferentiableAt one_ne_zero) v
  exact (CovariantDerivative.rawBundleConnLap_map D inferInstance
    (CovariantDerivative.trivial I M ℝ) φ hm g A hA x).symm

open DifferentialGeometry.Geometry.Operator

theorem trace_rawBundleEndomorphismConnLap_eq_laplacian_of_isMetricCompatible
    [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I F V)
    (hcov : cov.IsMetricCompatible) (hsmooth : cov.ContMDiffCovariantDerivative ∞)
    (A : ∀ y, V y →L[ℝ] V y)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F)) ∞
      (fun y => (⟨y, A y⟩ : TotalSpace (F →L[ℝ] F) (fun y => V y →L[ℝ] V y))))
    (x : M) :
    LinearMap.trace ℝ (V x) (rawBundleEndomorphismConnLap g cov A x).toLinearMap =
      laplacian (LeviCivita g) g
        (fun y => LinearMap.trace ℝ (V y) (A y).toLinearMap) x := by
  rw [trace_rawBundleEndomorphismConnLap_of_isMetricCompatible g cov hcov hsmooth A
    (hA.of_le (by norm_cast)) x]
  exact rawBundleConnLap_trivial_eq_laplacian g (contMDiff_linearMap_trace A hA) x

end DifferentialGeometry.Geometry.Connection
