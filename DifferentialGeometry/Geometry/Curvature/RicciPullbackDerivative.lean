import DifferentialGeometry.Geometry.Curvature.Metric
import DifferentialGeometry.Geometry.Connection.TensorNabla.TotalPullback
import DifferentialGeometry.Geometry.Connection.Laplacian.CovariantTensor
import DifferentialGeometry.Geometry.Connection.Laplacian.PullbackTensor

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

theorem multilinear_pullback_metricRicci_eq_metricNablaRic
    (g : SmoothRiemannianMetric I M)
    (φ : ∀ x : M, TangentSpace I x ≃L[Real] TangentSpace I x)
    (hφ : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ :
        TotalSpace (E →L[Real] E)
          (fun x => TangentSpace I x →L[Real] TangentSpace I x))))
    (x : M) (X : TangentSpace I x) (tail : Fin 2 → TangentSpace I x) :
    (CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map (metricCov g)).multilinear 2
        (fun y => tensor0SPullbackCLE 2 (φ y).toLinearEquiv (metricRicci g y))
        x (φ x X) tail =
      tensor0SPullbackCLE 3 (φ x).toLinearEquiv
        (metricNablaRic g x) (Fin.cons X tail) := by
  exact multilinear_pullback_eq_totalNabla0SFun φ hφ 2 (metricCov g)
    (metricRicci g) x X tail

theorem rawBundleConnLap_pullback_metricRicci_eq_roughLap0STensor
    [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M)
    (φ : ∀ x : M, TangentSpace I x ≃L[Real] TangentSpace I x)
    (hφ : ContMDiff I (I.prod 𝓘(Real, E →L[Real] E)) 1
      (fun x => (⟨x, (φ x).toContinuousLinearMap⟩ :
        TotalSpace (E →L[Real] E)
          (fun x => TangentSpace I x →L[Real] TangentSpace I x))))
    (x : M) :
    rawBundleConnLap g
      ((CovariantDerivative.pullbackFiberwiseLinearEquiv
        (fun y => (φ y).toLinearEquiv) hφ.clm_bundle_map (metricCov g)).multilinear 2)
      (fun y => tensor0SPullbackCLE 2 (φ y).toLinearEquiv (metricRicci g y)) x =
      tensor0SPullbackCLE 2 (φ x).toLinearEquiv
        (roughLap0STensor g (metricNabla2Ric g x)) := by
  have h := rawBundleConnLap_multilinear_pullbackFiberwiseLinearEquiv
    φ hφ g (LeviCivita g) 2 ((metricRicci g).contMDiff x |>.of_le
      (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
  have hbase := rawBundleConnLap_multilinear_eq_roughLap0STensor
    g (metricRicci g)
    (totalNabla0S_reg 2 (metricCov g) (metricCov_smooth g) (metricRicci g)) x
  rw [hbase] at h
  exact h

end DifferentialGeometry.Geometry.Curvature
