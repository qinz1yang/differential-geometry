import DifferentialGeometry.Geometry.Curvature.RicciRayleigh
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Scalar
import DifferentialGeometry.Geometry.Curvature.Metric.ConstantRicci

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem ricciTensor_zero (v w : E3) :
    ricciTensor metric 0 v w = metric.inner 0 v w := by
  let : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
  have hsec (u z : E3) :
      metricRm04StandardAt metric 0 u z z u =
        (1 / 2 : ℝ) *
          (metric.inner 0 u u * metric.inner 0 z z -
            metric.inner 0 u z * metric.inner 0 u z) := by
    simpa only [metric_inner_zero, pow_two] using metricRm04_zero u z
  have hRm := metricRm_of_sec metric 0 (1 / 2) hsec
  have hRic := ricci_of_rm metric 0 (1 / 2) hRm v w
  norm_num only [finrank_euclideanSpace_fin, Nat.cast_ofNat] at hRic
  simpa only [one_mul] using hRic

theorem leastUpperRicciAt_zero :
    leastUpperRicciAt metric (0 : E3) = 1 / 2 := by
  obtain ⟨v, hmin, _hminimal⟩ :=
    exists_unitSphere_minimizer_upperRicciRayleighAt metric (0 : E3)
  have hv : (v : E3) ≠ 0 :=
    Metric.ne_of_mem_sphere v.property one_ne_zero
  have hd : metric.inner 0 (v : E3) (v : E3) ≠ 0 :=
    ne_of_gt (metric.pos 0 v.val hv)
  rw [hmin]
  unfold upperRicciRayleighAt
  rw [metricScalarAt_zero, ricciTensor_zero]
  field_simp [hd]
  ring

end DifferentialGeometry.PDE.RicciFlow.StandardCap
