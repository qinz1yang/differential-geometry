import DifferentialGeometry.Geometry.Comparison.Volume.ScaledBallComparison
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

set_option autoImplicit false

open Bundle Manifold DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped Manifold ENNReal

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

example (r : ℝ) (hr : 0 < r) :
    ballVolume (euclideanMetric (E := ℝ)) 0 (2 * r) ≤
      2 * ballVolume (euclideanMetric (E := ℝ)) 0 r := by
  let : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩
  let : IsContinuousRiemannianBundle ℝ (fun x : ℝ => TangentSpace 𝓘(ℝ, ℝ) x) :=
    ⟨euclideanMetric.inner, euclideanMetric.contMDiff.continuous, fun _ _ _ => rfl⟩
  have hn : IsMetricNorm (I := 𝓘(ℝ, ℝ)) (euclideanMetric (E := ℝ)) := by
    intro x v
    rw [enorm_tangentSpace_vectorSpace]
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hc := ballVolume_mul_scale_le_model_ratio (euclideanMetric (E := ℝ)) hn 0
    (q := 0) (r := r) (s := 1) (R := 2) (by norm_num) hr (by norm_num) (by norm_num)
    (by
      intro x _ v
      simp only [zero_div, zero_pow (by decide : 2 ≠ 0), neg_zero, mul_zero, zero_mul,
        euclideanMetric_ricciTensor, le_refl])
  norm_num only [Module.finrank_self, zero_pow (by decide : 2 ≠ 0), neg_zero, one_mul] at hc
  rw [modelVolume_zero 1 2 (by omega), modelVolume_zero 1 1 (by omega)] at hc
  have hω := euclideanUnitBallVolume_pos 1
  have hratio : euclideanUnitBallVolume 1 * 2 ^ 1 /
      (euclideanUnitBallVolume 1 * 1 ^ 1) = (2 : ℝ) := by
    field_simp
  simpa only [hratio, ENNReal.ofReal_ofNat] using hc
