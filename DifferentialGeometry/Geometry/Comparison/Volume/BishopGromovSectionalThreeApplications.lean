import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovSectionalThree
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models

/-!
# Euclidean three-space consumers of the sectional Bishop–Gromov bindings

The flat metric supplies its curvature and metric-norm compatibility directly.
Both zero and negative comparison parameters are tested on actual positive-radius balls.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private local instance : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
  ⟨by simp⟩

private local instance : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
    (fun x : EuclideanSpace ℝ (Fin 3) => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x) :=
  ⟨euclideanMetric.inner, euclideanMetric.contMDiff.continuous, by intro x v w; rfl⟩

private theorem sectionalThree_euclidean_norm :
    IsMetricNorm (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
      (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) := by
  intro x v
  rw [enorm_tangentSpace_vectorSpace, ← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

private theorem sectionalThree_euclidean_sec (x : EuclideanSpace ℝ (Fin 3)) :
    SectionalBoundedBelowAt (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) x 0 := by
  intro v w
  simp only [zero_mul, metricRm04StandardAt_apply, euclideanMetric_metricRm04At_eq_zero,
    zero_apply, le_refl]

theorem sectionalThree_euclidean_volume_ratio :
    0 < (ballVolume (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) 0 1).toReal ∧
      0 < (ballVolume (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) 0 2).toReal ∧
      ballVolume (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) 0 1 < ⊤ ∧
      ballVolume (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) 0 2 < ⊤ ∧
      (ballVolume (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) 0 2).toReal /
        (ballVolume (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) 0 1).toReal ≤ 8 := by
  have hsec : ∀ q ∈ riemannianBallOf
      (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) 0 2,
      SectionalBoundedBelowAt (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) q (-0) := by
    intro q hq
    clear hq
    simpa only [neg_zero] using sectionalThree_euclidean_sec q
  obtain ⟨hs, hR, hsfin, hRfin, hratio, hlower⟩ :=
    localBishopGromov_relative_ratios_sectional_three
      (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) sectionalThree_euclidean_norm
      (by simp) 0 (κ := 0) (s := 1) (R := 2) (by norm_num)
      (by norm_num) (by norm_num) hsec
  clear hlower
  refine ⟨hs, hR, hsfin, hRfin, ?_⟩
  norm_num only [neg_zero] at hratio
  rw [modelVolume_zero 3 2 (by norm_num), modelVolume_zero 3 1 (by norm_num)] at hratio
  have hfactor : euclideanUnitBallVolume 3 * 2 ^ 3 /
      (euclideanUnitBallVolume 3 * 1 ^ 3) = (8 : ℝ) := by
    have hc := (euclideanUnitBallVolume_pos 3).ne'
    field_simp
    norm_num
  simpa only [hfactor] using hratio

theorem sectionalThree_euclidean_negative_parameter :
    ballVolume (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) 0 2 *
        ENNReal.ofReal (modelVolume (-1) 3 1) ≤
      ENNReal.ofReal (modelVolume (-1) 3 2) *
        ballVolume (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) 0 1 := by
  apply localBishopGromov_cross_sectional_three
    (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) sectionalThree_euclidean_norm
    (by simp) 0 (R₀ := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro q hq
  clear hq
  exact (sectionalThree_euclidean_sec q).mono (by norm_num)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
