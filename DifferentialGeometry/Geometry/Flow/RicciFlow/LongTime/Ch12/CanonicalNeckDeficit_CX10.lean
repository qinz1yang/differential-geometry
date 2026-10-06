import DifferentialGeometry.Geometry.Neck.SpatialOverlap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.VolumeTransport
import DifferentialGeometry.Geometry.Measure.RoundCylinderVolume
import DifferentialGeometry.Geometry.Collapse.CurvatureScale

set_option autoImplicit false
noncomputable section

open Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12

/-!
CH12-CX10, review CH12-R2 Q4(b), D-R2-6, at source commit 7219cf77d.
The normalized ambient ball of radius 30 is first captured in the closed
cylinder slab [-60,60]. Its volume is then bounded by the volume of that slab.
Neither completeness of the ambient metric nor a volume lower bound is used.
-/

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M}

private theorem cylinder_metric_zero_eq_round_CX10 (C : CylinderReference) :
    C.metric 0 = Geometry.Metric.roundCylinderMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  have hC := C.inner_eq 0 le_rfl z v w
  apply hC.trans
  rw [Geometry.Metric.roundCylinderMetric_inner]
  simp only [sub_zero, mul_one]
  rfl

omit [SigmaCompactSpace M] in
/-- A fixed ambient ball is contained in a compact, controlled chart window. -/
theorem spatialNeck_ball_capture_CX10 (nk : SpatialNeck g eps p)
    (heps : eps ≤ 1 / 100) :
    riemannianBallOf (scaleMetric (metricScalarAt g p) nk.Q_pos g) p 30 ⊆
      nk.map '' (univ ×ˢ Icc (-60 : ℝ) 60) := by
  have hbuffer : (60 : ℝ) < eps⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num : (0 : ℝ) < 60) nk.eps_pos]
    norm_num
    linarith
  simpa only [show (60 : ℝ) / 2 = 30 by norm_num] using
    nk.ball_subset_closed_slab (by norm_num : (0 : ℝ) < 60) hbuffer

/-- The normalized neck ball has a definite deficit relative to Euclidean volume. -/
theorem spatialNeck_normalized_volume_deficit_CX10 (nk : SpatialNeck g eps p)
    (heps : eps ≤ 1 / 100) :
    ballVolume (scaleMetric (metricScalarAt g p) nk.Q_pos g) p 30 ≤
      ENNReal.ofReal ((1 / 2 : ℝ) * euclideanThreeUnitBallVolume * 30 ^ 3) := by
  let V : Set Cylinder := univ ×ˢ Ioo (-eps⁻¹) eps⁻¹
  let K : Set Cylinder := univ ×ˢ Icc (-60 : ℝ) 60
  have hbuffer : (60 : ℝ) < eps⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num : (0 : ℝ) < 60) nk.eps_pos]
    norm_num
    linarith
  have hKV : K ⊆ V := by
    intro z hz
    exact ⟨hz.1, (neg_lt_neg hbuffer).trans_le hz.2.1, hz.2.2.trans_lt hbuffer⟩
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  have hvol := nk.comparison.volume_image_le nk.map (by simp : (0 : ℝ) ∈ ({0} : Set ℝ))
    nk.eps_pos.le (by linarith [nk.eps_small])
    (isOpen_univ.prod isOpen_Ioo) Subset.rfl nk.domain hK hKV
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  rw [hdim] at hvol
  have hfactor : Real.sqrt ((1 + eps) ^ 3) ≤ 3 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by norm_num, ?_⟩
    have hc := pow_le_pow_left₀ (by linarith [nk.eps_pos] : 0 ≤ 1 + eps)
      (show 1 + eps ≤ 2 by linarith [nk.eps_small]) 3
    norm_num at hc ⊢
    linarith
  have hmodel : riemannianVolumeMeasure IC Cylinder (nk.cylinder.metric 0) K =
      ENNReal.ofReal (960 * Real.pi) := by
    rw [cylinder_metric_zero_eq_round_CX10]
    rw [Geometry.Measure.riemannianVolumeMeasure_roundCylinder_interval]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 8 * Real.pi)]
    congr 1
    norm_num
    ring
  calc
    ballVolume (scaleMetric (metricScalarAt g p) nk.Q_pos g) p 30
      ≤ riemannianVolumeMeasure I3 M (scaleMetric (metricScalarAt g p) nk.Q_pos g)
          (nk.map '' K) := measure_mono (spatialNeck_ball_capture_CX10 nk heps)
    _ ≤ ENNReal.ofReal (Real.sqrt ((1 + eps) ^ 3)) *
          riemannianVolumeMeasure IC Cylinder (nk.cylinder.metric 0) K := hvol
    _ ≤ ENNReal.ofReal 3 * ENNReal.ofReal (960 * Real.pi) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hfactor) hmodel.le
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * euclideanThreeUnitBallVolume * 30 ^ 3) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      apply ENNReal.ofReal_le_ofReal
      dsimp [euclideanThreeUnitBallVolume]
      nlinarith [Real.pi_pos]

/-- The same deficit at the physical scalar-curvature scale. -/
theorem spatialNeck_volume_deficit_CX10 (nk : SpatialNeck g eps p)
    (heps : eps ≤ 1 / 100) :
    ballVolume g p (30 / Real.sqrt (metricScalarAt g p)) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) * euclideanThreeUnitBallVolume *
        (30 / Real.sqrt (metricScalarAt g p)) ^ 3) := by
  have hs : 0 < Real.sqrt (metricScalarAt g p) := Real.sqrt_pos.mpr nk.Q_pos
  have h := spatialNeck_normalized_volume_deficit_CX10 nk heps
  have hrad : Real.sqrt (metricScalarAt g p) *
      (30 / Real.sqrt (metricScalarAt g p)) = 30 := by field_simp
  change riemannianVolumeMeasure I3 M (scaleMetric (metricScalarAt g p) nk.Q_pos g)
    (riemannianBallOf (scaleMetric (metricScalarAt g p) nk.Q_pos g) p 30) ≤ _ at h
  rw [← hrad, riemannianBallOf_scaleMetric, volume_scale_apply] at h
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  rw [hdim] at h
  have hright : ENNReal.ofReal ((1 / 2 : ℝ) * euclideanThreeUnitBallVolume *
      (Real.sqrt (metricScalarAt g p) * (30 / Real.sqrt (metricScalarAt g p))) ^ 3) =
      ENNReal.ofReal (Real.sqrt (metricScalarAt g p)) ^ 3 *
        ENNReal.ofReal ((1 / 2 : ℝ) * euclideanThreeUnitBallVolume *
          (30 / Real.sqrt (metricScalarAt g p)) ^ 3) := by
    rw [← ENNReal.ofReal_pow hs.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hright] at h
  exact (ENNReal.mul_le_mul_iff_right (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hs).ne')
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)).mp h

end GC.LongTime.Ch12
