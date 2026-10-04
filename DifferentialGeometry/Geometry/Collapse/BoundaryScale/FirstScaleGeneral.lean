import DifferentialGeometry.Geometry.Comparison.Volume.FirstCrossingScale

/-!
# First volume scales on compact manifolds of any model (BSA03 kernel)

`firstVolumeScale g p w` is the infimum of the positive radii `r` with `vol B(p,r) ≤ w r³`.
Its definition makes sense for every model with corners, in particular on compact carriers with
boundary. This file records the elementary facts used by the boundary-scale rows of chapter 14
(blueprint 207B, BSA03–BSA06) WITHOUT a small-ball volume estimate at the center: the scale is
nonnegative, bounded by every crossing radius, below it the volume is larger than the barrier,
it is attained from below whenever it is positive, and it is antitone in the volume parameter.
A zero scale is allowed; then the ball of that radius is empty.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- The first volume scale is nonnegative. -/
theorem firstVolumeScale_nonneg (g : SmoothRiemannianMetric I M) (p : M) (w : ℝ) :
    0 ≤ firstVolumeScale g p w :=
  Real.sInf_nonneg fun _ hr => hr.1.le

/-- The first volume scale is at most every positive crossing radius. -/
theorem firstVolumeScale_le_of_ballVolume_toReal_le (g : SmoothRiemannianMetric I M)
    (p : M) {w s : ℝ} (hs : 0 < s) (hvol : (ballVolume g p s).toReal ≤ w * s ^ 3) :
    firstVolumeScale g p w ≤ s :=
  csInf_le ⟨0, fun _ hr => hr.1.le⟩ ⟨hs, hvol⟩

/-- Below the first volume scale the volume is strictly above the cubic barrier. -/
theorem lt_ballVolume_toReal_of_lt_firstVolumeScale (g : SmoothRiemannianMetric I M)
    (p : M) {w r : ℝ} (hr : 0 < r) (hlt : r < firstVolumeScale g p w) :
    w * r ^ 3 < (ballVolume g p r).toReal := by
  by_contra! hle
  exact (firstVolumeScale_le_of_ballVolume_toReal_le g p hr hle).not_gt hlt

variable [CompactSpace M]

/-- A positive first volume scale is attained from below: the volume of its ball is at least the
barrier. (Left continuity of the ball volume; no small-ball estimate is used.) -/
theorem le_ballVolume_toReal_firstVolumeScale_of_pos (g : SmoothRiemannianMetric I M)
    (p : M) {w : ℝ} (hpos : 0 < firstVolumeScale g p w) :
    w * firstVolumeScale g p w ^ 3 ≤ (ballVolume g p (firstVolumeScale g p w)).toReal := by
  have hF : ContinuousWithinAt (fun r : ℝ => w * r ^ 3) (Iio (firstVolumeScale g p w))
      (firstVolumeScale g p w) := by
    fun_prop
  apply le_of_tendsto_of_tendsto hF
    (ballVolume_toReal_continuousWithinAt_left g p (firstVolumeScale g p w))
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hpos)] with r hrs hr
  exact (lt_ballVolume_toReal_of_lt_firstVolumeScale g p hr hrs).le

/-- On a compact manifold every positive volume parameter has a crossing radius. -/
theorem exists_ballVolume_toReal_le_cube (g : SmoothRiemannianMetric I M) (p : M) {w : ℝ}
    (hw : 0 < w) : ∃ s > 0, (ballVolume g p s).toReal ≤ w * s ^ 3 := by
  set C := (Integral.Measure.riemannianVolumeMeasure I M g univ).toReal
  set R := max 1 (C / w + 1) with hRdef
  have hR1 : 1 ≤ R := le_max_left _ _
  have hCR : C / w < R := by
    have h := le_max_right 1 (C / w + 1)
    linarith
  have hCw : C < w * R := by
    simpa only [mul_comm] using (div_lt_iff₀ hw).mp hCR
  refine ⟨R, zero_lt_one.trans_le hR1, (ballVolume_toReal_le_total g p R).trans ?_⟩
  exact hCw.le.trans (mul_le_mul_of_nonneg_left (le_self_pow₀ hR1 (by norm_num)) hw.le)

/-- The first volume scale is antitone in the volume parameter. -/
theorem firstVolumeScale_anti_of_le (g : SmoothRiemannianMetric I M) (p : M) {w w' : ℝ}
    (hw : 0 < w) (hww' : w ≤ w') :
    firstVolumeScale g p w' ≤ firstVolumeScale g p w := by
  obtain ⟨s, hs, hvol⟩ := exists_ballVolume_toReal_le_cube g p hw
  refine csInf_le_csInf ⟨0, fun _ hr => hr.1.le⟩ ⟨s, hs, hvol⟩ ?_
  intro r hr
  exact ⟨hr.1, hr.2.trans (mul_le_mul_of_nonneg_right hww' (pow_pos hr.1 3).le)⟩

end DifferentialGeometry.Geometry.Collapse
