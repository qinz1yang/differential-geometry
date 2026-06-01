import DifferentialGeometry.Analysis.Sobolev.Tools.Translation

/-!
# Mollifier construction on Euclidean space

This module provides a fixed mollifier on `EuclideanSpace ℝ (Fin d)` and its
ε-rescaled version, used downstream in the convolution-smoothing arguments
underlying compactness in `L^p`.

The construction is based on Mathlib's `ContDiffBump`: a smooth, nonnegative,
compactly supported bump function with a chosen radius. The `normed` variant
of a bump integrates to one.
-/

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The unit `ContDiffBump` centred at the origin with `rIn = 1/2` and
`rOut = 1`. -/
def mollifierBump : ContDiffBump (0 : E) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The fixed mollifier on `EuclideanSpace ℝ (Fin d)`: smooth, nonnegative,
supported in the closed unit ball, integrating to 1. -/
def mollifier : E → ℝ := mollifierBump.normed (volume : Measure E)

theorem mollifier_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (mollifier (d := d)) :=
  (mollifierBump (d := d)).contDiff_normed

theorem mollifier_continuous :
    Continuous (mollifier (d := d)) :=
  (mollifierBump (d := d)).continuous_normed

theorem mollifier_nonneg (x : E) : 0 ≤ mollifier (d := d) x :=
  (mollifierBump (d := d)).nonneg_normed x

theorem mollifier_integral_eq_one :
    ∫ x, mollifier (d := d) x ∂(volume : Measure E) = 1 :=
  (mollifierBump (d := d)).integral_normed

theorem mollifier_integrable :
    Integrable (mollifier (d := d)) (volume : Measure E) :=
  (mollifierBump (d := d)).integrable_normed

theorem mollifier_compactSupport : HasCompactSupport (mollifier (d := d)) :=
  (mollifierBump (d := d)).hasCompactSupport_normed

theorem mollifier_support_eq :
    Function.support (mollifier (d := d)) = Metric.ball (0 : E) 1 := by
  unfold mollifier
  simpa using (mollifierBump (d := d)).support_normed_eq (μ := volume)

theorem mollifier_tsupport_eq :
    tsupport (mollifier (d := d)) = Metric.closedBall (0 : E) 1 := by
  unfold mollifier
  simpa using (mollifierBump (d := d)).tsupport_normed_eq (μ := volume)

theorem mollifier_support_subset_closedBall_one :
    Function.support (mollifier (d := d)) ⊆ Metric.closedBall (0 : E) 1 := by
  rw [mollifier_support_eq]
  exact Metric.ball_subset_closedBall

/-- The ε-scaled `ContDiffBump` centred at the origin with `rIn = ε/2`,
`rOut = ε`. -/
def mollifierBumpEps {ε : ℝ} (hε : 0 < ε) : ContDiffBump (0 : E) where
  rIn := ε / 2
  rOut := ε
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The ε-scaled mollifier: smooth, nonnegative, supported in the closed
ε-ball, integrating to 1. -/
def mollifierEps {ε : ℝ} (hε : 0 < ε) : E → ℝ :=
  (mollifierBumpEps (d := d) hε).normed (volume : Measure E)

theorem mollifierEps_smooth {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifierEps (d := d) hε) :=
  (mollifierBumpEps (d := d) hε).contDiff_normed

theorem mollifierEps_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (mollifierEps (d := d) hε) :=
  (mollifierBumpEps (d := d) hε).continuous_normed

theorem mollifierEps_nonneg {ε : ℝ} (hε : 0 < ε) (x : E) :
    0 ≤ mollifierEps (d := d) hε x :=
  (mollifierBumpEps (d := d) hε).nonneg_normed x

theorem mollifierEps_integral_eq_one {ε : ℝ} (hε : 0 < ε) :
    ∫ x, mollifierEps (d := d) hε x ∂(volume : Measure E) = 1 :=
  (mollifierBumpEps (d := d) hε).integral_normed

theorem mollifierEps_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (mollifierEps (d := d) hε) (volume : Measure E) :=
  (mollifierBumpEps (d := d) hε).integrable_normed

theorem mollifierEps_compactSupport {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (mollifierEps (d := d) hε) :=
  (mollifierBumpEps (d := d) hε).hasCompactSupport_normed

theorem mollifierEps_support_eq {ε : ℝ} (hε : 0 < ε) :
    Function.support (mollifierEps (d := d) hε) = Metric.ball (0 : E) ε := by
  unfold mollifierEps
  simpa [mollifierBumpEps] using
    (mollifierBumpEps (d := d) hε).support_normed_eq (μ := volume)

theorem mollifierEps_tsupport_eq {ε : ℝ} (hε : 0 < ε) :
    tsupport (mollifierEps (d := d) hε) = Metric.closedBall (0 : E) ε := by
  unfold mollifierEps
  simpa [mollifierBumpEps] using
    (mollifierBumpEps (d := d) hε).tsupport_normed_eq (μ := volume)

theorem mollifierEps_support_subset_closedBall_eps
    {ε : ℝ} (hε : 0 < ε) :
    Function.support (mollifierEps (d := d) hε) ⊆ Metric.closedBall (0 : E) ε := by
  rw [mollifierEps_support_eq]
  exact Metric.ball_subset_closedBall

theorem mollifierEps_tsupport_subset_closedBall_eps
    {ε : ℝ} (hε : 0 < ε) :
    tsupport (mollifierEps (d := d) hε) ⊆ Metric.closedBall (0 : E) ε := by
  rw [mollifierEps_tsupport_eq]

end DifferentialGeometry.Analysis.Sobolev
