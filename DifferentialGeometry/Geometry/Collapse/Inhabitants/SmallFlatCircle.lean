import DifferentialGeometry.Geometry.Metric.AddCircle
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat

/-!
A canonical rescaling of the actual flat circle has uniformly small intrinsic diameter.
Compactness is used for its length metric, and its one-dimensional curvature vanishes.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature Set
open scoped Manifold

namespace DifferentialGeometry.Geometry.Collapse

private theorem smallFlatCircle_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y : AddCircle (1 : ℝ),
      riemannianEDistOf AddCircle.flatMetric x y ≤ ENNReal.ofReal D := by
  let intrinsic := inducedMetricSpace AddCircle.flatMetric
  let intrinsicPseudo : PseudoMetricSpace (AddCircle (1 : ℝ)) := intrinsic.toPseudoMetricSpace
  let intrinsicEMetric : PseudoEMetricSpace (AddCircle (1 : ℝ)) := intrinsic.toPseudoEMetricSpace
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.mp
    (isCompact_univ : IsCompact (univ : Set (AddCircle (1 : ℝ)))).isBounded
  refine ⟨max D 0, le_max_right D 0, ?_⟩
  intro x y
  have hb := (hD (mem_univ x) (mem_univ y)).trans (le_max_left D 0)
  exact (ENNReal.ofReal_toReal (riemannianEDistOf_ne_top AddCircle.flatMetric x y)).symm.trans_le
    (ENNReal.ofReal_le_ofReal hb)

private def smallFlatCircleBound : ℝ := Classical.choose smallFlatCircle_bound

private theorem smallFlatCircleBound_nonneg : 0 ≤ smallFlatCircleBound :=
  (Classical.choose_spec smallFlatCircle_bound).1

noncomputable def smallFlatCircleScale : ℝ :=
  1 / (10000 * (smallFlatCircleBound + 1))

theorem smallFlatCircleScale_pos : 0 < smallFlatCircleScale := by
  have hD := smallFlatCircleBound_nonneg
  unfold smallFlatCircleScale
  positivity

def smallFlatCircleMetric :
    SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) :=
  scaleMetric (smallFlatCircleScale ^ 2)
    (sq_pos_of_pos smallFlatCircleScale_pos) AddCircle.flatMetric

theorem smallFlatCircle_distance (x y : AddCircle (1 : ℝ)) :
    riemannianEDistOf smallFlatCircleMetric x y ≤ ENNReal.ofReal (1 / 10000 : ℝ) := by
  rw [smallFlatCircleMetric, edistOf_scale, Real.sqrt_sq smallFlatCircleScale_pos.le]
  have hb := (Classical.choose_spec smallFlatCircle_bound).2 x y
  have hmul := mul_le_mul' (le_refl (ENNReal.ofReal smallFlatCircleScale)) hb
  refine hmul.trans ?_
  rw [← ENNReal.ofReal_mul smallFlatCircleScale_pos.le]
  apply ENNReal.ofReal_le_ofReal
  change smallFlatCircleScale * smallFlatCircleBound ≤ (1 / 10000 : ℝ)
  have hD := smallFlatCircleBound_nonneg
  unfold smallFlatCircleScale
  rw [div_mul_eq_mul_div, one_mul]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 10000 * (smallFlatCircleBound + 1))).2
  nlinarith

theorem smallFlatCircle_flat (x : AddCircle (1 : ℝ))
    (v w : TangentSpace 𝓘(ℝ, ℝ) x) :
    metricRm04StandardAt smallFlatCircleMetric x v w w v = 0 := by
  change metricRm04At smallFlatCircleMetric x (vec4 v w w v) = 0
  rw [metricRm04At_eq_zero_of_finrank_le_one smallFlatCircleMetric (by simp) x]
  rfl

end DifferentialGeometry.Geometry.Collapse
