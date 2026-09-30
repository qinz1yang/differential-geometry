import DifferentialGeometry.Geometry.Metric.SegmentLog
import DifferentialGeometry.Geometry.Comparison.EightRadialContraction
import DifferentialGeometry.Geometry.Comparison.IntrinsicGeodesicDirections
import Mathlib.Topology.MetricSpace.HausdorffDimension

set_option autoImplicit false

open Set Metric Filter Topology Real
open scoped NNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompleteSpace X]
variable (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
  ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
    eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
variable (p : X) {R : ℝ} (hR : 0 < R)
variable [LocallyCompactSpace (ball p (8 * R))]
variable (hlocal : ∀ z : ball p (8 * R), ∃ Ω : Set (ball p (8 * R)),
  @IsOpen (ball p (8 * R))
    (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
  @fourPointComparison (ball p (8 * R))
    (intrinsicBallMetricSpace hcurves p (by positivity : 0 < 8 * R)) 1 Ω ∧ z ∈ Ω)

include hcurves hR hlocal

theorem antilipschitz_segmentLog_of_chosen_isometries_intrinsic_8_buffer
    {q : X} (hq : q ∈ ball p (R / 2))
    (γ : ∀ x : closedBall p R, Icc (0 : ℝ) (dist q (x : X)) → X)
    (hγ : ∀ x, Isometry (γ x))
    (hγ0 : ∀ x, γ x ⟨0, le_rfl, dist_nonneg⟩ = q)
    (hγend : ∀ x, γ x ⟨dist q (x : X), dist_nonneg, le_rfl⟩ = x) :
    letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
      (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
      (by change dist q p < 8 * R; have hh : dist q p < R / 2 := hq; linarith)
    AntilipschitzWith (NNReal.mk (sinh (2 * R) / (2 * R)) (by positivity))
      (fun x : closedBall p R => segmentLog x.val (γ x) (hγ x) (hγ0 x)) := by
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
    (by change dist q p < 8 * R; have hh : dist q p < R / 2 := hq; linarith)
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have hlim := dist_div_tendsto_segmentLog x.val y.val (γ x) (γ y)
    (hγ x) (hγ y) (hγ0 x) (hγ0 y)
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      (2 * R / sinh (2 * R)) * dist x.val y.val ≤
      dist (IccExtend dist_nonneg (γ x) (dist q x.val * t))
        (IccExtend dist_nonneg (γ y) (dist q y.val * t)) / t := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with t ht
    let u : unitInterval := ⟨t, ht.1.le, by linarith [ht.2]⟩
    have hδ : 2 * R * t ∈ Ioo (0 : ℝ) R := by
      constructor
      · exact mul_pos (by positivity) ht.1
      · nlinarith [mul_pos hR (sub_pos.mpr ht.2)]
    have hu : (u : ℝ) = (2 * R * t) / (2 * R) := by
      dsimp [u]
      field_simp
    have hh := (radial_contraction_of_chosen_isometries_intrinsic_8_buffer
      hcurves p hR hlocal hq hδ u hu γ hγ hγ0 hγend).2 x y
    have hxt : dist q x.val * t ∈ Icc (0 : ℝ) (dist q x.val) :=
      ⟨mul_nonneg dist_nonneg ht.1.le, mul_le_of_le_one_right dist_nonneg (by linarith [ht.2])⟩
    have hyt : dist q y.val * t ∈ Icc (0 : ℝ) (dist q y.val) :=
      ⟨mul_nonneg dist_nonneg ht.1.le, mul_le_of_le_one_right dist_nonneg (by linarith [ht.2])⟩
    rw [IccExtend_of_mem dist_nonneg (γ x) hxt, IccExtend_of_mem dist_nonneg (γ y) hyt]
    apply (le_div_iff₀ ht.1).mpr
    have hmul : (2 * R / sinh (2 * R) * dist x.val y.val) * t =
        (2 * R * t / sinh (2 * R)) * dist x.val y.val := by ring
    rw [hmul]
    simpa only [u, mul_comm t] using hh
  have hbound := ge_of_tendsto hlim hevent
  have hsinh : 0 < sinh (2 * R) := sinh_pos_iff.mpr (by positivity)
  change dist x.val y.val ≤ (sinh (2 * R) / (2 * R)) * _
  have hh := mul_le_mul_of_nonneg_left hbound (div_nonneg hsinh.le (by positivity : 0 ≤ 2 * R))
  have hcancel : (sinh (2 * R) / (2 * R)) *
      ((2 * R / sinh (2 * R)) * dist x.val y.val) = dist x.val y.val := by
    field_simp
  rwa [hcancel] at hh

theorem dimH_closedBall_le_tangent_of_intrinsic_8_buffer
    {q : X} (hq : q ∈ ball p (R / 2)) :
    letI : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
      (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
      (by change dist q p < 8 * R; have hh : dist q p < R / 2 := hq; linarith)
    dimH (closedBall p R) ≤ dimH (univ : Set (TangentCone q)) := by
  let : HasAnglesAt q := hasAnglesAt_of_intrinsic_ball_local_comparison hcurves p
    (by positivity : 0 < 8 * R) (by norm_num : (0 : ℝ) ≤ 1) hlocal
    (by change dist q p < 8 * R; have hh : dist q p < R / 2 := hq; linarith)
  classical
  have hsegments (x : closedBall p R) :
      ∃ γ : Icc (0 : ℝ) (dist q (x : X)) → X, Isometry γ ∧
        γ ⟨0, le_rfl, dist_nonneg⟩ = q ∧
        γ ⟨dist q (x : X), dist_nonneg, le_rfl⟩ = x := by
    obtain ⟨f, _, hf0, hf1, _, hfd⟩ := exists_radial_metric_segment_in_two_ball
      hcurves p hR (L := 8 * R) (by linarith) hq x.property
    exact exists_isometric_segment_of_dist_eq_mul hf0 hf1 hfd
  choose γ hγ hγ0 hγend using hsegments
  have hlog := antilipschitz_segmentLog_of_chosen_isometries_intrinsic_8_buffer
    hcurves p hR hlocal hq γ hγ hγ0 hγend
  have hdim := (hlog.le_dimH_image (univ : Set (closedBall p R))).trans
    (dimH_mono (subset_univ _))
  have heq : dimH (univ : Set (closedBall p R)) = dimH (closedBall p R) := by
    simpa only [image_univ, Subtype.range_coe] using
      (isometry_subtype_coe.dimH_image (univ : Set (closedBall p R))).symm
  rwa [heq] at hdim

end DifferentialGeometry.Geometry.Comparison.Toponogov
