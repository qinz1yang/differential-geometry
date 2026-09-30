import DifferentialGeometry.Topology.MetricSpace.PseudometricLimit
import DifferentialGeometry.Topology.MetricSpace.ProperRadialImage
import DifferentialGeometry.Geometry.Metric.RadialConeQuotient
import DifferentialGeometry.Geometry.Metric.Approximation.CompactParameterMaps
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open Set Metric Filter
open scoped Topology NNReal
open GC.MetricGeometry

namespace ConeRegression

private noncomputable def c (R : ℝ) : ℝ := (max R 0 + 1)⁻¹
@[instance_reducible]
private noncomputable def m (R : ℝ) : PseudoMetricSpace ℝ :=
  PseudoMetricSpace.induced (fun x : ℝ => c R * x) inferInstance

private theorem c_pos (R : ℝ) : 0 < c R := by
  dsimp [c]
  positivity

private theorem m_dist (R x y : ℝ) : @dist ℝ (m R).toDist x y = c R * dist x y := by
  change |c R * x - c R * y| = c R * |x - y|
  rw [← mul_sub, abs_mul, abs_of_pos (c_pos R)]

theorem uniform_real_scale_collapse :
    TendstoUniformlyOn (fun R (xy : ℝ × ℝ) => @dist ℝ (m R).toDist xy.1 xy.2)
      (fun _ => (0 : ℝ)) atTop ((Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) := by
  have hc : Tendsto c atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    exact tendsto_atTop_add_const_right _ 1
      (tendsto_atTop_mono (fun R : ℝ => le_max_left R 0) tendsto_id)
  apply Metric.tendstoUniformlyOn_dist_of_dominated_antitone m (fun _ _ => 0)
    (hs := isCompact_Icc)
  · intro R x y
    rw [m_dist]
    have hc1 : c R ≤ 1 := by
      dsimp [c]
      apply (inv_le_one₀ (by positivity)).mpr
      linarith [le_max_right R (0 : ℝ)]
    exact mul_le_of_le_one_left dist_nonneg hc1
  · intro x y R S hRS
    dsimp only
    rw [m_dist, m_dist]
    apply mul_le_mul_of_nonneg_right _ dist_nonneg
    exact (inv_le_inv₀ (by positivity) (by positivity)).mpr
      (by linarith [max_le_max hRS (le_refl (0 : ℝ))])
  · intro x y
    simpa only [m_dist, zero_mul] using hc.mul_const (dist x y)

private structure TwoSidedRay where
  value : ℝ

private noncomputable instance : PseudoMetricSpace TwoSidedRay :=
  PseudoMetricSpace.induced (fun x : TwoSidedRay => |x.value|) inferInstance

private def dilation (t : ℝ≥0) (x : TwoSidedRay) : TwoSidedRay := ⟨t * x.value⟩

private theorem dilation_sq (s t : ℝ≥0) (x y : TwoSidedRay) :
    dist (dilation s x) (dilation t y) ^ 2 =
      (s : ℝ) ^ 2 * dist (⟨0⟩ : TwoSidedRay) x ^ 2 +
      (t : ℝ) ^ 2 * dist (⟨0⟩ : TwoSidedRay) y ^ 2 -
      (s : ℝ) * (t : ℝ) *
        (dist (⟨0⟩ : TwoSidedRay) x ^ 2 + dist (⟨0⟩ : TwoSidedRay) y ^ 2 - dist x y ^ 2) := by
  change (abs (abs ((s : ℝ) * x.value) - abs ((t : ℝ) * y.value))) ^ 2 =
    (s : ℝ) ^ 2 * (abs (abs (0 : ℝ) - abs x.value)) ^ 2 +
      (t : ℝ) ^ 2 * (abs (abs (0 : ℝ) - abs y.value)) ^ 2 -
      (s : ℝ) * (t : ℝ) *
        ((abs (abs (0 : ℝ) - abs x.value)) ^ 2 + (abs (abs (0 : ℝ) - abs y.value)) ^ 2 -
          (abs (abs x.value - abs y.value)) ^ 2)
  simp only [abs_mul, abs_of_nonneg s.coe_nonneg, abs_of_nonneg t.coe_nonneg, sq_abs, abs_zero]
  ring

theorem radial_quotient_collapses_opposite_points :
    ∃ H : RadialConeData (SeparationQuotient.mk (⟨0⟩ : TwoSidedRay)),
      H.map 2 (SeparationQuotient.mk (⟨1⟩ : TwoSidedRay)) =
        SeparationQuotient.mk (⟨2⟩ : TwoSidedRay) ∧
      SeparationQuotient.mk (⟨1⟩ : TwoSidedRay) = SeparationQuotient.mk (⟨-1⟩ : TwoSidedRay) := by
  let H := radialConeDataSeparationQuotient (⟨0⟩ : TwoSidedRay) dilation
    (by intro x; simp [dilation]) (by intro x; simp [dilation]) dilation_sq
  refine ⟨H, ?_, ?_⟩
  · change SeparationQuotient.mk (⟨(2 : ℝ) * 1⟩ : TwoSidedRay) = _
    norm_num
  · apply dist_eq_zero.mp
    rw [SeparationQuotient.dist_mk]
    change dist |(1 : ℝ)| |(-1 : ℝ)| = 0
    norm_num

theorem proper_absolute_value_image : ProperSpace ℝ≥0 := by
  let f : ℝ → ℝ≥0 := fun x => ⟨|x|, abs_nonneg x⟩
  refine ProperSpace.of_surjective_dist_basepoint_eq f
    (continuous_abs.subtype_mk _) ?_ (0 : ℝ) ?_
  · intro r
    refine ⟨r.val, Subtype.ext ?_⟩
    exact abs_of_nonneg r.property
  · intro x
    change dist |x| |(0 : ℝ)| = dist x (0 : ℝ)
    simp only [Real.dist_eq, abs_zero, sub_zero, abs_abs]

theorem repeated_parameters_exact_coverage :
    ∃ f : ℝ → ℝ, (∀ x, |f x| ≤ 2) ∧ ∀ x, |x| ≤ 2 → f x = x := by
  let Z := Icc (-2 : ℝ) 2 × Bool
  let Γ : Z → ℝ := fun z => z.1.val
  let z₀ : Z := (⟨0, by norm_num⟩, false)
  have hcompact : Continuous Γ := continuous_subtype_val.comp continuous_fst
  have hparam (z : Z) : Γ z ∈ closedBall (Γ z₀) 2 := by
    change dist z.1.val (0 : ℝ) ≤ 2
    rw [Real.dist_eq, sub_zero, abs_le]
    exact z.1.property
  have hrange (x : ℝ) (hx : x ∈ closedBall (Γ z₀) 2) : ∃ z : Z, Γ z = x := by
    have hx' : x ∈ Icc (-2 : ℝ) 2 := by
      change |x - 0| ≤ 2 at hx
      simpa only [sub_zero, abs_le, mem_Icc] using hx
    exact ⟨(⟨x, hx'⟩, false), rfl⟩
  obtain ⟨f, _, hfix, himage, _, _⟩ := exists_onto_ball_map_of_compact_parameters
    Γ Γ hcompact z₀ (β := 0) (ω := 0) (fun _ => rfl) hparam hrange
    (fun _ _ => le_rfl) (fun _ _ => by simp) (fun x hx => by
      obtain ⟨z, hz⟩ := hrange x hx
      rw [infDist_zero_of_mem (show x ∈ range Γ from ⟨z, hz⟩)])
  refine ⟨f, ?_, ?_⟩
  · intro x
    simpa only [mem_closedBall, Γ, z₀, Real.dist_eq, sub_zero] using himage x
  · intro x hx
    obtain ⟨z, hz⟩ := hrange x (by simpa only [mem_closedBall, Γ, z₀, Real.dist_eq, sub_zero] using hx)
    rw [← hz]
    exact hfix z

#print axioms uniform_real_scale_collapse
#print axioms radial_quotient_collapses_opposite_points
#print axioms proper_absolute_value_image
#print axioms repeated_parameters_exact_coverage
end ConeRegression
