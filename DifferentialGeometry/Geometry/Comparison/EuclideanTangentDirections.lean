import DifferentialGeometry.Geometry.Metric.TangentCone
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal RealInnerProductSpace
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace Metric.TangentCone

variable {X E : Type*} [MetricSpace X] {p : X} [HasAnglesAt p]
    [NormedAddCommGroup E]

theorem norm_isometryEquiv (e : TangentCone p ≃ᵢ E) (he : e EuclideanCone.tip = 0)
    (x : TangentCone p) : ‖e x‖ = EuclideanCone.radius x := by
  have h := e.dist_eq x EuclideanCone.tip
  rwa [he, dist_zero_right, EuclideanCone.dist_tip] at h

def unitVector (e : TangentCone p ≃ᵢ E) (he : e EuclideanCone.tip = 0)
    (v : SpaceOfDirections p) : {x : E // ‖x‖ = 1} :=
  ⟨e (EuclideanCone.mk 1 v), by rw [norm_isometryEquiv e he, EuclideanCone.radius_mk]; rfl⟩

variable [InnerProductSpace ℝ E]

theorem angle_unitVector (e : TangentCone p ≃ᵢ E) (he : e EuclideanCone.tip = 0)
    (v w : SpaceOfDirections p) :
    InnerProductGeometry.angle (unitVector e he v).val (unitVector e he w).val = dist v w := by
  have hdist := e.dist_eq (EuclideanCone.mk 1 v) (EuclideanCone.mk 1 w)
  rw [EuclideanCone.dist_mk] at hdist
  have hs := coneDistance_sq (x := ((1 : ℝ), v)) (y := ((1 : ℝ), w))
    (by norm_num) (by norm_num)
  rw [min_eq_right (SpaceOfDirections.dist_le_pi v w)] at hs
  have hnorm := norm_sub_pow_two_real (unitVector e he v).val (unitVector e he w).val
  rw [(unitVector e he v).property, (unitVector e he w).property] at hnorm
  have hdist' : ‖(unitVector e he v).val - (unitVector e he w).val‖ =
      coneDistance ((1 : ℝ), v) ((1 : ℝ), w) := by
    simpa only [unitVector, dist_eq_norm, NNReal.coe_one] using hdist
  rw [hdist'] at hnorm
  have hi : inner ℝ (unitVector e he v).val (unitVector e he w).val = Real.cos (dist v w) := by
    nlinarith
  rw [InnerProductGeometry.angle, (unitVector e he v).property,
    (unitVector e he w).property, mul_one, div_one, hi]
  exact Real.arccos_cos dist_nonneg (SpaceOfDirections.dist_le_pi v w)

omit [InnerProductSpace ℝ E] in
theorem surjective_unitVector (e : TangentCone p ≃ᵢ E) (he : e EuclideanCone.tip = 0) :
    Function.Surjective (unitVector e he) := by
  intro v
  let x := e.symm v.val
  have hx : EuclideanCone.radius x = 1 := by
    rw [← norm_isometryEquiv e he, show e x = v.val from e.apply_symm_apply _]
    exact v.property
  have hxtip : x ≠ EuclideanCone.tip := by
    intro h
    rw [h, EuclideanCone.radius_tip] at hx
    norm_num at hx
  obtain ⟨r, u, hxu⟩ := EuclideanCone.exists_positive_of_ne_tip hxtip
  have hr : (r : ℝ) = 1 := by simpa only [hxu, EuclideanCone.radius_some] using hx
  refine ⟨u, Subtype.ext ?_⟩
  change e (EuclideanCone.mk 1 u) = v.val
  have hm : EuclideanCone.mk 1 u = x := by
    rw [hxu, EuclideanCone.mk_pos (show (0 : ℝ) < (1 : ℝ≥0) by norm_num)]
    congr 2
    exact Subtype.ext hr.symm
  rw [hm]
  exact e.apply_symm_apply _

theorem exists_representative_angle_lt (e : TangentCone p ≃ᵢ E)
    (he : e EuclideanCone.tip = 0) (v : E) (hv : ‖v‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ σ : GeodesicRepresentative p,
      InnerProductGeometry.angle v (unitVector e he σ.direction).val < ε := by
  obtain ⟨u, hu⟩ := surjective_unitVector e he ⟨v, hv⟩
  obtain ⟨σ, hσ⟩ := u.exists_representative_dist_lt hε
  refine ⟨σ, ?_⟩
  have hval := congrArg Subtype.val hu
  change (unitVector e he u).val = v at hval
  rw [← hval, angle_unitVector]
  exact hσ

end Metric.TangentCone
