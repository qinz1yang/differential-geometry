import DifferentialGeometry.Geometry.Metric.SpaceOfDirections
import DifferentialGeometry.Geometry.Metric.EuclideanConeComplete

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace Metric

variable {X : Type*} [MetricSpace X] {p : X}

abbrev TangentCone (p : X) [HasAnglesAt p] := EuclideanCone (SpaceOfDirections p)

variable [HasAnglesAt p]

def GeodesicRepresentative.tangentVector (σ : GeodesicRepresentative p) (r : ℝ≥0) :
    TangentCone p := EuclideanCone.mk r σ.direction

theorem GeodesicRepresentative.dist_tangentVector (σ τ : GeodesicRepresentative p)
    (r s : ℝ≥0) :
    dist (σ.tangentVector r) (τ.tangentVector s) =
      Real.sqrt ((r : ℝ) ^ 2 + (s : ℝ) ^ 2 - 2 * r * s * Real.cos (σ.angle τ)) := by
  rw [tangentVector, tangentVector, EuclideanCone.dist_mk]
  simp only [coneDistance, σ.dist_direction τ, min_eq_right (σ.angle_mem_Icc τ).2]

theorem GeodesicRepresentative.tangentVector_shorten (σ : GeodesicRepresentative p)
    {r : ℝ} (hr : 0 < r) (hle : r ≤ σ.length) (a : ℝ≥0) :
    (σ.shorten hr hle).tangentVector a = σ.tangentVector a := by
  simp only [tangentVector, σ.direction_shorten hr hle]

omit [HasAnglesAt p] in
private theorem dist_base_path_mul_div_tendsto (σ : GeodesicRepresentative p) (a : ℝ≥0) :
    Tendsto (fun t : ℝ => dist p (σ.path ((a : ℝ) * t)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (a : ℝ)) := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have ha : Tendsto (fun t : ℝ => (a : ℝ) * t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hid.const_mul (a : ℝ)
  have hp : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  apply tendsto_const_nhds.congr'
  filter_upwards [hp, ha.eventually (gt_mem_nhds σ.length_pos)] with t ht hsmall
  rw [σ.dist_base_path (t := (a : ℝ) * t) ⟨mul_nonneg a.property ht.le, hsmall.le⟩]
  field_simp

theorem GeodesicRepresentative.dist_div_tendsto_tangentVector
    (σ τ : GeodesicRepresentative p) (r s : ℝ≥0) :
    Tendsto (fun t : ℝ => dist (σ.path ((r : ℝ) * t)) (τ.path ((s : ℝ) * t)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (dist (σ.tangentVector r) (τ.tangentVector s))) := by
  by_cases hr : r = 0
  · subst r
    simpa only [NNReal.coe_zero, zero_mul, σ.path_zero, tangentVector,
      EuclideanCone.mk_zero, EuclideanCone.tip_dist, EuclideanCone.radius_mk] using
      dist_base_path_mul_div_tendsto τ s
  by_cases hs : s = 0
  · subst s
    simpa only [NNReal.coe_zero, zero_mul, τ.path_zero, tangentVector,
      EuclideanCone.mk_zero, EuclideanCone.dist_tip, EuclideanCone.radius_mk, dist_comm _ p] using
      dist_base_path_mul_div_tendsto σ r
  rw [σ.dist_tangentVector τ r s]
  exact dist_div_tendsto_of_joint_comparisonAngle (le_refl 0) σ.length_pos τ.length_pos
    p σ.path τ.path
    (fun _ ht => σ.dist_base_path ⟨ht.1.le, ht.2⟩)
    (fun _ ht => τ.dist_base_path ⟨ht.1.le, ht.2⟩)
    (HasAnglesAt.tendsto_angle σ τ) (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr))
    (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs))

end Metric
