import DifferentialGeometry.Geometry.Metric.TangentCone

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped NNReal

namespace Metric

variable {X : Type*} [MetricSpace X] {q : X} [HasAnglesAt q]

def segmentLog (x : X) (γ : Icc (0 : ℝ) (dist q x) → X)
    (hγ : Isometry γ) (hγ0 : γ ⟨0, le_rfl, dist_nonneg⟩ = q) : TangentCone q := by
  classical
  exact if h : q = x then EuclideanCone.tip else
    (⟨dist q x, dist_pos.mpr h, γ, hγ, hγ0⟩ : GeodesicRepresentative q).tangentVector
      (NNReal.mk (dist q x) dist_nonneg)

theorem segmentLog_radius (x : X) (γ : Icc (0 : ℝ) (dist q x) → X)
    (hγ : Isometry γ) (hγ0 : γ ⟨0, le_rfl, dist_nonneg⟩ = q) :
    EuclideanCone.radius (segmentLog x γ hγ hγ0) = dist q x := by
  classical
  by_cases h : q = x
  · subst x
    simp [segmentLog, EuclideanCone.radius_tip]
  · simp only [segmentLog, dite_eq_right h, GeodesicRepresentative.tangentVector,
      EuclideanCone.radius_mk, NNReal.coe_mk]

theorem segmentLog_self (γ : Icc (0 : ℝ) (dist q q) → X)
    (hγ : Isometry γ) (hγ0 : γ ⟨0, le_rfl, dist_nonneg⟩ = q) :
    segmentLog q γ hγ hγ0 = EuclideanCone.tip := by
  simp [segmentLog]

omit [HasAnglesAt q] in
private theorem segment_dist_base_div_tendsto
    (x : X) (γ : Icc (0 : ℝ) (dist q x) → X)
    (hγ : Isometry γ) (hγ0 : γ ⟨0, le_rfl, dist_nonneg⟩ = q) :
    Tendsto (fun t : ℝ => dist q (IccExtend dist_nonneg γ (dist q x * t)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (dist q x)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  have hm : dist q x * t ∈ Icc (0 : ℝ) (dist q x) :=
    ⟨mul_nonneg dist_nonneg ht.1.le, mul_le_of_le_one_right dist_nonneg ht.2.le⟩
  have he := hγ.dist_IccExtend (show (0 : ℝ) ≤ dist q x from dist_nonneg)
    (show (0 : ℝ) ∈ Icc 0 (dist q x) from ⟨le_rfl, dist_nonneg⟩) hm
  rw [IccExtend_of_mem dist_nonneg γ ⟨le_rfl, dist_nonneg⟩, hγ0,
    zero_sub, abs_neg, abs_of_nonneg hm.1] at he
  rw [he]
  exact (mul_div_cancel_right₀ _ ht.1.ne').symm

theorem dist_div_tendsto_segmentLog
    (x y : X) (γ : Icc (0 : ℝ) (dist q x) → X)
    (τ : Icc (0 : ℝ) (dist q y) → X)
    (hγ : Isometry γ) (hτ : Isometry τ)
    (hγ0 : γ ⟨0, le_rfl, dist_nonneg⟩ = q)
    (hτ0 : τ ⟨0, le_rfl, dist_nonneg⟩ = q) :
    Tendsto (fun t : ℝ =>
      dist (IccExtend dist_nonneg γ (dist q x * t))
        (IccExtend dist_nonneg τ (dist q y * t)) / t)
      (𝓝[>] (0 : ℝ)) (𝓝 (dist (segmentLog x γ hγ hγ0) (segmentLog y τ hτ hτ0))) := by
  classical
  by_cases hx : q = x
  · subst x
    simpa only [dist_self, zero_mul, IccExtend_of_mem dist_nonneg γ
      (show (0 : ℝ) ∈ Icc 0 (dist q q) from ⟨le_rfl, dist_nonneg⟩),
      hγ0, segmentLog_self, EuclideanCone.tip_dist, segmentLog_radius] using
      segment_dist_base_div_tendsto y τ hτ hτ0
  by_cases hy : q = y
  · subst y
    simpa only [dist_self, zero_mul, IccExtend_of_mem dist_nonneg τ
      (show (0 : ℝ) ∈ Icc 0 (dist q q) from ⟨le_rfl, dist_nonneg⟩),
      hτ0, segmentLog_self, EuclideanCone.dist_tip, segmentLog_radius, dist_comm _ q] using
      segment_dist_base_div_tendsto x γ hγ hγ0
  let σ : GeodesicRepresentative q := ⟨dist q x, dist_pos.mpr hx, γ, hγ, hγ0⟩
  let ρ : GeodesicRepresentative q := ⟨dist q y, dist_pos.mpr hy, τ, hτ, hτ0⟩
  simpa only [segmentLog, dite_eq_right hx, dite_eq_right hy, GeodesicRepresentative.path,
    NNReal.coe_mk, σ, ρ] using
    σ.dist_div_tendsto_tangentVector ρ (NNReal.mk (dist q x) dist_nonneg)
      (NNReal.mk (dist q y) dist_nonneg)

end Metric
