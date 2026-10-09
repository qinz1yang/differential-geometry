import DifferentialGeometry.Geometry.Metric.Approximation.BoundedDiameterLimit

/-! A concrete entire interval factor exercises compact pointed-product limit extraction. -/

set_option autoImplicit false

open Set Metric Filter
open scoped Topology

namespace GC.MetricGeometry.CompactFactorExamples

abbrev UnitInterval := Icc (0 : ℝ) 1

def intervalPoint : UnitInterval := ⟨0, by norm_num⟩

def intervalProductPoint : WithLp 2 (ℝ × UnitInterval) :=
  WithLp.toLp 2 ((0 : ℝ), intervalPoint)

def intervalProductApprox (i : ℕ) : KleinerLottApprox intervalProductPoint
    intervalProductPoint (1 / ((i : ℝ) + 2)) where
  error_pos := by positivity
  error_lt_one := by
    apply (div_lt_one (by positivity : (0 : ℝ) < (i : ℝ) + 2)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) i]
  toFun := id
  basepoint := rfl
  distortion x hx y hy := by
    simp only [id_eq, sub_self, abs_zero]
    positivity
  coverage y hy := by
    have hδ : 0 < (1 : ℝ) / ((i : ℝ) + 2) := by positivity
    have hball : y ∈ ball intervalProductPoint (1 / ((i : ℝ) + 2))⁻¹ := by
      exact hy.trans (sub_lt_self (1 / ((i : ℝ) + 2))⁻¹ hδ)
    have himage : y ∈ id '' ball intervalProductPoint (1 / ((i : ℝ) + 2))⁻¹ :=
      ⟨y, hball, rfl⟩
    exact (infDist_le_dist_of_mem himage).trans (by simpa using hδ.le)

theorem interval_distance_bound (x y : UnitInterval) : dist x y ≤ 1 := by
  change |x.val - y.val| ≤ 1
  exact abs_le.mpr ⟨by linarith [x.property.1, y.property.2],
    by linarith [y.property.1, x.property.2]⟩

theorem interval_product_has_compact_pointed_factor :
    ∃ (W : Type) (m : MetricSpace W), letI := m
      ∃ (w : W) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace W ∧ CompleteSpace W ∧
        CompactSpace W ∧ (∀ x y : W, dist x y ≤ 1) ∧
        PointedGHConverges (fun _index => intervalPoint) w ∧
        PointedGHConverges (fun _index => intervalProductPoint) intervalProductPoint ∧
        ∃ e : WithLp 2 (ℝ × UnitInterval) ≃ᵢ WithLp 2 (ℝ × W),
          e intervalProductPoint = WithLp.toLp 2 ((0 : ℝ), w) := by
  have hδ : Tendsto (fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 2)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  exact PointedGHConverges.exists_compact_factor_of_approximate_products
    (PointedGHConverges.const intervalProductPoint) intervalProductApprox hδ
      (fun i => interval_distance_bound)

end GC.MetricGeometry.CompactFactorExamples
