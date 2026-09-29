import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle

open Filter Set Topology

noncomputable section

namespace DifferentialGeometry.Toponogov

export DifferentialGeometry.Geometry.Comparison.Toponogov
  (comparisonCosine comparisonAngle metricComparisonAngle)

theorem comparisonAngle_mem_Icc (a b c : ℝ) : comparisonAngle a b c ∈ Icc 0 Real.pi :=
  Geometry.Comparison.Toponogov.comparisonAngle_mem_Icc a b c

theorem comparisonCosine_mem_Icc {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hca : |a - b| ≤ c) (hac : c ≤ a + b) : comparisonCosine a b c ∈ Icc (-1) 1 :=
  Geometry.Comparison.Toponogov.comparison_cosine_mem_Icc ha hb hca hac

theorem cos_comparisonAngle {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hca : |a - b| ≤ c) (hac : c ≤ a + b) :
    Real.cos (comparisonAngle a b c) = comparisonCosine a b c :=
  Geometry.Comparison.Toponogov.cos_comparisonAngle ha hb hca hac

theorem comparisonCosine_scale {a b c scale : ℝ} (hscale : scale ≠ 0) :
    comparisonCosine (scale * a) (scale * b) (scale * c) = comparisonCosine a b c :=
  Geometry.Comparison.Toponogov.comparisonCosine_scale hscale

theorem comparisonAngle_scale {a b c scale : ℝ} (hscale : 0 < scale) :
    comparisonAngle (scale * a) (scale * b) (scale * c) = comparisonAngle a b c :=
  Geometry.Comparison.Toponogov.comparisonAngle_scale a b c hscale

theorem comparisonCosine_comm (a b c : ℝ) :
    comparisonCosine a b c = comparisonCosine b a c :=
  Geometry.Comparison.Toponogov.comparisonCosine_comm a b c

theorem comparisonAngle_comm (a b c : ℝ) :
    comparisonAngle a b c = comparisonAngle b a c :=
  Geometry.Comparison.Toponogov.comparisonAngle_comm a b c

theorem comparisonSideInequalities_limit {a b c : ℕ → ℝ} {a₀ b₀ c₀ : ℝ}
    (ha : Tendsto a atTop (nhds a₀)) (hb : Tendsto b atTop (nhds b₀))
    (hc : Tendsto c atTop (nhds c₀)) (hca : ∀ j, |a j - b j| ≤ c j)
    (hac : ∀ j, c j ≤ a j + b j) : |a₀ - b₀| ≤ c₀ ∧ c₀ ≤ a₀ + b₀ :=
  Geometry.Comparison.Toponogov.comparison_triangle_limits ha hb hc
    (Eventually.of_forall fun j => ⟨hca j, hac j⟩)

theorem comparisonAngle_tendsto {a b c : ℕ → ℝ} {a₀ b₀ c₀ : ℝ}
    (ha : Tendsto a atTop (nhds a₀)) (hb : Tendsto b atTop (nhds b₀))
    (hc : Tendsto c atTop (nhds c₀)) (ha₀ : 0 < a₀) (hb₀ : 0 < b₀) :
    Tendsto (fun j ↦ comparisonAngle (a j) (b j) (c j)) atTop
      (nhds (comparisonAngle a₀ b₀ c₀)) :=
  Geometry.Comparison.Toponogov.tendsto_comparisonAngle ha hb hc ha₀ hb₀

theorem comparisonAngle_tendsto_of_sideInequalities {a b c : ℕ → ℝ} {a₀ b₀ c₀ : ℝ}
    (ha : Tendsto a atTop (nhds a₀)) (hb : Tendsto b atTop (nhds b₀))
    (hc : Tendsto c atTop (nhds c₀))
    (hca : ∀ j, |a j - b j| ≤ c j) (hac : ∀ j, c j ≤ a j + b j)
    (ha₀ : 0 < a₀) (hb₀ : 0 < b₀) :
    (|a₀ - b₀| ≤ c₀ ∧ c₀ ≤ a₀ + b₀) ∧
      Tendsto (fun j ↦ comparisonAngle (a j) (b j) (c j)) atTop
        (nhds (comparisonAngle a₀ b₀ c₀)) :=
  ⟨comparisonSideInequalities_limit ha hb hc hca hac,
    comparisonAngle_tendsto ha hb hc ha₀ hb₀⟩

theorem comparisonAngle_abs_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    comparisonAngle a b |a - b| = 0 :=
  Geometry.Comparison.Toponogov.comparisonAngle_abs_sub ha hb

theorem comparisonAngle_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    comparisonAngle a b (a + b) = Real.pi :=
  Geometry.Comparison.Toponogov.comparisonAngle_add ha hb

theorem metricComparisonAngle_sideInequalities {X : Type*} [PseudoMetricSpace X] (x o y : X) :
    |dist o x - dist o y| ≤ dist x y ∧ dist x y ≤ dist o x + dist o y :=
  Geometry.Comparison.Toponogov.metricComparisonAngle_sideInequalities x o y

theorem metricComparisonCosine_mem_Icc {X : Type*} [MetricSpace X] {x o y : X}
    (hxo : x ≠ o) (hyo : y ≠ o) :
    comparisonCosine (dist o x) (dist o y) (dist x y) ∈ Icc (-1) 1 :=
  comparisonCosine_mem_Icc (dist_pos.mpr hxo.symm) (dist_pos.mpr hyo.symm)
    (metricComparisonAngle_sideInequalities x o y).1
    (metricComparisonAngle_sideInequalities x o y).2

theorem cos_metricComparisonAngle {X : Type*} [MetricSpace X] {x o y : X}
    (hxo : x ≠ o) (hyo : y ≠ o) :
    Real.cos (metricComparisonAngle x o y) =
      comparisonCosine (dist o x) (dist o y) (dist x y) :=
  Geometry.Comparison.Toponogov.cos_metricComparisonAngle hxo hyo

@[simp] theorem metricComparisonAngle_self {X : Type*} [MetricSpace X] {x o : X}
    (hxo : x ≠ o) : metricComparisonAngle x o x = 0 := by
  have hpos : 0 < dist o x := dist_pos.mpr hxo.symm
  simpa only [metricComparisonAngle, dist_self, sub_self, abs_zero] using
    (comparisonAngle_abs_sub hpos hpos)

end DifferentialGeometry.Toponogov
