import DifferentialGeometry.Geometry.Comparison.Toponogov.HyperbolicComparisonAngle

set_option autoImplicit false
open Filter
open scoped Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem exists_hyperbolic_comparison_cosine_tolerance {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ k a b c : ℝ,
      0 < k → 0 < a → 0 < b → |a - b| ≤ c → c ≤ a + b →
      k * max a b < δ →
      |hyperbolicComparisonCosine k a b c - comparisonCosine a b c| < ε := by
  let T := {p : ℝ × ℝ × ℝ × ℝ // 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2.1 ∧
    |p.2.1 - p.2.2.1| ≤ p.2.2.2 ∧ p.2.2.2 ≤ p.2.1 + p.2.2.1}
  let scale : T → ℝ := fun p => p.val.1 * max p.val.2.1 p.val.2.2.1
  let l : Filter T := Filter.comap scale (𝓝 0)
  have hlim := tendsto_hyperbolic_comparison_cosine_sub_euclidean
    (l := l) (k := fun p => p.val.1) (a := fun p => p.val.2.1)
    (b := fun p => p.val.2.2.1) (c := fun p => p.val.2.2.2)
    (Eventually.of_forall fun p => p.property) (show Tendsto scale l (𝓝 0) from tendsto_comap)
  have hevent : ∀ᶠ p in l, |hyperbolicComparisonCosine p.val.1 p.val.2.1 p.val.2.2.1 p.val.2.2.2 -
      comparisonCosine p.val.2.1 p.val.2.2.1 p.val.2.2.2| < ε := by
    simpa only [Real.dist_eq, sub_zero, hyperbolicComparisonCosine, comparisonCosine] using
      Metric.tendsto_nhds.mp hlim ε hε
  obtain ⟨S, hS, hsub⟩ := hevent
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨δ, hδ, ?_⟩
  intro k a b c hk ha hb hlow hupp hsmall
  let p : T := ⟨(k, a, b, c), hk, ha, hb, hlow, hupp⟩
  apply hsub (a := p)
  apply hball
  change dist (k * max a b) 0 < δ
  simpa only [Real.dist_eq, sub_zero, abs_of_pos (mul_pos hk (lt_of_lt_of_le ha (le_max_left _ _)))]
    using hsmall

end DifferentialGeometry.Geometry.Comparison.Toponogov
