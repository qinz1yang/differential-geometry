import DifferentialGeometry.Geometry.Coordinates.Frame.TangentProduct
import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.Euclidean
import Mathlib.Tactic.Linarith

open Bundle Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.SmoothRiemannianMetric

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

theorem prod_chart_norm_comparison
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (p : M × N) {q : M × N}
    (hq : q ∈ (trivializationAt (E × F) (TangentSpace (I.prod J)) p).baseSet)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hg : ∀ v : TangentSpace I q.1,
      Real.sqrt (g.inner q.1 v v) ≤
        C * ‖(trivializationAt E (TangentSpace I) p.1).continuousLinearMapAt ℝ q.1 v‖ ∧
      ‖(trivializationAt E (TangentSpace I) p.1).continuousLinearMapAt ℝ q.1 v‖ ≤
        C * Real.sqrt (g.inner q.1 v v))
    (hh : ∀ v : TangentSpace J q.2,
      Real.sqrt (h.inner q.2 v v) ≤
        D * ‖(trivializationAt F (TangentSpace J) p.2).continuousLinearMapAt ℝ q.2 v‖ ∧
      ‖(trivializationAt F (TangentSpace J) p.2).continuousLinearMapAt ℝ q.2 v‖ ≤
        D * Real.sqrt (h.inner q.2 v v))
    (v : TangentSpace (I.prod J) q) :
    Real.sqrt ((g.prod h).inner q v v) ≤ (C + D) *
      ‖(trivializationAt (E × F) (TangentSpace (I.prod J)) p).continuousLinearMapAt ℝ q v‖ ∧
    ‖(trivializationAt (E × F) (TangentSpace (I.prod J)) p).continuousLinearMapAt ℝ q v‖ ≤
      (C + D) * Real.sqrt ((g.prod h).inner q v v) := by
  rw [prod_inner, trivializationAt_continuousLinearMapAt_prod_of_mem p hq v, Prod.norm_def]
  let a := g.inner q.1 v.1 v.1
  let b := h.inner q.2 v.2 v.2
  have ha : 0 ≤ a := metric_inner_self_nonneg g q.1 v.1
  have hb : 0 ≤ b := metric_inner_self_nonneg h q.2 v.2
  have hab : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), ?_⟩
    nlinarith only [Real.sq_sqrt ha, Real.sq_sqrt hb,
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  have hma := le_max_left
    ‖(trivializationAt E (TangentSpace I) p.1).continuousLinearMapAt ℝ q.1 v.1‖
    ‖(trivializationAt F (TangentSpace J) p.2).continuousLinearMapAt ℝ q.2 v.2‖
  have hmb := le_max_right
    ‖(trivializationAt E (TangentSpace I) p.1).continuousLinearMapAt ℝ q.1 v.1‖
    ‖(trivializationAt F (TangentSpace J) p.2).continuousLinearMapAt ℝ q.2 v.2‖
  refine ⟨hab.trans ?_, max_le ?_ ?_⟩
  · exact (add_le_add (hg v.1).1 (hh v.2).1).trans (by
      nlinarith only [mul_le_mul_of_nonneg_left hma hC, mul_le_mul_of_nonneg_left hmb hD])
  · exact (hg v.1).2.trans ((mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (le_add_of_nonneg_right hb)) hC).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD) (Real.sqrt_nonneg (a + b))))
  · exact (hh v.2).2.trans ((mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (le_add_of_nonneg_left ha)) hD).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (Real.sqrt_nonneg (a + b))))

theorem prod_euclidean_chart_norm_comparison
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (g : SmoothRiemannianMetric I M) (p : M × V) {q : M × V}
    (hq : q.1 ∈ (trivializationAt E (TangentSpace I) p.1).baseSet)
    {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ v : TangentSpace I q.1,
      Real.sqrt (g.inner q.1 v v) ≤
        C * ‖(trivializationAt E (TangentSpace I) p.1).continuousLinearMapAt ℝ q.1 v‖ ∧
      ‖(trivializationAt E (TangentSpace I) p.1).continuousLinearMapAt ℝ q.1 v‖ ≤
        C * Real.sqrt (g.inner q.1 v v))
    (v : TangentSpace (I.prod 𝓘(ℝ, V)) q) :
    Real.sqrt ((g.prod (euclideanMetric (E := V))).inner q v v) ≤ (C + 1) *
      ‖(trivializationAt (E × V) (TangentSpace (I.prod 𝓘(ℝ, V))) p).continuousLinearMapAt ℝ q v‖ ∧
    ‖(trivializationAt (E × V) (TangentSpace (I.prod 𝓘(ℝ, V))) p).continuousLinearMapAt ℝ q v‖ ≤
      (C + 1) * Real.sqrt ((g.prod (euclideanMetric (E := V))).inner q v v) := by
  have hprod : q ∈ (trivializationAt (E × V) (TangentSpace (I.prod 𝓘(ℝ, V))) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, prodChartedSpace_chartAt,
      OpenPartialHomeomorph.prod_source, mem_prod, chartAt_self_eq,
      OpenPartialHomeomorph.refl_source, mem_univ, and_true] using hq
  apply prod_chart_norm_comparison g euclideanMetric p hprod hC zero_le_one hg
  have hh (y u : V) : Real.sqrt ((euclideanMetric (E := V)).inner y u u) ≤ 1 * ‖u‖ ∧
      ‖u‖ ≤ 1 * Real.sqrt ((euclideanMetric (E := V)).inner y u u) := by
    change Real.sqrt (inner ℝ u u) ≤ 1 * ‖u‖ ∧ ‖u‖ ≤ 1 * Real.sqrt (inner ℝ u u)
    simp only [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg u), one_mul, le_refl, and_self]
  intro w
  rw [TangentBundle.continuousLinearMapAt_model_space]
  exact hh q.2 w

end DifferentialGeometry.SmoothRiemannianMetric
