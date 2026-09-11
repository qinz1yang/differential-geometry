import DifferentialGeometry.Geometry.Measure.Area.MetricContinuity
import DifferentialGeometry.Geometry.Metric.UniformTensorConvergence



noncomputable section

open Set Filter Function ContinuousMap Manifold DifferentialGeometry
  DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M] [PreconnectedSpace M]



def metricTransferLipschitzLoop (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) : lipschitzContractibleLoop h := by
  let hcomp := metricUniformEquivalentOn_of_compact g h
  let C : ℝ := hcomp.choose
  have hC := hcomp.choose_spec
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC.1
  exact postcomposeLipschitzContractibleLoop g h id (metric_upper_lipschitz g h hCpos
    (fun x v => (hC.2 x (mem_univ x) v).2)) γ

omit [Nonempty M] [PreconnectedSpace M] in
theorem metricTransferLipschitzLoop_val (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ : lipschitzContractibleLoop g) : (metricTransferLipschitzLoop g h γ).val = γ.val := by
  apply Subtype.ext
  rfl



theorem continuous_leastSpanningArea_metric_family {T : Type*} [TopologicalSpace T]
    (G : T → SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hG : Continuous (fun p : T × TangentBundle 𝓘(ℝ, E) M =>
      (G p.1).inner p.2.proj p.2.2 p.2.2))
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : lipschitzContractibleLoop g) :
    Continuous (fun t => leastSpanningArea (G t) (metricTransferLipschitzLoop g (G t) γ)) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A := leastSpanningArea (G t₀) (metricTransferLipschitzLoop g (G t₀) γ)
  have hA : 0 ≤ A := leastSpanningArea_nonneg _ _
  let δ : ℝ := min (1 / 2) (ε / (2 * (A + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδA : δ * A < ε := by
    have hb := (le_div_iff₀ (by positivity : 0 < 2 * (A + 1))).mp
      (min_le_right (1 / 2 : ℝ) (ε / (2 * (A + 1))))
    change δ * (2 * (A + 1)) ≤ ε at hb
    nlinarith
  filter_upwards [eventually_metric_quad_bounds G hG t₀ hδ] with t ht
  have herr := leastSpanningArea_metric_relative_error (G t₀) (G t) hδ hδ1
    (fun x v => (ht x v).1) (fun x v => (ht x v).2)
    (metricTransferLipschitzLoop g (G t₀) γ) (metricTransferLipschitzLoop g (G t) γ)
    ((metricTransferLipschitzLoop_val g (G t₀) γ).trans
      (metricTransferLipschitzLoop_val g (G t) γ).symm)
  rw [Real.dist_eq]
  exact herr.trans_lt hδA



theorem continuous_leastSpanningArea_of_metricFamilySmoothOn
    {D : RealTimeInterval} (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hG : MetricFamilySmoothOn (I := 𝓘(ℝ, E)) (M := M) D G)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : lipschitzContractibleLoop g) :
    Continuous (fun t : D.carrier => leastSpanningArea (G t) (metricTransferLipschitzLoop g (G t) γ)) := by
  apply continuous_leastSpanningArea_metric_family (fun t : D.carrier => G t) ?_ g γ
  exact metricTimeBundleQuad_cont_of_metricFamilySmoothOn G hG (fun _ hx => hx)

end DifferentialGeometry.Geometry
