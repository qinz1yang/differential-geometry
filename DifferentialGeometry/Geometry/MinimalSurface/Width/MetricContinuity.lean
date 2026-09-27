import DifferentialGeometry.Geometry.MinimalSurface.Width.Metric
import DifferentialGeometry.Geometry.Metric.FamilyComparison
import DifferentialGeometry.Geometry.Metric.Family.Basic








noncomputable section

open Set Filter Function ContinuousMap Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M] [PreconnectedSpace M] {n : ℕ}



theorem classWidth_metric_relative_error
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlo : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), (1 - δ) * g.inner x v v ≤ h.inner x v v)
    (hhi : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), h.inner x v v ≤ (1 + δ) * g.inner x v v)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (ξ : loopFamilyClass M) :
    |classWidth h e (he.of_le (by exact_mod_cast le_top)) hemb ξ -
      classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb ξ| ≤
        δ * classWidth g e (he.of_le (by exact_mod_cast le_top)) hemb ξ := by
  have hpos : 0 < 1 - δ := sub_pos.mpr hδ1
  have hu := classWidth_metric_upper g h (by positivity : 0 < 1 + δ) hhi e he hemb hi ξ
  have hl := classWidth_metric_upper h g (inv_pos.mpr hpos)
    (metric_lower_inverse_upper g h hpos hlo) e he hemb hi ξ
  rw [← div_eq_inv_mul] at hl
  have hl' := (le_div_iff₀ hpos).mp hl
  rw [abs_le]
  constructor <;> nlinarith



theorem continuous_classWidth_metric_family {T : Type*} [TopologicalSpace T]
    (G : T → SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hG : Continuous (fun p : T × TangentBundle 𝓘(ℝ, E) M =>
      (G p.1).inner p.2.proj p.2.2 p.2.2))
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (ξ : loopFamilyClass M) :
    Continuous (fun t => classWidth (G t) e (he.of_le (by exact_mod_cast le_top)) hemb ξ) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let W := classWidth (G t₀) e (he.of_le (by exact_mod_cast le_top)) hemb ξ
  have hW : 0 ≤ W := classWidth_nonneg (G t₀) e he hemb hi ξ
  let δ : ℝ := min (1 / 2) (ε / (2 * (W + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδW : δ * W < ε := by
    have hb := (le_div_iff₀ (by positivity : 0 < 2 * (W + 1))).mp
      (min_le_right (1 / 2 : ℝ) (ε / (2 * (W + 1))))
    change δ * (2 * (W + 1)) ≤ ε at hb
    nlinarith
  filter_upwards [eventually_metric_quad_bounds G hG t₀ hδ] with t ht
  have hb := classWidth_metric_relative_error (G t₀) (G t) hδ hδ1
    (fun x v => (ht x v).1) (fun x v => (ht x v).2) e he hemb hi ξ
  rw [Real.dist_eq]
  exact hb.trans_lt hδW



theorem continuous_classWidth_of_metricFamilySmoothOn
    {D : RealTimeInterval} (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hG : MetricFamilySmoothOn (I := 𝓘(ℝ, E)) (M := M) D G)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (ξ : loopFamilyClass M) :
    Continuous (fun t : D.carrier =>
      classWidth (G t) e (he.of_le (by exact_mod_cast le_top)) hemb ξ) := by
  apply continuous_classWidth_metric_family (fun t : D.carrier => G t) ?_ e he hemb hi ξ
  exact metricTimeBundleQuad_cont_of_metricFamilySmoothOn G hG (Subset.refl _)

end DifferentialGeometry.Geometry
