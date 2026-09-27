import DifferentialGeometry.Geometry.Measure.Area.LeastAreaMetric
import DifferentialGeometry.Geometry.Measure.Area.LeastAreaContinuity
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



theorem leastSpanningArea_metric_relative_error
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlo : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), (1 - δ) * g.inner x v v ≤ h.inner x v v)
    (hhi : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), h.inner x v v ≤ (1 + δ) * g.inner x v v)
    (γ : lipschitzContractibleLoop g) (σ : lipschitzContractibleLoop h) (htrace : γ.val = σ.val) :
    |leastSpanningArea h σ - leastSpanningArea g γ| ≤ δ * leastSpanningArea g γ := by
  have hpos : 0 < 1 - δ := sub_pos.mpr hδ1
  have hu := leastSpanningArea_metric_upper g h (by positivity : 0 < 1 + δ) hhi γ σ htrace
  have hl := leastSpanningArea_metric_upper h g (inv_pos.mpr hpos)
    (metric_lower_inverse_upper g h hpos hlo) σ γ htrace.symm
  rw [← div_eq_inv_mul] at hl
  have hl' := (le_div_iff₀ hpos).mp hl
  rw [abs_le]
  constructor <;> nlinarith


theorem regularLeastArea_metric_relative_error
    (g h : SmoothRiemannianMetric 𝓘(ℝ, E) M) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hlo : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), (1 - δ) * g.inner x v v ≤ h.inner x v v)
    (hhi : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x), h.inner x v v ≤ (1 + δ) * g.inner x v v)
    (γ : regularContractibleLoop E M) :
    |regularLeastArea h γ - regularLeastArea g γ| ≤ δ * regularLeastArea g γ :=
  leastSpanningArea_metric_relative_error g h hδ hδ1 hlo hhi
    (regularContractibleToLipschitz g γ) (regularContractibleToLipschitz h γ) rfl




theorem continuous_regularLeastArea_metric_loop_family {T : Type*} [TopologicalSpace T]
    (G : T → SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hG : Continuous (fun p : T × TangentBundle 𝓘(ℝ, E) M =>
      (G p.1).inner p.2.proj p.2.2 p.2.2))
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (Γ : T → regularContractibleLoop E M)
    (hΓ : Continuous[inferInstance, regularContractibleLoopTopology e
      (he.of_le (by exact_mod_cast le_top))] Γ) :
    Continuous (fun t => regularLeastArea (G t) (Γ t)) := by
  let : TopologicalSpace (regularContractibleLoop E M) :=
    regularContractibleLoopTopology e (he.of_le (by exact_mod_cast le_top))
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A := regularLeastArea (G t₀) (Γ t₀)
  have hA : 0 ≤ A := regularLeastArea_nonneg _ _
  let δ : ℝ := min (1 / 2) (ε / (4 * (A + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδA : δ * (A + 1) < ε / 2 := by
    have hb := (le_div_iff₀ (by positivity : 0 < 4 * (A + 1))).mp
      (min_le_right (1 / 2 : ℝ) (ε / (4 * (A + 1))))
    change δ * (4 * (A + 1)) ≤ ε at hb
    nlinarith
  have hac := (continuous_regularLeastArea (G t₀) e he hemb hi).comp hΓ
  have hnear : ∀ᶠ t in 𝓝 t₀, |regularLeastArea (G t₀) (Γ t) - A| < min 1 (ε / 2) := by
    have ht := Metric.tendsto_nhds.mp (hac.continuousAt (x := t₀)) (min 1 (ε / 2))
      (lt_min zero_lt_one (half_pos hε))
    simpa only [Real.dist_eq, Function.comp_def] using! ht
  filter_upwards [eventually_metric_quad_bounds G hG t₀ hδ, hnear] with t ht hclose
  have herr := regularLeastArea_metric_relative_error (G t₀) (G t) hδ hδ1
    (fun x v => (ht x v).1) (fun x v => (ht x v).2) (Γ t)
  have hsmall : |regularLeastArea (G t₀) (Γ t) - A| < ε / 2 :=
    hclose.trans_le (min_le_right _ _)
  have hbound : regularLeastArea (G t₀) (Γ t) ≤ A + 1 := by
    have hlt := (abs_lt.mp (hclose.trans_le (min_le_left _ _))).2
    linarith
  have herror : |regularLeastArea (G t) (Γ t) - regularLeastArea (G t₀) (Γ t)| < ε / 2 :=
    (herr.trans (mul_le_mul_of_nonneg_left hbound hδ.le)).trans_lt hδA
  rw [Real.dist_eq]
  have htri := abs_add_le (regularLeastArea (G t) (Γ t) - regularLeastArea (G t₀) (Γ t))
    (regularLeastArea (G t₀) (Γ t) - A)
  change |regularLeastArea (G t) (Γ t) - A| < ε
  rw [sub_add_sub_cancel] at htri
  linarith



theorem continuous_regularLeastArea_of_metricFamilySmoothOn
    {D : RealTimeInterval} (G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hG : MetricFamilySmoothOn (I := 𝓘(ℝ, E)) (M := M) D G)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (γ : regularContractibleLoop E M) :
    Continuous (fun t : D.carrier => regularLeastArea (G t) γ) := by
  let : TopologicalSpace (regularContractibleLoop E M) :=
    regularContractibleLoopTopology e (he.of_le (by exact_mod_cast le_top))
  apply continuous_regularLeastArea_metric_loop_family (fun t : D.carrier => G t) ?_
    e he hemb hi (fun _ => γ) continuous_const
  exact metricTimeBundleQuad_cont_of_metricFamilySmoothOn G hG (Subset.refl _)

end DifferentialGeometry.Geometry
