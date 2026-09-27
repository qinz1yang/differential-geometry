import DifferentialGeometry.Geometry.Measure.Area.MetricContinuity
import DifferentialGeometry.Geometry.Metric.UniformTensorConvergence



noncomputable section

open Set Filter Function ContinuousMap Manifold DifferentialGeometry
  DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M] [PreconnectedSpace M] {n : ℕ}



theorem tendsto_regularLeastArea_of_metricCPConv
    (G : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hG : MetricCPConvergenceOn (I := 𝓘(ℝ, E)) Set.univ 0 G g g)
    (e : M → EuclideanSpace ℝ (Fin n))
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (hi : ∀ p, Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) e p))
    (Γ : ℕ → regularContractibleLoop E M) (γ : regularContractibleLoop E M)
    (hΓ : Tendsto Γ atTop (@nhds (regularContractibleLoop E M)
      (regularContractibleLoopTopology e (he.of_le (by exact_mod_cast le_top))) γ)) :
    Tendsto (fun j => regularLeastArea (G j) (Γ j)) atTop (𝓝 (regularLeastArea g γ)) := by
  let : TopologicalSpace (regularContractibleLoop E M) :=
    regularContractibleLoopTopology e (he.of_le (by exact_mod_cast le_top))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A := regularLeastArea g γ
  have hA : 0 ≤ A := regularLeastArea_nonneg _ _
  let δ : ℝ := min (1 / 2) (ε / (4 * (A + 1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδA : δ * (A + 1) < ε / 2 := by
    have hb := (le_div_iff₀ (by positivity : 0 < 4 * (A + 1))).mp
      (min_le_right (1 / 2 : ℝ) (ε / (4 * (A + 1))))
    change δ * (4 * (A + 1)) ≤ ε at hb
    nlinarith
  have hac := ((continuous_regularLeastArea g e he hemb hi).continuousAt (x := γ)).tendsto.comp hΓ
  have hnear : ∀ᶠ j in atTop, |regularLeastArea g (Γ j) - A| < min 1 (ε / 2) := by
    have ht := Metric.tendsto_nhds.mp hac (min 1 (ε / 2)) (lt_min zero_lt_one (half_pos hε))
    simpa only [Real.dist_eq, Function.comp_def] using! ht
  filter_upwards [eventually_metric_quad_bounds_of_uniform_convergence G g hG hδ, hnear]
    with j hj hclose
  have herr := regularLeastArea_metric_relative_error g (G j) hδ hδ1
    (fun x v => (hj x v).1) (fun x v => (hj x v).2) (Γ j)
  have hsmall : |regularLeastArea g (Γ j) - A| < ε / 2 := hclose.trans_le (min_le_right _ _)
  have hbound : regularLeastArea g (Γ j) ≤ A + 1 := by
    have hlt := (abs_lt.mp (hclose.trans_le (min_le_left _ _))).2
    linarith
  have herror : |regularLeastArea (G j) (Γ j) - regularLeastArea g (Γ j)| < ε / 2 :=
    (herr.trans (mul_le_mul_of_nonneg_left hbound hδ.le)).trans_lt hδA
  rw [Real.dist_eq]
  have htri := abs_add_le (regularLeastArea (G j) (Γ j) - regularLeastArea g (Γ j))
    (regularLeastArea g (Γ j) - A)
  change |regularLeastArea (G j) (Γ j) - A| < ε
  rw [sub_add_sub_cancel] at htri
  linarith

end DifferentialGeometry.Geometry
