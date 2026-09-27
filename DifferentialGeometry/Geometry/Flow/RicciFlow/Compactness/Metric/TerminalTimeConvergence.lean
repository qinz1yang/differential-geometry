import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.InitialMetricTimeBounds
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Evaluation

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem metricCPConvergenceOn_at_terminal_times_of_finite_ricci_bounds
    (U : Set M) (hU : IsOpen U) (R : SmoothRiemannianMetric I M)
    (N : ℕ) {T Λ K : ℝ} (hT : 0 ≤ T) (hΛ : 1 ≤ Λ) (hK : 0 ≤ K)
    (A : ℕ → ℝ) (hA : ∀ q, 1 ≤ q → q ≤ N → 0 ≤ A q)
    (D : ℕ → RealTimeInterval) (age : ℕ → ℝ)
    (hage : ∀ i, 0 ≤ age i) (hageT : ∀ i, age i ≤ T)
    {b : ℝ} (hb : 0 < b) (hlim : Tendsto age atTop (𝓝 b))
    (hcarrier : ∀ i, Icc 0 (age i) ⊆ (D i).carrier)
    (hregular : ∀ i, Ioo 0 (age i) ⊆ (D i).regular)
    (S : ∀ i, SolutionOn (I := I) (M := M) (D i)) (hS : ∀ i, IsSolutionOn (S i))
    (hgram : ∀ i (x₀ : M) (j k : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          ((S i).base.metric p.1) x₀ p.2 j k)
        (Icc 0 (age i) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hequiv : ∀ i, MetricUniformEquivalentOn U R ((S i).base.metric 0) Λ)
    (hjets : ∀ i q, 1 ≤ q → q ≤ N → ∀ x ∈ U,
      metricCovDerivNorm q ((S i).base.metric 0) R x ≤ A q)
    (hRic : ∀ i, MovingShiBoundOn U 0 (age i) (fun _ t => (S i).base.metric t) N K)
    {V : Set M} (hV : IsCompact V) (hVU : V ⊆ U)
    (g : ℝ → SmoothRiemannianMetric I M) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b, ∀ q : ℕ, q ≤ N → ∀ x ∈ V,
      metricDerivNorm q (g s) (g t) R x ≤ L * |s - t|)
    (hconv : ∀ t ∈ Ico 0 b, MetricCPConvergenceOn V N (fun i => (S i).base.metric t) (g t) R) :
    MetricCPConvergenceOn V N (fun i => (S i).base.metric (age i)) (g b) R := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨B, hB, hbound⟩ := exists_metricDerivNormSupOn_time_lipschitz_of_initial_bounds
    U hU R N T Λ K hT hΛ hK A hA
  apply metricCPConvergenceOn_at_terminal_times_of_time_lipschitz R hV hb hB hL hconv hlip hlim
  exact Eventually.of_forall fun i s hs t ht q hq x hx =>
    (derivNorm_le_sup hV hq _ _ _ hx).trans
      (hbound (D i) (age i) (hage i) (hageT i) (hcarrier i) (hregular i)
        (S i) (hS i) (hgram i) (hequiv i) (hjets i) (hRic i) V hVU s hs t ht)

end DifferentialGeometry.PDE.RicciFlow
