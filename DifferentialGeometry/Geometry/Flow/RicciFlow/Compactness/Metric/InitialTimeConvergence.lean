import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.InitialMetricTimeBounds
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity

noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem metric_cp_convergence_on_vanishing_intervals_of_finite_ricci_bounds
    (U : Set M) (hU : IsOpen U) (R : SmoothRiemannianMetric I M)
    (N : ℕ) {Λ K : ℝ} (hΛ : 1 ≤ Λ) (hK : 0 ≤ K)
    (A : ℕ → ℝ) (hA : ∀ q, 1 ≤ q → q ≤ N → 0 ≤ A q)
    (D : ℕ → RealTimeInterval) (age : ℕ → ℝ) (hage : ∀ n, 0 ≤ age n)
    (hlim : Tendsto age atTop (𝓝 0))
    (hcarrier : ∀ n, Icc 0 (age n) ⊆ (D n).carrier)
    (hregular : ∀ n, Ioo 0 (age n) ⊆ (D n).regular)
    (S : ∀ n, SolutionOn (I := I) (M := M) (D n)) (hS : ∀ n, IsSolutionOn (S n))
    (hgram : ∀ n (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          ((S n).base.metric p.1) x₀ p.2 i j)
        (Icc 0 (age n) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hequiv : ∀ n, MetricUniformEquivalentOn U R ((S n).base.metric 0) Λ)
    (hjets : ∀ n q, 1 ≤ q → q ≤ N → ∀ x ∈ U,
      metricCovDerivNorm q ((S n).base.metric 0) R x ≤ A q)
    (hRic : ∀ n, MovingShiBoundOn U 0 (age n) (fun _ t => (S n).base.metric t) N K)
    {V : Set M} (hV : IsCompact V) (hVU : V ⊆ U)
    (hinit : MetricCPConvergenceOn V N (fun n => (S n).base.metric 0) R R) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ∈ Icc 0 (age n),
      metricDerivNormSupOn V N ((S n).base.metric t) R R < epsilon := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro epsilon hepsilon
  obtain ⟨eta, heta, _, hvariation⟩ := exists_uniform_initial_metric_derivative_stability
    U hU R N 1 Λ K (epsilon / 2) (by norm_num) hΛ hK (half_pos hepsilon) A hA
  obtain ⟨n₀, hn₀⟩ := hinit (epsilon / 2) (half_pos hepsilon)
  have htime : ∀ᶠ n in atTop, age n ≤ min eta 1 :=
    (hlim.eventually (Iio_mem_nhds (lt_min heta zero_lt_one))).mono fun _ h => h.le
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp htime
  refine ⟨max n₀ n₁, fun n hn t ht => ?_⟩
  have hninit := hn₀ n ((le_max_left _ _).trans hn)
  have hnage := hn₁ n ((le_max_right _ _).trans hn)
  have hvar := hvariation (D n) (age n) (hage n) (hnage.trans (min_le_right _ _))
    (hcarrier n) (hregular n) (S n) (hS n) (hgram n) (hequiv n) (hjets n) (hRic n)
    V hVU t ⟨ht.1, le_min (ht.2.trans (hnage.trans (min_le_left _ _))) ht.2⟩
  let bound := metricDerivNormSupOn V N ((S n).base.metric t) ((S n).base.metric 0) R +
    metricDerivNormSupOn V N ((S n).base.metric 0) R R
  have hsmall : bound < epsilon := by dsimp only [bound]; linarith
  have hle : metricDerivNormSupOn V N ((S n).base.metric t) R R ≤ max 0 bound := by
    apply metricDerivNormSupOn_le_of_forall V N _ _ _ _ (le_max_left _ _) ?_
    intro q hq x hx
    exact ((metricDerivNorm_triangle q ((S n).base.metric t) ((S n).base.metric 0)
      R R x).trans (add_le_add (derivNorm_le_sup hV hq _ _ _ hx)
        (derivNorm_le_sup hV hq _ _ _ hx))).trans (le_max_right _ _)
  exact hle.trans_lt (max_lt hepsilon hsmall)

theorem metric_cp_convergence_on_at_vanishing_time_of_finite_ricci_bounds
    (U : Set M) (hU : IsOpen U) (R : SmoothRiemannianMetric I M)
    (N : ℕ) {Λ K : ℝ} (hΛ : 1 ≤ Λ) (hK : 0 ≤ K)
    (A : ℕ → ℝ) (hA : ∀ q, 1 ≤ q → q ≤ N → 0 ≤ A q)
    (D : ℕ → RealTimeInterval) (age : ℕ → ℝ) (hage : ∀ n, 0 ≤ age n)
    (hlim : Tendsto age atTop (𝓝 0))
    (hcarrier : ∀ n, Icc 0 (age n) ⊆ (D n).carrier)
    (hregular : ∀ n, Ioo 0 (age n) ⊆ (D n).regular)
    (S : ∀ n, SolutionOn (I := I) (M := M) (D n)) (hS : ∀ n, IsSolutionOn (S n))
    (hgram : ∀ n (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          ((S n).base.metric p.1) x₀ p.2 i j)
        (Icc 0 (age n) ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hequiv : ∀ n, MetricUniformEquivalentOn U R ((S n).base.metric 0) Λ)
    (hjets : ∀ n q, 1 ≤ q → q ≤ N → ∀ x ∈ U,
      metricCovDerivNorm q ((S n).base.metric 0) R x ≤ A q)
    (hRic : ∀ n, MovingShiBoundOn U 0 (age n) (fun _ t => (S n).base.metric t) N K)
    {V : Set M} (hV : IsCompact V) (hVU : V ⊆ U)
    (hinit : MetricCPConvergenceOn V N (fun n => (S n).base.metric 0) R R) :
    MetricCPConvergenceOn V N (fun n => (S n).base.metric (age n)) R R := by
  intro epsilon hepsilon
  obtain ⟨n₀, hn₀⟩ := metric_cp_convergence_on_vanishing_intervals_of_finite_ricci_bounds
    U hU R N hΛ hK A hA D age hage hlim hcarrier hregular S hS hgram hequiv hjets hRic
    hV hVU hinit epsilon hepsilon
  exact ⟨n₀, fun n hn => hn₀ n hn (age n) ⟨hage n, le_rfl⟩⟩

end DifferentialGeometry.PDE.RicciFlow
