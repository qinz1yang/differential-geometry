import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Evaluation
import DifferentialGeometry.Geometry.Curvature.RicciUniformPerturbation
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange

noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

theorem MetricCPConvergenceOn.eventually_ricciTensor_lower_bound
    {G : ℕ → SmoothRiemannianMetric I M} {g R : SmoothRiemannianMetric I M}
    {K : Set M} (hconv : MetricCPConvergenceOn K 2 G g R) (hK : IsCompact K)
    {κ : ℝ} (hκ : 0 < κ)
    (hRic : ∀ x ∈ K, ∀ v : TangentSpace I x, κ * g.inner x v v ≤ ricciTensor g x v v) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v : TangentSpace I x,
      (κ / 2) * (G k).inner x v v ≤ ricciTensor (G k) x v v := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := Nat.cast_nonneg _
  let ε := min (1 / 2 : ℝ) (κ / (κ + 480 * n))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hbudget : (κ / 2) * (1 + ε) + 240 * n * ε ≤ κ := by
    have hh := (le_div_iff₀ (by positivity : 0 < κ + 480 * n)).mp
      (min_le_right _ _ : ε ≤ κ / (κ + 480 * n))
    nlinarith
  obtain ⟨N, hN⟩ := (hconv.change_reference hK g) ε hε
  filter_upwards [eventually_ge_atTop N] with k hk
  intro x hx v
  exact ricciTensor_lower_bound_of_small_metric_derivatives (G k) g x
    (min_le_left _ _) (by positivity)
    (fun a ha => (derivNorm_le_sup hK ha (G k) g g hx).trans (hN k hk).le)
    (hRic x hx) hbudget v

variable {A : Type*} [PseudoMetricSpace A]

theorem eventually_ricciTensor_lower_bound_of_uniform_metric_approximation
    {G : ℕ → A → SmoothRiemannianMetric I M} {g : A → SmoothRiemannianMetric I M}
    (R : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K)
    {U : Set A} (hU : IsCompact U) {L κ : ℝ} (hL : 0 ≤ L) (hκ : 0 < κ)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ U,
      metricDerivNormSupOn K 2 (G i t) (g t) R < ε)
    (hlip : ∀ s ∈ U, ∀ t ∈ U, ∀ q : ℕ, q ≤ 2 → ∀ x ∈ K,
      metricDerivNorm q (g s) (g t) R x ≤ L * dist s t)
    (hRic : ∀ t ∈ U, ∀ x ∈ K, ∀ v : TangentSpace I x,
      κ * (g t).inner x v v ≤ ricciTensor (g t) x v v) :
    ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ U, ∀ x ∈ K, ∀ v : TangentSpace I x,
      (κ / 2) * (G i t).inner x v v ≤ ricciTensor (G i t) x v v := by
  classical
  by_contra! hnot
  choose n hn t ht x hx v hbad using hnot
  obtain ⟨a, ha, rho, hrho, htime⟩ := hU.tendsto_subseq ht
  have hcp : MetricCPConvergenceOn K 2
      (fun i => G (n (rho i)) (t (rho i))) (g a) R := by
    apply metricCPConvergenceOn_of_uniform_approximation_of_lipschitz
      (G := fun i r => G (n (rho i)) r) (g := g) R hK hL ?_ hlip
      (Eventually.of_forall fun i => ht (rho i)) ha htime
    intro ε hε
    obtain ⟨N, hN⟩ := hconv ε hε
    exact ⟨N, fun i hi r hr => hN (n (rho i))
      (hi.trans ((hrho.id_le i).trans (hn (rho i)))) r hr⟩
  obtain ⟨i, hi⟩ := (hcp.eventually_ricciTensor_lower_bound hK hκ (hRic a ha)).exists
  exact (not_lt_of_ge (hi (x (rho i)) (hx (rho i)) (v (rho i)))) (hbad (rho i))

end DifferentialGeometry.CheegerGromovCompactness
