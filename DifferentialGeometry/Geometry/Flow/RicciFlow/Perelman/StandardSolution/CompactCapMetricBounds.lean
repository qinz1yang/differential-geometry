import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialMetricTimeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactCapFlows
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S3 := Metric.sphere (0 : E4) 1
private local instance : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

private theorem closed_comparison {D : RealTimeInterval}
    (S : SolutionOn (I := 𝓡 3) (M := S3) D) (τ K : ℝ) (hτ : 0 ≤ τ) (hK : 0 ≤ K)
    (g₀ : SmoothRiemannianMetric (𝓡 3) S3) (hzero : S.base.metric 0 = g₀)
    (hpde : ∀ t ∈ Icc 0 τ, ∀ (x : S3) (v w : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun r => (S.base.metric r).inner x v w)
        (-2 * ricciTensor (S.base.metric t) x v w) (Ici 0) t)
    (hRm : ∀ t ∈ Icc 0 τ, ∀ x : S3,
      normSq0S (S.base.metric t) x 4 (nablaKRm04Field S t 0 x) ≤ K ^ 2) :
    ∀ t ∈ Icc 0 τ, MetricUniformEquivalentOn univ g₀ (S.base.metric t)
      (Real.exp (18 * K * τ)) := by
  let Λ := Real.exp (18 * K * τ)
  have hΛ : 1 ≤ Λ := Real.one_le_exp (by positivity)
  have hric (t : ℝ) (ht : t ∈ Icc 0 τ) (x : S3) (v : TangentSpace (𝓡 3) x) :
      |ricciTensor (S.base.metric t) x v v| ≤ (9 * K) * (S.base.metric t).inner x v v := by
    have hh := ricci_quadratic_form_bound_of_solution_curvature_bound S x v (hRm t ht x)
    simpa only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
      Real.sqrt_sq (hK), show (3 : ℝ) ^ 2 = 9 by norm_num] using hh
  have hequiv (t : ℝ) (ht : t ∈ Icc 0 τ) :
      MetricUniformEquivalentOn univ g₀ (S.base.metric t) Λ := by
    refine ⟨hΛ, ?_⟩
    intro x _ v
    have hh := metricEquiv_Icc S.base.metric
      (fun s hs y u w => (hpde s hs y u w).mono Icc_subset_Ici_self) hric t ht x v
    rw [hzero] at hh
    simp only [sub_zero, show (2 : ℝ) * (9 * K) = 18 * K by ring] at hh
    have hscale : 18 * K * t ≤ 18 * K * τ :=
      mul_le_mul_of_nonneg_left ht.2 (by positivity)
    have hn : 0 ≤ g₀.inner x v v := by
      by_cases hv : v = 0
      · simp only [hv, map_zero, le_refl]
      · exact (g₀.pos x v hv).le
    constructor
    · have he : Λ⁻¹ ≤ Real.exp (-(18 * K * t)) := by
        rw [show Λ⁻¹ = Real.exp (-(18 * K * τ)) from (Real.exp_neg _).symm]
        exact Real.exp_le_exp.mpr (neg_le_neg hscale)
      exact (mul_le_mul_of_nonneg_right he hn).trans hh.1
    · exact hh.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hscale) hn)
  exact hequiv

theorem exists_uniform_compact_cap_metric_bounds :
    ∃ τ : ℝ, ∃ hτ : 0 < τ, ∃ Λ : ℝ, 1 ≤ Λ ∧
    ∃ B C L : ℕ → ℝ, (∀ N, 0 ≤ B N) ∧ (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧
      ∀ (north : S3) (R : ℝ) (hR : max transitionEnd 2 + 2 ≤ R),
      ∃ S : SolutionOn (I := 𝓡 3) (M := S3) (RealTimeInterval.closed 0 τ hτ.le),
        IsSolutionOn S ∧ S.base.metric 0 = compactDoubleMetric north R hR ∧
        (∀ t ∈ Icc 0 τ, RiemannianMetricComplete (S.base.metric t)) ∧
        (∀ (x₀ : S3) (i j : Fin (Module.finrank ℝ E3)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
            (fun p : ℝ × S3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
            (Icc 0 τ ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
        (∀ t ∈ Icc 0 τ, ∀ (x : S3) (v w : TangentSpace (𝓡 3) x),
          HasDerivWithinAt (fun r => (S.base.metric r).inner x v w)
            (-2 * ricciTensor (S.base.metric t) x v w) (Ici 0) t) ∧
        (∀ N a b : ℕ, a + 2 * b ≤ N → ∀ t ∈ Icc 0 τ, ∀ x : S3,
          Real.sqrt (normSq0S (S.base.metric t) x (4 + a)
            (iteratedCovariantTimeDerivWithin S.base.metric
              (fun r => nablaKRm04Field S r a x) (Icc 0 τ) b t)) ≤ B N) ∧
        (∀ t ∈ Icc 0 τ, MetricUniformEquivalentOn univ
          (compactDoubleMetric north R hR) (S.base.metric t) Λ) ∧
        (∀ N : ℕ, ∀ t ∈ Icc 0 τ, ∀ x : S3,
          metricCovDerivNorm N (S.base.metric t) (compactDoubleMetric north R hR) x ≤ C N) ∧
        ∀ N : ℕ, ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ x : S3,
          metricDerivNorm N (S.base.metric s) (S.base.metric t)
            (compactDoubleMetric north R hR) x ≤ L N * |s - t| := by
  obtain ⟨τ, hτ, B, hB, hflows⟩ := exists_uniform_compact_cap_flows
  have hB0 := hB 0
  let Λ := Real.exp (18 * B 0 * τ)
  have hΛ : 1 ≤ Λ := Real.one_le_exp (by positivity)
  let κ := fun N => Real.sqrt (∑ k ∈ Finset.range (N + 1), (3 : ℝ) ^ (k + 4) * B k ^ 2)
  obtain ⟨C, L, hC, hL, hCLbound⟩ := exists_uniform_closed_initial_metric_time_bounds
    (I := 𝓡 3) (M := S3) (D := RealTimeInterval.closed 0 τ hτ.le)
    τ hτ.le (fun _ hs => hs) Λ hΛ κ (fun _ => Real.sqrt_nonneg _)
  refine ⟨τ, hτ, Λ, hΛ, B, C, L, hB, hC, hL, ?_⟩
  intro north R hR
  obtain ⟨S, hS, hzero, hcomplete, hgram, hpde, hbounds⟩ := hflows north R hR
  let g₀ := compactDoubleMetric north R hR
  have hRm (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 τ) (x : S3) :
      normSq0S (S.base.metric t) x (4 + k) (nablaKRm04Field S t k x) ≤ B k ^ 2 := by
    have hh := hbounds k k 0 (by omega) t ht x
    change Real.sqrt (normSq0S (S.base.metric t) x (4 + k) (nablaKRm04Field S t k x)) ≤ B k at hh
    exact (Real.sqrt_le_iff.mp hh).2
  have hequiv := closed_comparison S τ (B 0) hτ.le hB0 g₀ hzero hpde (hRm 0)
  have hShi (N : ℕ) : MovingShiBoundOn univ 0 τ (fun _ t => S.base.metric t) N (κ N) := by
    intro k hk _ t ht x _
    have hh := ricTower_normSq_le S t k x
    have hbound := hh.trans (mul_le_mul_of_nonneg_left (hRm k t ht x) (by positivity))
    apply Real.sqrt_le_sqrt (hbound.trans ?_)
    have hs : (3 : ℝ) ^ (k + 4) * B k ^ 2 ≤
        ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (j + 4) * B j ^ 2 :=
      Finset.single_le_sum (s := Finset.range (N + 1)) (a := k)
        (f := fun j : ℕ => (3 : ℝ) ^ (j + 4) * B j ^ 2)
        (fun _ _ => by positivity) (Finset.mem_range.mpr (by omega))
    simpa only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
      show 2 + k + 2 = k + 4 by omega] using hs
  obtain ⟨hspace, htime⟩ := hCLbound S hS hgram
    (fun s hs => by rw [hzero]; exact hequiv s hs) hShi
  refine ⟨S, hS, hzero, hcomplete, hgram, hpde, hbounds, hequiv, ?_, ?_⟩
  · intro N t ht x
    have hh := hspace N t ht x
    rwa [hzero] at hh
  · intro N s hs t ht x
    have hh := htime N s hs t ht x
    rwa [hzero] at hh
end DifferentialGeometry.PDE.RicciFlow
