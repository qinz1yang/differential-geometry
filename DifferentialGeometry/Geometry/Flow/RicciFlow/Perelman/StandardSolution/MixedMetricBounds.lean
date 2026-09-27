import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialMetricTimeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem closed_comparison {D : RealTimeInterval}
    (hdim : Module.finrank ℝ E = 3)
    (S : SolutionOn (I := I) (M := M) D)
    (τ K : ℝ) (hτ : 0 ≤ τ) (hK : 0 ≤ K)
    (hpde : ∀ t ∈ Icc 0 τ, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun r => (S.base.metric r).inner x v w)
        (-2 * ricciTensor (S.base.metric t) x v w) (Ici 0) t)
    (hRm : ∀ t ∈ Icc 0 τ, ∀ x : M,
      normSq0S (S.base.metric t) x 4
        (nablaKRm04Field S t 0 x) ≤ K ^ 2) :
    ∀ t ∈ Icc 0 τ,
      MetricUniformEquivalentOn univ (S.base.metric 0) (S.base.metric t)
        (Real.exp (18 * K * τ)) := by
  let Λ := Real.exp (18 * K * τ)
  have hΛ : 1 ≤ Λ := Real.one_le_exp (by positivity)
  have hric (t : ℝ) (ht : t ∈ Icc 0 τ)
      (x : M) (v : TangentSpace I x) :
      |ricciTensor (S.base.metric t) x v v| ≤
        (9 * K) * (S.base.metric t).inner x v v := by
    have hh :=
      ricci_quadratic_form_bound_of_solution_curvature_bound S x v (hRm t ht x)
    simpa only [hdim, Nat.cast_ofNat, Real.sqrt_sq hK,
      show (3 : ℝ) ^ 2 = 9 by norm_num] using hh
  intro t ht
  refine ⟨hΛ, ?_⟩
  intro x _ v
  have hh := metricEquiv_Icc S.base.metric
    (fun s hs y u w => (hpde s hs y u w).mono Icc_subset_Ici_self)
    hric t ht x v
  simp only [sub_zero, show (2 : ℝ) * (9 * K) = 18 * K by ring] at hh
  have hscale : 18 * K * t ≤ 18 * K * τ :=
    mul_le_mul_of_nonneg_left ht.2 (by positivity)
  have hn : 0 ≤ (S.base.metric 0).inner x v v := by
    by_cases hv : v = 0
    · simp only [hv, map_zero, le_refl]
    · exact ((S.base.metric 0).pos x v hv).le
  constructor
  · have he : Λ⁻¹ ≤ Real.exp (-(18 * K * t)) := by
      rw [show Λ⁻¹ = Real.exp (-(18 * K * τ)) from (Real.exp_neg _).symm]
      exact Real.exp_le_exp.mpr (neg_le_neg hscale)
    exact (mul_le_mul_of_nonneg_right he hn).trans hh.1
  · exact hh.2.trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hscale) hn)

theorem exists_uniform_metric_time_bounds_of_spatial_curvature_bounds
    (hdim : Module.finrank ℝ E = 3)
    (τ : ℝ) (hτ : 0 < τ) (B : ℕ → ℝ) (hB : ∀ N, 0 ≤ B N) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ C L : ℕ → ℝ,
      (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧
      ∀ S : SolutionOn (I := I) (M := M)
        (RealTimeInterval.closed 0 τ hτ.le),
        IsSolutionOn S →
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
            (fun p : ℝ × M =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
            (Icc 0 τ ×ˢ
              (trivializationAt E (TangentSpace I) x₀).baseSet)) →
        (∀ t ∈ Icc 0 τ, ∀ (x : M) (v w : TangentSpace I x),
          HasDerivWithinAt (fun r => (S.base.metric r).inner x v w)
            (-2 * ricciTensor (S.base.metric t) x v w) (Ici 0) t) →
        (∀ k : ℕ, ∀ t ∈ Icc 0 τ, ∀ x : M,
          Real.sqrt (normSq0S (S.base.metric t) x (4 + k)
            (nablaKRm04Field S t k x)) ≤ B k) →
        (∀ t ∈ Icc 0 τ,
          MetricUniformEquivalentOn univ
            (S.base.metric 0) (S.base.metric t) Λ) ∧
        (∀ N : ℕ, ∀ t ∈ Icc 0 τ, ∀ x : M,
          metricCovDerivNorm N (S.base.metric t) (S.base.metric 0) x ≤ C N) ∧
        ∀ N : ℕ, ∀ s ∈ Icc 0 τ, ∀ t ∈ Icc 0 τ, ∀ x : M,
          metricDerivNorm N (S.base.metric s) (S.base.metric t)
            (S.base.metric 0) x ≤ L N * |s - t| := by
  have hB0 := hB 0
  let Λ := Real.exp (18 * B 0 * τ)
  have hΛ : 1 ≤ Λ := Real.one_le_exp (by positivity)
  let κ := fun N =>
    Real.sqrt (∑ k ∈ Finset.range (N + 1), (3 : ℝ) ^ (k + 4) * B k ^ 2)
  obtain ⟨C, L, hC, hL, hCLbound⟩ :=
    exists_uniform_closed_initial_metric_time_bounds
      (I := I) (M := M) (D := RealTimeInterval.closed 0 τ hτ.le)
      τ hτ.le (fun _ hs => hs) Λ hΛ κ (fun _ => Real.sqrt_nonneg _)
  refine ⟨Λ, hΛ, C, L, hC, hL, ?_⟩
  intro S hS hgram hpde hbounds
  have hRm (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 τ) (x : M) :
      normSq0S (S.base.metric t) x (4 + k)
        (nablaKRm04Field S t k x) ≤ B k ^ 2 :=
    (Real.sqrt_le_iff.mp (hbounds k t ht x)).2
  have hequiv :=
    closed_comparison hdim S τ (B 0) hτ.le hB0 hpde (hRm 0)
  have hShi (N : ℕ) :
      MovingShiBoundOn univ 0 τ (fun _ t => S.base.metric t) N (κ N) := by
    intro k hk _ t ht x _
    have hh := ricTower_normSq_le S t k x
    have hbound :=
      hh.trans (mul_le_mul_of_nonneg_left (hRm k t ht x) (by positivity))
    apply Real.sqrt_le_sqrt (hbound.trans ?_)
    have hs : (3 : ℝ) ^ (k + 4) * B k ^ 2 ≤
        ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ (j + 4) * B j ^ 2 :=
      Finset.single_le_sum (s := Finset.range (N + 1)) (a := k)
        (f := fun j : ℕ => (3 : ℝ) ^ (j + 4) * B j ^ 2)
        (fun _ _ => by positivity) (Finset.mem_range.mpr (by omega))
    simpa only [hdim, Nat.cast_ofNat,
      show 2 + k + 2 = k + 4 by omega] using hs
  obtain ⟨hspace, htime⟩ := hCLbound S hS hgram hequiv hShi
  exact ⟨hequiv, hspace, htime⟩

end DifferentialGeometry.PDE.RicciFlow
