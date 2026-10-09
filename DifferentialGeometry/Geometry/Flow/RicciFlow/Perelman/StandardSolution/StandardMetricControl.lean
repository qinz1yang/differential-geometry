import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShorterMetricTimeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.TerminalSpatialBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem initial_comparison {D : RealTimeInterval}
    (S : SolutionOn (I := 𝓡 3) (M := E3) D) (τ α K : ℝ) (hτ : 0 ≤ τ)
    (hτα : τ ≤ α) (hK : 0 ≤ K)
    (hpde : ∀ t ∈ Icc 0 τ, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun r => (S.base.metric r).inner x v w)
        (-2 * ricciTensor (S.base.metric t) x v w) (Ici 0) t)
    (hRm : ∀ t ∈ Icc 0 τ, ∀ x : E3,
      normSq0S (S.base.metric t) x 4 (nablaKRm04Field S t 0 x) ≤ K ^ 2) :
    ∀ t ∈ Icc 0 τ, MetricUniformEquivalentOn univ (S.base.metric 0) (S.base.metric t)
      (Real.exp (18 * K * α)) := by
  have hα : 0 ≤ α := hτ.trans hτα
  let Λ := Real.exp (18 * K * α)
  have hΛ : 1 ≤ Λ := Real.one_le_exp (by positivity)
  have hric (t : ℝ) (ht : t ∈ Icc 0 τ) (x : E3) (v : TangentSpace (𝓡 3) x) :
      |ricciTensor (S.base.metric t) x v v| ≤ (9 * K) * (S.base.metric t).inner x v v := by
    have hh := ricci_quadratic_form_bound_of_solution_curvature_bound S x v (hRm t ht x)
    simpa only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
      Real.sqrt_sq (hK), show (3 : ℝ) ^ 2 = 9 by norm_num] using hh
  have hequiv (t : ℝ) (ht : t ∈ Icc 0 τ) :
      MetricUniformEquivalentOn univ (S.base.metric 0) (S.base.metric t) Λ := by
    refine ⟨hΛ, ?_⟩
    intro x _ v
    have hh := metricEquiv_Icc S.base.metric
      (fun s hs y u w => (hpde s hs y u w).mono Icc_subset_Ici_self) hric t ht x v
    simp only [sub_zero, show (2 : ℝ) * (9 * K) = 18 * K by ring] at hh
    have hscale : 18 * K * t ≤ 18 * K * α :=
      mul_le_mul_of_nonneg_left (ht.2.trans hτα) (by positivity)
    have hn : 0 ≤ (S.base.metric 0).inner x v v := by
      by_cases hv : v = 0
      · simp only [hv, map_zero, le_refl]
      · exact ((S.base.metric 0).pos x v hv).le
    constructor
    · have he : Λ⁻¹ ≤ Real.exp (-(18 * K * t)) := by
        rw [show Λ⁻¹ = Real.exp (-(18 * K * α)) from (Real.exp_neg _).symm]
        exact Real.exp_le_exp.mpr (neg_le_neg hscale)
      exact (mul_le_mul_of_nonneg_right he hn).trans hh.1
    · exact hh.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hscale) hn)
  exact hequiv

theorem standard_metric_bounds_on_shorter_windows
    (T K : ℝ) (hT : 0 ≤ T) (hK : 0 ≤ K) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ C L : ℕ → ℝ,
      (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧
      ∀ S : PartialStandardSolution, ∀ θ : ℝ, 0 ≤ θ → θ ≤ T →
        ENNReal.ofReal θ < S.lifetime →
        (∀ t ∈ Icc 0 θ, ∀ x : E3,
          Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ K) →
        (∀ t ∈ Icc 0 θ, MetricUniformEquivalentOn univ
          DifferentialGeometry.PDE.RicciFlow.StandardCap.metric (S.metric t) Λ) ∧
        (∀ N : ℕ, ∀ t ∈ Icc 0 θ, ∀ x : E3,
          metricCovDerivNorm N (S.metric t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ C N) ∧
        ∀ N : ℕ, ∀ s ∈ Icc 0 θ, ∀ t ∈ Icc 0 θ, ∀ x : E3,
          metricDerivNorm N (S.metric s) (S.metric t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤
            L N * |s - t| := by
  obtain ⟨A, _, hA⟩ := standard_initial_curvature_derivative_bounds
  let V := fun N => completeCurvatureEndpointBound (Module.finrank ℝ E3) N T K A
  let κ := fun N => Real.sqrt (∑ k ∈ Finset.range (N + 1),
    (3 : ℝ) ^ ((2 + k) + 2) * (V N) ^ 2)
  have hκ (N : ℕ) : 0 ≤ κ N := Real.sqrt_nonneg _
  let Λ := Real.exp (18 * K * T)
  have hΛ : 1 ≤ Λ := Real.one_le_exp (by positivity)
  obtain ⟨C, L, hC, hL, hmetric⟩ := exists_uniform_shorter_initial_metric_time_bounds
    (I := 𝓡 3) (M := E3) T Λ hΛ κ hκ
  refine ⟨Λ, hΛ, C, L, hC, hL, ?_⟩
  intro S θ hθ hθα hθl hRm
  have hslab : Icc 0 θ ⊆ S.domain :=
    (Icc_subset_lifetimeInterval_iff S.lifetime S.lifetime_pos θ hθ).mpr hθl
  have hreg : Ioo 0 θ ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
    intro s hs
    exact (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos s).mpr
      ⟨hs.1, (ENNReal.ofReal_le_ofReal hs.2.le).trans_lt hθl⟩
  have hgram := chartGram_contMDiffOn_of_cartesian S.metric (Icc 0 θ)
    (S.smooth.mono (prod_mono hslab subset_rfl))
  have he := initial_comparison S.toSolutionOn θ T K hθ hθα hK
    (fun t ht => S.equation t (hslab ht))
    (fun t ht x => (Real.sqrt_le_iff.mp (hRm t ht x)).2)
  have hjet (N k : ℕ) (hk : k ≤ N) (t : ℝ) (ht : t ∈ Icc 0 θ) (x : E3) :
      Real.sqrt (nablaKRm04NormSqIntrinsic S.toSolutionOn k t x) ≤ V N := by
    have hh := curvature_endpoint_bound_complete_terminal θ hθ N K hK A
      (lifetimeInterval S.lifetime S.lifetime_pos) S.toSolutionOn S.isSolutionOn
      (S.complete 0 (hslab ⟨le_rfl, hθ⟩)) hslab hreg hgram
      (hRm) (fun j _ y => hA S j y) k hk t ht x
    exact hh.trans (completeCurvatureEndpointBound_mono_time _ N θ T K A hK hθ hθα)
  have hShi (N : ℕ) : MovingShiBoundOn univ 0 θ (fun _ t => S.metric t) N (κ N) := by
    intro k hk _i t ht x _
    apply Real.sqrt_le_sqrt
    have hRm := (Real.sqrt_le_iff.mp (hjet N k hk t ht x)).2
    have hh := ricTower_normSq_le S.toSolutionOn t k x
    simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat] at hh
    apply (hh.trans (mul_le_mul_of_nonneg_left hRm (by positivity))).trans
    have hsum : (3 : ℝ) ^ ((2 + k) + 2) * (V N) ^ 2 ≤
        ∑ j ∈ Finset.range (N + 1), (3 : ℝ) ^ ((2 + j) + 2) * (V N) ^ 2 :=
      Finset.single_le_sum (s := Finset.range (N + 1)) (a := k)
        (f := fun j : ℕ => (3 : ℝ) ^ ((2 + j) + 2) * (V N) ^ 2) (fun j _ => mul_nonneg (by positivity) (sq_nonneg (V N)))
        (Finset.mem_range.mpr (by omega))
    exact hsum
  have hm := hmetric (lifetimeInterval S.lifetime S.lifetime_pos) θ hθ hθα hreg
    S.toSolutionOn S.isSolutionOn hgram he hShi
  have hecap : ∀ t ∈ Icc 0 θ, MetricUniformEquivalentOn univ
      DifferentialGeometry.PDE.RicciFlow.StandardCap.metric (S.metric t) Λ := by
    simpa only [PartialStandardSolution.toSolutionOn_metric, S.initial] using he
  refine ⟨hecap, ?_⟩
  simpa only [PartialStandardSolution.toSolutionOn_metric, S.initial] using hm

theorem standard_uniform_fixed_cap_metric_bounds :
    ∃ α : ℝ, 0 < α ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ C L : ℕ → ℝ,
      (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧
      ∀ S : PartialStandardSolution, ∀ θ : ℝ, 0 ≤ θ → θ ≤ α →
        ENNReal.ofReal θ < S.lifetime →
        (∀ t ∈ Icc 0 θ, MetricUniformEquivalentOn univ
          DifferentialGeometry.PDE.RicciFlow.StandardCap.metric (S.metric t) Λ) ∧
        (∀ N : ℕ, ∀ t ∈ Icc 0 θ, ∀ x : E3,
          metricCovDerivNorm N (S.metric t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ C N) ∧
        ∀ N : ℕ, ∀ s ∈ Icc 0 θ, ∀ t ∈ Icc 0 θ, ∀ x : E3,
          metricDerivNorm N (S.metric s) (S.metric t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤
            L N * |s - t| := by
  obtain ⟨α, hα, K, hK, hcurv⟩ := standard_uniform_initial_curvature_control
  obtain ⟨Λ, hΛ, C, L, hC, hL, hb⟩ :=
    standard_metric_bounds_on_shorter_windows α K hα.le hK.le
  exact ⟨α, hα, Λ, hΛ, C, L, hC, hL, fun S θ hθ hθα hθl =>
    hb S θ hθ hθα hθl (hcurv S θ hθ hθα hθl)⟩

theorem standard_metric_bounds_before_endpoint
    (T K : ℝ) (hT : 0 ≤ T) (hK : 0 ≤ K) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ C L : ℕ → ℝ,
      (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧
      ∀ S : PartialStandardSolution, ENNReal.ofReal T ≤ S.lifetime →
        (∀ t ∈ Ico 0 T, ∀ x : E3,
          Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ K) →
        (∀ t ∈ Ico 0 T, MetricUniformEquivalentOn univ
          DifferentialGeometry.PDE.RicciFlow.StandardCap.metric (S.metric t) Λ) ∧
        (∀ N : ℕ, ∀ t ∈ Ico 0 T, ∀ x : E3,
          metricCovDerivNorm N (S.metric t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ C N) ∧
        ∀ N : ℕ, ∀ s ∈ Ico 0 T, ∀ t ∈ Ico 0 T, ∀ x : E3,
          metricDerivNorm N (S.metric s) (S.metric t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤
            L N * |s - t| := by
  obtain ⟨Λ, hΛ, C, L, hC, hL, hb⟩ := standard_metric_bounds_on_shorter_windows T K hT hK
  refine ⟨Λ, hΛ, C, L, hC, hL, ?_⟩
  intro S hTS hRm
  have hw (θ : ℝ) (hθ : θ ∈ Ico 0 T) := hb S θ hθ.1 hθ.2.le
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hθ.1).mpr hθ.2 |>.trans_le hTS)
    (fun t ht => hRm t ⟨ht.1, ht.2.trans_lt hθ.2⟩)
  refine ⟨fun t ht => (hw t ht).1 t ⟨ht.1, le_rfl⟩,
    fun N t ht x => (hw t ht).2.1 N t ⟨ht.1, le_rfl⟩ x, ?_⟩
  intro N s hs t ht x
  exact (hw (max s t) ⟨hs.1.trans (le_max_left _ _), max_lt hs.2 ht.2⟩).2.2 N
    s ⟨hs.1, le_max_left _ _⟩ t ⟨ht.1, le_max_right _ _⟩ x
end DifferentialGeometry.PDE.RicciFlow
