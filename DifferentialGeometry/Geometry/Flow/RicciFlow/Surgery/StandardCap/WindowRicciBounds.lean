import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformTipCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.RicciTimeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.LocalWindowCurvatureHorizon

set_option autoImplicit false
noncomputable section
open Set Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private local instance (V : Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)

theorem exists_uniform_window_ricci_lower_bound_of_local_curvature
    (ρ T K κ : ℝ) (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∃ σ c : ℝ, 0 < σ ∧ 0 < c ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ζ : ℝ}
        (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      32 * ρ < D → 4 ≤ m → ζ ≤ 1 / 2 →
      ∀ (J : RealTimeInterval) (θ : ℝ), 0 < θ → θ ≤ T →
        Icc 0 θ ⊆ J.carrier → Ioo 0 θ ⊆ J.regular →
        ∀ S : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
        IsSolutionOn S → S.base.metric 0 = w.windowMetric →
        (∀ (p : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun z : ℝ × standardCapWindow D =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric z.1) p z.2 i j)
            (Icc 0 θ ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)) →
        (∀ t ∈ Icc 0 θ, ∀ x : standardCapWindow D, ‖x.val‖ ≤ 32 * ρ →
          nablaKRm04NormSqIntrinsic S 0 t x ≤ K) →
        ∀ τ ∈ Icc 0 θ, ∀ (x : standardCapWindow D), ‖x.val‖ ≤ ρ →
          (∀ v : TangentSpace ThreeModel x,
            κ * (S.base.metric τ).inner x v v ≤ ricciTensor (S.base.metric τ) x v v) →
          ∀ t ∈ Icc τ (min (τ + σ) θ), ∀ v : TangentSpace ThreeModel x,
            c * (S.base.metric t).inner x v v ≤ ricciTensor (S.base.metric t) x v v := by
  obtain ⟨B, hB, hjets⟩ :=
    exists_uniform_window_flow_curvature_derivative_bound_of_local_curvature_bounded_horizon
      2 (32 * ρ) T K (by positivity)
  let Λ := Real.exp (18 * Real.sqrt K * T)
  let R := ricciOrdinaryTimeBound 3 (Real.sqrt B)
  have hΛ : 0 < Λ := Real.exp_pos _
  have hR : 0 ≤ R := ricciOrdinaryTimeBound_nonneg _ _ (Real.sqrt_nonneg _)
  let σ := κ / (2 * (Λ * R + 1))
  let c := κ / (2 * Λ)
  have hσ : 0 < σ := div_pos hκ (by positivity)
  have hc : 0 < c := div_pos hκ (by positivity)
  have hcΛ : c * Λ = κ / 2 := by dsimp only [c]; field_simp
  have hσR : Λ * R * σ ≤ κ / 2 := by
    have hh : σ * (2 * (Λ * R + 1)) = κ := div_mul_cancel₀ κ (by positivity)
    nlinarith
  refine ⟨σ, c, hσ, hc, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA D m ζ w hD hm hζ
    J θ hθ hθT hcarrier hregular S hS hzero hgram hcurv τ hτ x hx hRic t ht v
  have htt : t ≤ θ := ht.2.trans (min_le_right _ _)
  have hτt : Icc τ t ⊆ Icc 0 θ := Icc_subset_Icc hτ.1 htt
  have hτtreg : Ioo τ t ⊆ Ioo 0 θ := Ioo_subset_Ioo hτ.1 htt
  have hjet := hjets w hζ hm hD J θ hθ hθT hcarrier hregular S hS hzero hgram hcurv
  have hsq : ∀ r ∈ Icc 0 θ, normSq0S (S.base.metric r) x 4 (S.base.rm04 r x) ≤ K := by
    intro r hr
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using
      hcurv r hr x (by linarith)
  apply hS.ricciTensor_lower_bound_of_curvature_derivative_bound x hΛ.le (Real.sqrt_nonneg B)
    hc.le (hτt.trans hcarrier) (hτtreg.trans hregular) ?_ ?_ hRic ?_ ⟨ht.1, le_rfl⟩ v
  · intro r hr z
    have hcmp := (metric_inner_exp_bounds_of_curvature_bound S hS hcarrier hregular x hsq
      (hτt hr) hτ z).2
    have hdim : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by simp [ThreeSpace]
    rw [hdim, abs_of_nonneg (sub_nonneg.mpr hr.1)] at hcmp
    have he : Real.exp (2 * (3 : ℝ)^2 * Real.sqrt K * (r - τ)) ≤ Λ := by
      apply Real.exp_le_exp.mpr
      have htime : r - τ ≤ T := by linarith [(hτt hr).2.trans hθT, hτ.1]
      norm_num only [show 2 * (3 : ℝ)^2 = 18 by norm_num]
      exact mul_le_mul_of_nonneg_left htime (by positivity)
    exact hcmp.trans (mul_le_mul_of_nonneg_right he (metric_inner_self_nonneg _ _ _))
  · intro r hr j hj
    exact Real.sqrt_le_sqrt (hjet j hj r (hτt (Ioo_subset_Icc_self hr)) x (by
      simpa only [mul_div_cancel_left₀ ρ (by norm_num : (32 : ℝ) ≠ 0)] using hx))
  · have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [hdim, hcΛ]
    change κ / 2 + Λ * R * (t - τ) ≤ κ
    have hd : t - τ ≤ σ := by have hh := ht.2.trans (min_le_left _ _); linarith
    have hh := mul_le_mul_of_nonneg_left hd (mul_nonneg hΛ.le hR)
    linarith

theorem exists_uniform_window_tip_ricci_lower_bound_of_standard_metric_close
    (Θ T₀ K : ℝ) (hΘ : 0 ≤ Θ) (hΘ1 : Θ < 1) :
    ∃ ε σ c : ℝ, 0 < ε ∧ 0 < σ ∧ 0 < c ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ} {m : ℕ} {ζ : ℝ}
        (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      32 < D → 4 ≤ m → ζ ≤ 1 / 2 →
      ∀ (J : RealTimeInterval) (T : ℝ), 0 < T → T ≤ T₀ →
        Icc 0 T ⊆ J.carrier → Ioo 0 T ⊆ J.regular →
        ∀ L : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
        IsSolutionOn L → L.base.metric 0 = w.windowMetric →
        (∀ (p : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun z : ℝ × standardCapWindow D =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (L.base.metric z.1) p z.2 i j)
            (Icc 0 T ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)) →
        (∀ t ∈ Icc 0 T, ∀ x : standardCapWindow D, ‖x.val‖ ≤ 32 →
          nablaKRm04NormSqIntrinsic L 0 t x ≤ K) →
        ∀ τ ∈ Icc 0 T, ∀ (Q : StandardSolution) (s : ℝ), s ∈ Icc 0 Θ →
        ∀ (x : standardCapWindow D), x.val = 0 →
          (∀ j : ℕ, j ≤ 2 → metricDerivNorm j (L.base.metric τ)
            ((Q.val.metric s).restrictOpen (standardCapWindow D))
            (metric.restrictOpen (standardCapWindow D)) x ≤ ε) →
          ∀ t ∈ Icc τ (min (τ + σ) T), ∀ v : TangentSpace ThreeModel x,
            c * (L.base.metric t).inner x v v ≤ ricciTensor (L.base.metric t) x v v := by
  obtain ⟨ε, κ, hε, hκ, htip⟩ :=
    exists_uniform_standard_tip_ricci_lower_bound_of_metric_close Θ hΘ hΘ1
  obtain ⟨σ, c, hσ, hc, hpropagate⟩ :=
    exists_uniform_window_ricci_lower_bound_of_local_curvature 1 T₀ K κ (by norm_num) hκ
  refine ⟨ε, σ, c, hε, hσ, hc, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA D m ζ w hD hm hζ
    J T hT hTT₀ hcarrier hregular L hL hzero hgram hcurv τ hτ Q s hs x hx hclose t ht v
  apply hpropagate w (by simpa using hD) hm hζ J T hT hTT₀ hcarrier hregular L hL
    hzero hgram (by simpa using hcurv) τ hτ x (by rw [hx]; simp) ?_ t ht v
  exact htip Q s hs (standardCapWindow D) (L.base.metric τ) x hx hclose

end DifferentialGeometry.PDE.RicciFlow.StandardCap
