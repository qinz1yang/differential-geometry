import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointMetricBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ClosedMetricLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.TimeRegularity

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem metric_cov_evolution_constant_mono (C B s T A : ℝ) (hsT : s ≤ T) :
    metricCovOrderEvolutionConstant C B s A ≤ metricCovOrderEvolutionConstant C B T A := by
  unfold metricCovOrderEvolutionConstant metricCovOrderEvolutionAlpha metricCovOrderEvolutionBeta
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_right
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsT (by positivity))
  · positivity

private theorem exists_local_closed_metric_covariant_bounds
    (U : Set M) (hU : IsOpen U) (R : SmoothRiemannianMetric I M)
    (N : ℕ) (T Λ K : ℝ) (hΛ : 1 ≤ Λ) (hK : 0 ≤ K)
    (A : ℕ → ℝ) (hA : ∀ q, 1 ≤ q → q ≤ N → 0 ≤ A q) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
      ∀ (D : RealTimeInterval) (θ : ℝ), 0 ≤ θ → θ ≤ T → Ioo 0 θ ⊆ D.regular →
      ∀ S : SolutionOn (I := I) (M := M) D, IsSolutionOn S →
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
            (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
              (S.base.metric p.1) x₀ p.2 i j)
            (Icc 0 θ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
        (∀ t ∈ Icc 0 θ, MetricUniformEquivalentOn U R (S.base.metric t) Λ) →
        (∀ q, 1 ≤ q → q ≤ N → ∀ x ∈ U,
          metricCovDerivNorm q (S.base.metric 0) R x ≤ A q) →
        MovingShiBoundOn U 0 θ (fun _ t => S.base.metric t) N K →
        ∀ q, 1 ≤ q → q ≤ N → ∀ t ∈ Icc 0 θ, ∀ x ∈ U,
          metricCovDerivNorm q (S.base.metric t) R x ≤ C q := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Good := fun (D : RealTimeInterval) (θ : ℝ) (S : SolutionOn (I := I) (M := M) D) =>
    IsSolutionOn S ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (S.base.metric p.1) x₀ p.2 i j)
          (Icc 0 θ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ t ∈ Icc 0 θ, MetricUniformEquivalentOn U R (S.base.metric t) Λ) ∧
      (∀ q, 1 ≤ q → q ≤ N → ∀ x ∈ U,
        metricCovDerivNorm q (S.base.metric 0) R x ≤ A q) ∧
      MovingShiBoundOn U 0 θ (fun _ t => S.base.metric t) N K
  have hb : ∀ q : ℕ, q ≤ N → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (D : RealTimeInterval) (θ : ℝ), 0 ≤ θ → θ ≤ T → Ioo 0 θ ⊆ D.regular →
      ∀ S : SolutionOn (I := I) (M := M) D, Good D θ S →
        1 ≤ q → ∀ t ∈ Icc 0 θ, ∀ x ∈ U,
          metricCovDerivNorm q (S.base.metric t) R x ≤ C := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro hqN
      by_cases hq : q = 0
      · subst q
        exact ⟨0, le_rfl, fun _ _ _ _ _ _ _ h => (by omega)⟩
      · let Cg := fun r => if hr : r < q then (ih r hr (by omega)).choose else 0
        have hCg (r : ℕ) (hr : r < q) : 0 ≤ Cg r ∧
            ∀ (D : RealTimeInterval) (θ : ℝ), 0 ≤ θ → θ ≤ T → Ioo 0 θ ⊆ D.regular →
            ∀ S : SolutionOn (I := I) (M := M) D, Good D θ S →
              1 ≤ r → ∀ t ∈ Icc 0 θ, ∀ x ∈ U,
                metricCovDerivNorm r (S.base.metric t) R x ≤ Cg r := by
          simpa only [Cg, dif_pos hr] using (ih r hr (by omega)).choose_spec
        let cf := ricTowerCoeffs (Module.finrank ℝ E) q Λ Cg K
        refine ⟨metricCovOrderEvolutionConstant cf.slope cf.offset T (A q),
          Real.sqrt_nonneg _, ?_⟩
        intro D θ hθ hθT hreg S hS hqpos t ht x hx
        obtain ⟨hSol, hgram, hequiv, hinit, hShi⟩ := hS
        have hbound := metricCovOrderBound_stage_closed S hSol θ hθ hreg hgram R U hU
          q hqpos Λ hΛ hequiv Cg
          (fun r hr hrq s hs y hy =>
            (hCg r hrq).2 D θ hθ hθT hreg S ⟨hSol, hgram, hequiv, hinit, hShi⟩
              hr s hs y hy)
          K hK (fun r hr => hShi r (hr.trans hqN)) (A q) (hA q hqpos hqN)
          (hinit q hqpos hqN) t ht x hx
        exact hbound.trans (metric_cov_evolution_constant_mono cf.slope cf.offset θ T (A q) hθT)
  let C := fun q => if hq : q ≤ N then (hb q hq).choose else 0
  refine ⟨C, ?_, ?_⟩
  · intro q
    by_cases hq : q ≤ N
    · simpa only [C, dif_pos hq] using (hb q hq).choose_spec.1
    · simp only [C, dif_neg hq, le_rfl]
  · intro D θ hθ hθT hreg S hS hgram hequiv hinit hShi q hq hqN
    simpa only [C, dif_pos hqN] using
      (hb q hqN).choose_spec.2 D θ hθ hθT hreg S ⟨hS, hgram, hequiv, hinit, hShi⟩ hq

theorem exists_metricDerivNormSupOn_time_lipschitz_of_finite_ricci_bounds
    (U : Set M) (hU : IsOpen U) (R : SmoothRiemannianMetric I M)
    (N : ℕ) (T Λ K : ℝ) (hΛ : 1 ≤ Λ) (hK : 0 ≤ K)
    (A : ℕ → ℝ) (hA : ∀ q, 1 ≤ q → q ≤ N → 0 ≤ A q) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ (D : RealTimeInterval) (θ : ℝ), 0 ≤ θ → θ ≤ T → Ioo 0 θ ⊆ D.regular →
      ∀ S : SolutionOn (I := I) (M := M) D, IsSolutionOn S →
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
            (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
              (S.base.metric p.1) x₀ p.2 i j)
            (Icc 0 θ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
        (∀ t ∈ Icc 0 θ, MetricUniformEquivalentOn U R (S.base.metric t) Λ) →
        (∀ q, 1 ≤ q → q ≤ N → ∀ x ∈ U,
          metricCovDerivNorm q (S.base.metric 0) R x ≤ A q) →
        MovingShiBoundOn U 0 θ (fun _ t => S.base.metric t) N K →
        ∀ V : Set M, V ⊆ U → ∀ s ∈ Icc 0 θ, ∀ t ∈ Icc 0 θ,
          metricDerivNormSupOn V N (S.base.metric s) (S.base.metric t) R ≤ L * |s - t| := by
  classical
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨C, hC, hCbound⟩ := exists_local_closed_metric_covariant_bounds U hU R N T Λ K hΛ hK A hA
  let cf := fun q => ricTowerCoeffs (Module.finrank ℝ E) q Λ C K
  let Lq := fun q => if q = 0 then 2 * Λ * K else 2 * ((cf q).slope * C q + (cf q).offset)
  have hLq (q : ℕ) : 0 ≤ Lq q := by
    by_cases hq : q = 0
    · simp only [Lq, if_pos hq]
      positivity
    · have hc := ricCoeffs_nonneg (Module.finrank ℝ E) q Λ C K hΛ hK
      simp only [Lq, if_neg hq]
      exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hc.1 (hC q)) hc.2)
  refine ⟨∑ q ∈ Finset.range (N + 1), Lq q, Finset.sum_nonneg (fun q _ => hLq q), ?_⟩
  intro D θ hθ hθT hreg S hS hgram hequiv hinit hShi V hVU s hs t ht
  have hnorm := hCbound D θ hθ hθT hreg S hS hgram hequiv hinit hShi
  apply metricDerivNormSupOn_le_of_forall V N _ _ R _
    (mul_nonneg (Finset.sum_nonneg (fun q _ => hLq q)) (abs_nonneg _))
  intro q hq x hx
  let Ev := fun r (y : M) => (-2 : ℝ) • nablaRicReal (fun _ u => S.base.metric u) R q 0 r y
  have hev : ∀ y ∈ U, ∀ r ∈ Ioo 0 θ, ∀ v : Fin (q + 2) → TangentSpace I y,
      HasDerivAt (fun u => metricCovDeriv (S.base.metric u) R q y v) (Ev r y v) r := by
    intro y _ r hr v
    have hwin : ∀ _i : ℕ, Icc r r ⊆ D.regular := by
      intro _ z hz
      have he : z = r := le_antisymm hz.2 hz.1
      exact he ▸ hreg hr
    exact hevComp_of_solutions (I := I) (N := q) (gRef := R)
      (fun _ => D) (fun _ => S) (fun _ => hS) (fun _ _ => rfl) hwin
      (fun _ => solutionTowerSwap_regularity R S hS q (fun {z} hz => D.regular_isOpen.mem_nhds hz))
      0 y r ⟨le_rfl, le_rfl⟩ v
  have hEv : ∀ y ∈ U, ∀ r ∈ Ioo 0 θ,
      Real.sqrt (normSq0S R y (q + 2) (Ev r y)) ≤ Lq q := by
    intro y hy r hr
    have hrc : r ∈ Icc 0 θ := Ioo_subset_Icc_self hr
    dsimp only [Ev]
    rw [sqrt_normSq0S_smul, show |(-2 : ℝ)| = 2 by norm_num]
    by_cases hzero : q = 0
    · subst q
      simp only [Lq, if_pos rfl]
      have hcomp := sqrt_normSq0S_le_of_metric_equiv (g := S.base.metric r) (h := R) y 2 hΛ
        (fun v => (metricUniformEquivalentOn_symm (hequiv r hrc)).2 y hy v)
        (nablaRicReal (fun _ u => S.base.metric u) R 0 0 r y)
      rw [Real.sqrt_sq (zero_le_one.trans hΛ)] at hcomp
      have hh := hShi 0 (Nat.zero_le N) 0 r hrc y hy
      have hn : Real.sqrt (normSq0S (S.base.metric r) y 2
          (nablaRicReal (fun _ u => S.base.metric u) R 0 0 r y)) ≤ K := hh
      nlinarith
    · have hc := ricCoeffs_nonneg (Module.finrank ℝ E) q Λ C K hΛ hK
      have hh := ric_bound_field_on (I := I) (gSeq := fun _ u => S.base.metric u)
        (gRef := R) hU q (Nat.one_le_iff_ne_zero.mpr hzero) Λ hΛ
        (fun _ => hequiv) C
        (fun a ha haq _ u hu z hz => hnorm a ha (by omega) u hu z hz)
        K hK (fun a ha => hShi a (ha.trans hq)) 0 r hrc y hy
      have hh' := hh.trans (add_le_add
        (mul_le_mul_of_nonneg_left (hnorm q (by omega) hq r hrc y hy) hc.1) le_rfl)
      simp only [Lq, if_neg hzero]
      exact mul_le_mul_of_nonneg_left hh' (by norm_num)
  have hlip := metricDerivNorm_le_of_closed_evolution S.base.metric 0 θ hgram R q Ev U
    (Lq q) (hLq q) hev hEv s hs t ht x (hVU hx)
  have hsum : Lq q ≤ ∑ a ∈ Finset.range (N + 1), Lq a :=
    Finset.single_le_sum (fun a _ => hLq a) (Finset.mem_range.mpr (by omega))
  exact hlip.trans (mul_le_mul_of_nonneg_right hsum (abs_nonneg _))

end DifferentialGeometry.PDE.RicciFlow
