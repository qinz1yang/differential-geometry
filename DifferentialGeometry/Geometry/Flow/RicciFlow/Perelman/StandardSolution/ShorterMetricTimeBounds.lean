import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialMetricTimeBounds
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.TimeRegularity

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [I.Boundaryless] in
private theorem zero_norm_bound (g gRef : SmoothRiemannianMetric I M) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (he : MetricUniformEquivalentOn univ gRef g Λ) (x : M) :
    metricCovDerivNorm 0 g gRef x ≤ Real.sqrt (Λ ^ 2) * Real.sqrt (Module.finrank ℝ E) := by
  classical
  have hsymm := metricUniformEquivalentOn_symm he
  have hc := sqrt_normSq0S_le_of_metric_equiv (g := g) (h := gRef) x 2 hΛ
    (fun v => hsymm.2 x (mem_univ x) v) (metricTensor0S g x)
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis g x
  have hinv : MetricInverseInBasis g x basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) := by
    have hh := metricInverseInBasis_of_orthonormal g basis hON
    intro i j
    simpa only [identityInvMetric, diagonalInvMetric] using hh i j
  have hcard := normSq0S_metricTensor0S_eq_card g basis
    (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I x)))) hinv
  rw [Fintype.card_fin, show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl] at hcard
  have hz : metricCovDerivNorm 0 g gRef x = Real.sqrt (normSq0S gRef x 2 (metricTensor0S g x)) := by
    change Real.sqrt (normSq0S gRef x 2 (metricTensorField g x)) = _
    have heq : metricTensorField g x = metricTensor0S g x := by
      ext v
      rw [metricTensorField_apply, metricTensor0S_apply]
    rw [heq]
  rw [hz]
  simpa only [hcard] using hc

private theorem time_constant_mono (C B s T A : ℝ) (hsT : s ≤ T) :
    metricCovOrderEvolutionConstant C B s A ≤ metricCovOrderEvolutionConstant C B T A := by
  unfold metricCovOrderEvolutionConstant metricCovOrderEvolutionAlpha metricCovOrderEvolutionBeta
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_right
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hsT (by positivity)
  · positivity

private theorem exists_shorter_spatial_bounds (T Λ : ℝ) (hΛ : 1 ≤ Λ)
    (κ : ℕ → ℝ) (hκ : ∀ N, 0 ≤ κ N) :
    ∃ C : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧
      ∀ (D : RealTimeInterval) (θ : ℝ), 0 ≤ θ → θ ≤ T → Ioo 0 θ ⊆ D.regular →
      ∀ S : SolutionOn (I := I) (M := M) D, IsSolutionOn S →
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
            (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
            (Icc 0 θ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
        (∀ t ∈ Icc 0 θ,
          MetricUniformEquivalentOn univ (S.base.metric 0) (S.base.metric t) Λ) →
        (∀ N : ℕ, MovingShiBoundOn univ 0 θ (fun _ t => S.base.metric t) N (κ N)) →
        ∀ N : ℕ, ∀ t ∈ Icc 0 θ, ∀ x : M,
          metricCovDerivNorm N (S.base.metric t) (S.base.metric 0) x ≤ C N := by
  classical
  let Good := fun (D : RealTimeInterval) (θ : ℝ) (S : SolutionOn (I := I) (M := M) D) =>
    IsSolutionOn S ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
          (Icc 0 θ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ t ∈ Icc 0 θ,
        MetricUniformEquivalentOn univ (S.base.metric 0) (S.base.metric t) Λ) ∧
      ∀ N : ℕ, MovingShiBoundOn univ 0 θ (fun _ t => S.base.metric t) N (κ N)
  have hb : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (D : RealTimeInterval) (θ : ℝ), 0 ≤ θ → θ ≤ T → Ioo 0 θ ⊆ D.regular →
      ∀ S : SolutionOn (I := I) (M := M) D, Good D θ S →
        ∀ t ∈ Icc 0 θ, ∀ x : M,
          metricCovDerivNorm N (S.base.metric t) (S.base.metric 0) x ≤ C := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      by_cases hN : N = 0
      · subst N
        exact ⟨Real.sqrt (Λ ^ 2) * Real.sqrt (Module.finrank ℝ E), by positivity,
          fun D θ _ _ _ S hS t ht x => zero_norm_bound _ _ Λ hΛ (hS.2.2.1 t ht) x⟩
      · let Cg := fun r => if hr : r < N then (ih r hr).choose else 0
        have hCg (r : ℕ) (hr : r < N) : 0 ≤ Cg r ∧
            ∀ (D : RealTimeInterval) (θ : ℝ), 0 ≤ θ → θ ≤ T → Ioo 0 θ ⊆ D.regular →
            ∀ S : SolutionOn (I := I) (M := M) D, Good D θ S →
              ∀ t ∈ Icc 0 θ, ∀ x : M,
                metricCovDerivNorm r (S.base.metric t) (S.base.metric 0) x ≤ Cg r := by
          simpa only [Cg, dite_eq_left hr] using (ih r hr).choose_spec
        let cf := ricTowerCoeffs (Module.finrank ℝ E) N Λ Cg (κ N)
        refine ⟨metricCovOrderEvolutionConstant cf.slope cf.offset T 0, Real.sqrt_nonneg _, ?_⟩
        intro D θ hθ hθT hreg S hS t ht x
        obtain ⟨hSol, hgram, hequiv, hShi⟩ := hS
        have hh := metricCovOrderBound_stage_closed S hSol θ hθ hreg hgram (S.base.metric 0)
          univ isOpen_univ N (Nat.one_le_iff_ne_zero.mpr hN) Λ hΛ hequiv Cg
          (fun r _ hr s hs y _ => (hCg r hr).2 D θ hθ hθT hreg S ⟨hSol, hgram, hequiv, hShi⟩ s hs y)
          (κ N) (hκ N) (hShi N) 0 le_rfl (by
            intro y _
            obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
            rw [covNorm_self_succ (S.base.metric 0) r y]) t ht x (mem_univ x)
        exact hh.trans (time_constant_mono cf.slope cf.offset θ T 0 hθT)
  choose C hC hbound using hb
  exact ⟨C, hC, fun D θ hθ hθT hreg S hS hgram hequiv hShi N t ht x =>
    hbound N D θ hθ hθT hreg S ⟨hS, hgram, hequiv, hShi⟩ t ht x⟩

omit [CompleteSpace E] [I.Boundaryless] in
private theorem reference_ricci_zero_bound {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (gRef : SmoothRiemannianMetric I M)
    (t Λ κ : ℝ) (hΛ : 1 ≤ Λ)
    (he : MetricUniformEquivalentOn univ gRef (S.base.metric t) Λ)
    (x : M)
    (hRic : Real.sqrt (normSq0S (S.base.metric t) x 2
      (ricCovTower (S.base.metric t) (S.base.metric t) 0 x)) ≤ κ) :
    Real.sqrt (normSq0S gRef x 2
      (nablaRicReal (fun _ s => S.base.metric s) gRef 0 0 t x)) ≤ Λ * κ := by
  have hh := sqrt_normSq0S_le_of_metric_equiv (g := S.base.metric t) (h := gRef) x 2 hΛ
    (fun v => (metricUniformEquivalentOn_symm he).2 x (mem_univ x) v)
    (nablaRicReal (fun _ s => S.base.metric s) gRef 0 0 t x)
  rw [Real.sqrt_sq (le_trans (by norm_num : (0 : ℝ) ≤ 1) hΛ)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hRic (le_trans (by norm_num) hΛ))

private theorem reference_metric_interior_evolution {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (gRef : SmoothRiemannianMetric I M) (a : ℕ) {s : ℝ} (hs : s ∈ D.regular)
    (x : M) (v : Fin (a + 2) → TangentSpace I x) :
    HasDerivAt (fun r => metricCovDeriv (S.base.metric r) gRef a x v)
      (((-2 : ℝ) • nablaRicReal (fun _ t => S.base.metric t) gRef a 0 s x) v) s := by
  have hwin : ∀ _i : ℕ, Icc s s ⊆ D.regular := by
    intro _ r hr
    have he : r = s := le_antisymm hr.2 hr.1
    exact he ▸ hs
  exact hevComp_of_solutions (I := I) (N := a) (gRef := gRef)
    (fun _ => D) (fun _ => S) (fun _ => hS) (fun _ _ => rfl) hwin
    (fun _ => solutionTowerSwap_regularity gRef S hS a (fun {t} ht => D.regular_isOpen.mem_nhds ht))
    0 x s ⟨le_rfl, le_rfl⟩ v

theorem exists_uniform_shorter_initial_metric_time_bounds
    (T Λ : ℝ) (hΛ : 1 ≤ Λ) (κ : ℕ → ℝ) (hκ : ∀ N, 0 ≤ κ N) :
    ∃ C L : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧
      ∀ (D : RealTimeInterval) (θ : ℝ), 0 ≤ θ → θ ≤ T → Ioo 0 θ ⊆ D.regular →
      ∀ S : SolutionOn (I := I) (M := M) D, IsSolutionOn S →
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
            (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
            (Icc 0 θ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
        (∀ t ∈ Icc 0 θ,
          MetricUniformEquivalentOn univ (S.base.metric 0) (S.base.metric t) Λ) →
        (∀ N : ℕ, MovingShiBoundOn univ 0 θ (fun _ t => S.base.metric t) N (κ N)) →
        (∀ N : ℕ, ∀ t ∈ Icc 0 θ, ∀ x : M,
          metricCovDerivNorm N (S.base.metric t) (S.base.metric 0) x ≤ C N) ∧
        ∀ N : ℕ, ∀ s ∈ Icc 0 θ, ∀ t ∈ Icc 0 θ, ∀ x : M,
          metricDerivNorm N (S.base.metric s) (S.base.metric t) (S.base.metric 0) x ≤ L N * |s - t| := by
  obtain ⟨C, hC, hCbound⟩ := exists_shorter_spatial_bounds (I := I) (M := M) T Λ hΛ κ hκ
  let cf := fun N => ricTowerCoeffs (Module.finrank ℝ E) N Λ C (κ N)
  let L := fun N => if N = 0 then 2 * Λ * κ 0 else 2 * ((cf N).slope * C N + (cf N).offset)
  have hL (N : ℕ) : 0 ≤ L N := by
    by_cases hN : N = 0
    · simp only [L, ite_eq_left hN]
      exact mul_nonneg (mul_nonneg (by norm_num) (le_trans (by norm_num) hΛ)) (hκ 0)
    · have hc := ricCoeffs_nonneg (Module.finrank ℝ E) N Λ C (κ N) hΛ (hκ N)
      simp only [L, ite_eq_right hN]
      exact mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hc.1 (hC N)) hc.2)
  refine ⟨C, L, hC, hL, ?_⟩
  intro D θ hθ hθT hreg S hS hgram hequiv hShi
  have hnorm := hCbound D θ hθ hθT hreg S hS hgram hequiv hShi
  refine ⟨hnorm, ?_⟩
  intro N s hs t ht x
  let Ev := fun r (y : M) => (-2 : ℝ) •
    nablaRicReal (fun _ u => S.base.metric u) (S.base.metric 0) N 0 r y
  have hev : ∀ y ∈ (univ : Set M), ∀ r ∈ Ioo 0 θ, ∀ v : Fin (N + 2) → TangentSpace I y,
      HasDerivAt (fun u => metricCovDeriv (S.base.metric u) (S.base.metric 0) N y v) (Ev r y v) r :=
    fun y _ r hr v => reference_metric_interior_evolution S hS (S.base.metric 0) N (hreg hr) y v
  have hEv : ∀ y ∈ (univ : Set M), ∀ r ∈ Ioo 0 θ,
      Real.sqrt (normSq0S (S.base.metric 0) y (N + 2) (Ev r y)) ≤ L N := by
    intro y _ r hr
    have hrc : r ∈ Icc 0 θ := Ioo_subset_Icc_self hr
    dsimp only [Ev]
    rw [sqrt_normSq0S_smul, show |(-2 : ℝ)| = 2 by norm_num]
    by_cases hN : N = 0
    · subst N
      simp only [L, ite_eq_left rfl]
      have hh := reference_ricci_zero_bound S (S.base.metric 0) r Λ (κ 0) hΛ (hequiv r hrc) y
        (hShi 0 0 le_rfl 0 r hrc y (mem_univ y))
      nlinarith
    · have hc := ricCoeffs_nonneg (Module.finrank ℝ E) N Λ C (κ N) hΛ (hκ N)
      have hh := ric_bound_field_on (I := I) (gSeq := fun _ u => S.base.metric u)
        (gRef := S.base.metric 0) isOpen_univ N (Nat.one_le_iff_ne_zero.mpr hN) Λ hΛ
        (fun _ => hequiv) C (fun a _ _ _ u hu z _ => hnorm a u hu z) (κ N) (hκ N) (hShi N)
        0 r hrc y (mem_univ y)
      have hh' := hh.trans (add_le_add
        (mul_le_mul_of_nonneg_left (hnorm N r hrc y) hc.1) le_rfl)
      simp only [L, ite_eq_right hN]
      exact mul_le_mul_of_nonneg_left hh' (by norm_num)
  exact metricDerivNorm_le_of_closed_evolution S.base.metric 0 θ hgram (S.base.metric 0)
    N Ev univ (L N) (hL N) hev hEv s hs t ht x (mem_univ x)
end DifferentialGeometry.PDE.RicciFlow
