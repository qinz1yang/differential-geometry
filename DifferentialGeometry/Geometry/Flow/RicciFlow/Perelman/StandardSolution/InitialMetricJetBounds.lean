import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointMetricBounds
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Self
import DifferentialGeometry.Geometry.Operator.Laplacian.Rough
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

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

theorem exists_uniform_closed_initial_metric_bounds {D : RealTimeInterval}
    (T : ℝ) (hT : 0 ≤ T) (hreg : Ioo 0 T ⊆ D.regular)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (κ : ℕ → ℝ) (hκ : ∀ N, 0 ≤ κ N) :
    ∃ C : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧
      ∀ S : SolutionOn (I := I) (M := M) D, IsSolutionOn S →
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
            (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
            (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
        (∀ t ∈ Icc 0 T,
          MetricUniformEquivalentOn univ (S.base.metric 0) (S.base.metric t) Λ) →
        (∀ N : ℕ, MovingShiBoundOn univ 0 T (fun _ t => S.base.metric t) N (κ N)) →
        ∀ N : ℕ, ∀ t ∈ Icc 0 T, ∀ x : M,
          metricCovDerivNorm N (S.base.metric t) (S.base.metric 0) x ≤ C N := by
  classical
  let Good := fun S : SolutionOn (I := I) (M := M) D =>
    IsSolutionOn S ∧
      (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
          (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
      (∀ t ∈ Icc 0 T,
        MetricUniformEquivalentOn univ (S.base.metric 0) (S.base.metric t) Λ) ∧
      ∀ N : ℕ, MovingShiBoundOn univ 0 T (fun _ t => S.base.metric t) N (κ N)
  have hb : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SolutionOn (I := I) (M := M) D, Good S →
        ∀ t ∈ Icc 0 T, ∀ x : M,
          metricCovDerivNorm N (S.base.metric t) (S.base.metric 0) x ≤ C := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      by_cases hN : N = 0
      · subst N
        exact ⟨Real.sqrt (Λ ^ 2) * Real.sqrt (Module.finrank ℝ E), by positivity,
          fun S hS t ht x => zero_norm_bound _ _ Λ hΛ (hS.2.2.1 t ht) x⟩
      · let Cg := fun r => if hr : r < N then (ih r hr).choose else 0
        have hCg (r : ℕ) (hr : r < N) : 0 ≤ Cg r ∧
            ∀ S : SolutionOn (I := I) (M := M) D, Good S →
              ∀ t ∈ Icc 0 T, ∀ x : M,
                metricCovDerivNorm r (S.base.metric t) (S.base.metric 0) x ≤ Cg r := by
          simpa only [Cg, dif_pos hr] using (ih r hr).choose_spec
        let cf := ricTowerCoeffs (Module.finrank ℝ E) N Λ Cg (κ N)
        refine ⟨metricCovOrderEvolutionConstant cf.slope cf.offset T 0, Real.sqrt_nonneg _, ?_⟩
        intro S hS t ht x
        obtain ⟨hSol, hgram, hequiv, hShi⟩ := hS
        apply metricCovOrderBound_stage_closed S hSol T hT hreg hgram (S.base.metric 0)
          univ isOpen_univ N (Nat.one_le_iff_ne_zero.mpr hN) Λ hΛ hequiv Cg
          (fun r _ hr s hs y _ => (hCg r hr).2 S ⟨hSol, hgram, hequiv, hShi⟩ s hs y)
          (κ N) (hκ N) (hShi N) 0 le_rfl ?_ t ht x (mem_univ x)
        intro y _
        obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
        rw [covNorm_self_succ (S.base.metric 0) r y]
  choose C hC hbound using hb
  exact ⟨C, hC, fun S hS hgram hequiv hShi N t ht x =>
    hbound N S ⟨hS, hgram, hequiv, hShi⟩ t ht x⟩
end DifferentialGeometry.PDE.RicciFlow
