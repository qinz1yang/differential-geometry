import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointMixedBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureBounds

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem original_regular_dense (S : PartialStandardSolution) :
    S.domain ⊆ closure (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
  change (lifetimeInterval S.lifetime S.lifetime_pos).carrier ⊆
    closure (lifetimeInterval S.lifetime S.lifetime_pos).regular
  by_cases htop : S.lifetime = ⊤
  · simpa only [lifetimeInterval, htop, dite_true, RealTimeInterval.closedInfinite, closure_Ioi] using
      (subset_rfl : Ici (0 : ℝ) ⊆ Ici 0)
  · have hp : 0 < S.lifetime.toReal := ENNReal.toReal_pos S.lifetime_pos.ne' htop
    simpa only [lifetimeInterval, htop, dite_false, RealTimeInterval.closedOpen, closure_Ioo hp.ne] using
      (Ico_subset_Icc_self : Ico (0 : ℝ) S.lifetime.toReal ⊆ Icc 0 S.lifetime.toReal)

private theorem mixed_bound_of_curvature (S : PartialStandardSolution)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθT : ENNReal.ofReal θ < S.lifetime)
    (N : ℕ) (K : ℝ) (A : ℕ → ℝ)
    (hcurv : ∀ t ∈ Icc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ K)
    (hinit : ∀ k : ℕ, ∀ x : E3,
      Real.sqrt (nablaKRm04NormSqIntrinsic S.toSolutionOn k 0 x) ≤ A k) :
    ∀ a b : ℕ, a + 2 * b ≤ N → ∀ t ∈ Icc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (S.metric t) x (4 + a)
        (iteratedCovariantTimeDerivWithin S.metric
          (fun r => nablaKRm04Field S.toSolutionOn r a x) S.domain b t)) ≤
        endpointMixedCurvatureBound 3 N θ K A := by
  have hslab := (Icc_subset_lifetimeInterval_iff S.lifetime S.lifetime_pos θ hθ).mpr hθT
  have hreg : Ioo 0 θ ⊆ (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
    intro t ht
    exact (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos t).mpr
      ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2.le).trans_lt hθT⟩
  have hg := chartGram_contMDiffOn_of_cartesian S.metric S.domain S.smooth
  have hh := curvature_endpoint_mixed_bound θ hθ N K A _ S.toSolutionOn S.isSolutionOn
    (uniqueDiffOn_lifetimeInterval S.lifetime S.lifetime_pos) hg (original_regular_dense S)
    (Or.inl (S.complete 0 (hslab ⟨le_rfl, hθ⟩))) hslab hreg hcurv
    (fun k _ x => hinit k x)
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hh
  convert hh using 1
  rfl

theorem PartialStandardSolution.curvature_mixed_bounds_closed (S : PartialStandardSolution)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθT : ENNReal.ofReal θ < S.lifetime) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℕ, a + 2 * b ≤ N → ∀ t ∈ Icc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (S.metric t) x (4 + a)
        (iteratedCovariantTimeDerivWithin S.metric
          (fun r => nablaKRm04Field S.toSolutionOn r a x) S.domain b t)) ≤ C := by
  obtain ⟨A, _, hi⟩ := standard_initial_curvature_derivative_bounds
  obtain ⟨K, _, hK⟩ := S.curvature_bound θ hθ hθT
  exact ⟨endpointMixedCurvatureBound 3 N θ K A,
    endpointMixedCurvatureBound_nonneg _ _ _ _ _,
    mixed_bound_of_curvature S θ hθ hθT N K A hK (hi S)⟩

theorem uniformStandardLifetime_mixed_bounds_closed
    (θ : ℝ) (hθ : 0 ≤ θ) (hθT : ENNReal.ofReal θ < uniformStandardLifetime) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : StandardSolution,
      ∀ a b : ℕ, a + 2 * b ≤ N → ∀ t ∈ Icc 0 θ, ∀ x : E3,
        Real.sqrt (normSq0S (S.val.metric t) x (4 + a)
          (iteratedCovariantTimeDerivWithin S.val.metric
            (fun r => nablaKRm04Field S.val.toSolutionOn r a x) S.val.domain b t)) ≤ C := by
  obtain ⟨A, _, hi⟩ := standard_initial_curvature_derivative_bounds
  obtain ⟨hlife, K, _, hK⟩ := uniformStandardLifetime_slab θ hθ hθT
  exact ⟨endpointMixedCurvatureBound 3 N θ K A,
    endpointMixedCurvatureBound_nonneg _ _ _ _ _,
    fun S => mixed_bound_of_curvature S.val θ hθ (hlife S) N K A (hK S) (hi S.val)⟩
end DifferentialGeometry.PDE.RicciFlow
