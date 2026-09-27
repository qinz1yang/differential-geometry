import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {D : RealTimeInterval}

section

variable [T2Space M]

omit [T2Space M] in
theorem lCost_le_lRegularizedAction_of_scalar_nonneg
    (S : SolutionOn (I := I) (M := M) D) {T tau : ℝ} (htau : 0 ≤ tau)
    (hscalar : ∀ s ∈ Icc 0 tau, ∀ z : M, 0 ≤ S.scalar (T - s) z)
    (alpha : ℝ → M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) :
    lCost S T (alpha 0) (alpha (Real.sqrt tau)) tau ≤
      lRegularizedAction S T alpha 0 (Real.sqrt tau) := by
  rw [← lLength_squareRootReparametrization_eq_lRegularizedAction S T alpha tau htau]
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨beta, _, _, _, rfl⟩
    apply intervalIntegral.integral_nonneg htau
    intro s hs
    exact mul_nonneg (Real.sqrt_nonneg s) (add_nonneg
      (hscalar s hs _) (lSpeedSq_nonneg S T _ s))
  · exact ⟨alpha, halpha, rfl, rfl, rfl⟩

end

theorem exists_lRegularizedAction_lt_of_lCost_lt
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x y : M)
    (tau : ℝ) (htau : 0 ≤ tau)
    (hreach : ∃ alpha : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
      alpha 0 = x ∧ alpha (Real.sqrt tau) = y)
    (A : ℝ) (hA : lCost S T x y tau < A) :
    ∃ alpha : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
      alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
        lRegularizedAction S T alpha 0 (Real.sqrt tau) < A := by
  obtain ⟨alpha₀, halpha₀, ha₀, hb₀⟩ := hreach
  have hne : {r : ℝ | ∃ alpha : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
      alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
        lLength S T (squareRootReparametrization alpha) 0 tau = r}.Nonempty :=
    ⟨_, alpha₀, halpha₀, ha₀, hb₀, rfl⟩
  obtain ⟨r, ⟨alpha, halpha, ha, hb, hr⟩, hlt⟩ := exists_lt_of_csInf_lt hne hA
  refine ⟨alpha, halpha, ha, hb, ?_⟩
  rw [← lLength_squareRootReparametrization_eq_lRegularizedAction S T alpha tau htau, hr]
  exact hlt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_lRegularizedAction_lt_of_lCost_lt_of_preconnected
    [PreconnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x y : M)
    (tau : ℝ) (htau : 0 < tau) (A : ℝ) (hA : lCost S T x y tau < A) :
    ∃ alpha : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
      alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
        lRegularizedAction S T alpha 0 (Real.sqrt tau) < A := by
  apply exists_lRegularizedAction_lt_of_lCost_lt S T x y tau htau.le ?_ A hA
  let _ : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(S.base.metric T).toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨(S.base.metric T).inner, (S.base.metric T).contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  obtain ⟨alpha, ha, hb, halpha, _, _, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt
      (Manifold.riemannianEDist_lt_top (I := I) x y) (Real.sqrt_pos.2 htau)
  exact ⟨alpha, halpha, ha, hb⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
