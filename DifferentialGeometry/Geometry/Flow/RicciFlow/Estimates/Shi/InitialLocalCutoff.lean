import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialLocalEndpointHorizon

set_option autoImplicit false
noncomputable section
open Set Bundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

universe u

theorem exists_uniform_initial_curvature_derivative_bound_on_compact_ball
    (N : ℕ) (T R K : ℝ) (hT : 0 < T) (hR : 0 < R) (A : ℕ → ℝ)
    (hA : ∀ j, 1 ≤ j → j ≤ N → 0 ≤ A j) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace H X]
      [IsManifold I ∞ X] [T2Space X] [SigmaCompactSpace X],
      ∀ (D : RealTimeInterval)
      (S : SolutionOn (I := I) (M := X) D), IsSolutionOn S →
      Icc 0 T ⊆ D.carrier → Ioc 0 T ⊆ D.regular →
      (∀ (x₀ : X) (i j : Fin (Module.finrank ℝ E)),
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × X => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
            (S.base.metric p.1) x₀ p.2 i j)
          (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) →
      ∀ p : X,
      IsCompact {x : X | riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal R} →
      (∀ t ∈ Icc 0 T, ∀ x : X,
        riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal R →
          nablaKRm04NormSqIntrinsic S 0 t x ≤ K) →
      (∀ k, 1 ≤ k → k ≤ N → ∀ x : X,
        riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal R →
          nablaKRm04NormSqIntrinsic S k 0 x ≤ A k) →
      ∀ k ≤ N, ∀ t ∈ Icc 0 T, ∀ x : X,
        riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal (R / 2) →
          nablaKRm04NormSqIntrinsic S k t x ≤ B := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_uniform_initial_curvature_derivative_bound_on_compact_ball_of_open_regular_interval
      (I := I) N T R K hR A hA
  refine ⟨B, hB, ?_⟩
  intro X _ _ _ _ _ D S hS hslab hreg
  exact hbound X D S T hT le_rfl hS hslab (fun t ht => hreg ⟨ht.1, ht.2.le⟩)

end DifferentialGeometry.PDE.RicciFlow
