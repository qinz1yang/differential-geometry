import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.LocalWindowCurvatureHorizon

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

theorem exists_uniform_window_flow_curvature_derivative_bound_of_local_curvature
    (N : ℕ) (ρ T K : ℝ) (hρ : 0 < ρ) (hT : 0 < T) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ζ : ℝ} (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      ζ ≤ 1/2 → N+2 ≤ m → ρ < D →
      ∀ (J : RealTimeInterval), Icc 0 T ⊆ J.carrier → Ioc 0 T ⊆ J.regular →
        ∀ L : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
        IsSolutionOn L → L.base.metric 0 = w.windowMetric →
        (∀ (p : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun q : ℝ × standardCapWindow D =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (L.base.metric q.1) p q.2 i j)
            (Icc 0 T ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)) →
        (∀ t ∈ Icc 0 T, ∀ x : standardCapWindow D, ‖x.val‖ ≤ ρ →
          nablaKRm04NormSqIntrinsic L 0 t x ≤ K) →
        ∀ j ≤ N, ∀ t ∈ Icc 0 T, ∀ x : standardCapWindow D, ‖x.val‖ ≤ ρ/32 →
          nablaKRm04NormSqIntrinsic L j t x ≤ B := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_uniform_window_flow_curvature_derivative_bound_of_local_curvature_bounded_horizon
      N ρ T K hρ
  refine ⟨B, hB, ?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA D m ζ w hζ hm hρD
    J hslab hreg L
  exact hbound w hζ hm hρD J T hT le_rfl hslab (fun t ht => hreg ⟨ht.1, ht.2.le⟩) L

end DifferentialGeometry.PDE.RicciFlow.StandardCap
