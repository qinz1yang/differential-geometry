import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialFlowComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.LocalWindowCurvatureHorizon

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private local instance (V : TopologicalSpace.Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)

theorem exists_uniform_initial_standard_cap_comparison_of_local_curvature
    (D r T K ε : ℝ) (hr : 0 < r) (hfit : 64 * r < D)
    (hT : 0 < T) (hε : 0 < ε) (N : ℕ) :
    ∃ η ε₀ : ℝ, 0 < η ∧ η ≤ T ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {m : ℕ} {ζ : ℝ}
        (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      N+2 ≤ m → ζ ≤ ε₀ →
      ∀ (J : RealTimeInterval) (θ : ℝ), 0 < θ → θ ≤ T →
        Icc 0 θ ⊆ J.carrier → Ioo 0 θ ⊆ J.regular →
        ∀ L : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
        IsSolutionOn L → L.base.metric 0 = w.windowMetric →
        (∀ (p : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun q : ℝ × standardCapWindow D =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (L.base.metric q.1) p q.2 i j)
            (Icc 0 θ ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)) →
        (∀ t ∈ Icc 0 θ, ∀ x : standardCapWindow D, ‖x.val‖ ≤ 64*r →
          nablaKRm04NormSqIntrinsic L 0 t x ≤ K) →
        ∀ S : StandardSolution, ∀ t ∈ Icc 0 (min η θ),
          metricDerivNormSupOn {x : standardCapWindow D | ‖x.val‖ ≤ r} N
            (L.base.metric t) ((S.val.metric t).restrictOpen (standardCapWindow D))
            (standardCapMetric.restrictOpen (standardCapWindow D)) < ε := by
  obtain ⟨B, hB, hcurv⟩ :=
    exists_uniform_window_flow_curvature_derivative_bound_of_local_curvature_bounded_horizon
      N (64 * r) T K (by positivity)
  obtain ⟨η,ε₀,hη,hηT,hε₀,hε₀half,hcompare⟩ :=
    exists_uniform_initial_standard_cap_comparison D r (2*r) T ε (by linarith)
      (by linarith) hT hε N (fun _ => Real.sqrt B)
  refine ⟨η,ε₀,hη,hηT,hε₀,hε₀half,?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A hA m ζ w hm hζ
    J θ hθ hθT hcarrier hregular L hL hzero hgram hlocal
  have hjets := hcurv w (hζ.trans hε₀half) hm hfit J θ hθ hθT
    hcarrier hregular L hL hzero hgram hlocal
  apply hcompare w (by omega) hζ J θ hθ.le hθT hcarrier hregular L hL hzero hgram
  intro j hj t ht x hx
  unfold curvDerivNorm
  rw [curvNormSq_eq]
  apply Real.sqrt_le_sqrt
  apply hjets j hj t ht x
  have he : (64*r)/32 = 2*r := by ring
  rw [he]
  exact hx.le

end DifferentialGeometry.PDE.RicciFlow.StandardCap
