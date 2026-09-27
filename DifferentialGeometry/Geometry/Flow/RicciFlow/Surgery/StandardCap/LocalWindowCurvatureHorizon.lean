import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialLocalEndpointHorizon
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowIntrinsicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology ENNReal BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private local instance (V : TopologicalSpace.Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)


private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

private theorem initial_curvature_norm_le_of_metric_bound
    {D : ℝ} {J : RealTimeInterval}
    (L : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J)
    (g₀ : SmoothRiemannianMetric ThreeModel (standardCapWindow D))
    (hzero : L.base.metric 0 = g₀) (j : ℕ) (x : standardCapWindow D) {C : ℝ}
    (hb : Real.sqrt (normSq0S g₀ x (4 + j) (iterCov g₀ 4 (metricRm04 g₀) j x)) ≤ C) :
    nablaKRm04NormSqIntrinsic L j 0 x ≤ C ^ 2 := by
  rw [← curvNormSq_eq,hzero]
  unfold curvDerivNormSq
  rw [curvCovDeriv_normSq_eq]
  exact (Real.sqrt_le_iff).mp hb |>.2

theorem exists_uniform_window_flow_curvature_derivative_bound_of_local_curvature_bounded_horizon
    (N : ℕ) (ρ T K : ℝ) (hρ : 0 < ρ) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
        [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
        [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
        {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}
        {d : normalizedDatum g x₀ δ k} {A : ℝ} {hA : 0 < A} {D : ℝ}
        {m : ℕ} {ζ : ℝ} (w : CanonicalStaticInsertionWitness d A hA D m ζ),
      ζ ≤ 1/2 → N+2 ≤ m → ρ < D →
      ∀ (J : RealTimeInterval) (θ : ℝ), 0 < θ → θ ≤ T →
        Icc 0 θ ⊆ J.carrier → Ioo 0 θ ⊆ J.regular →
        ∀ L : SolutionOn (I := ThreeModel) (M := standardCapWindow D) J,
        IsSolutionOn L → L.base.metric 0 = w.windowMetric →
        (∀ (p : standardCapWindow D) (i j : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
            (fun q : ℝ × standardCapWindow D =>
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (L.base.metric q.1) p q.2 i j)
            (Icc 0 θ ×ˢ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet)) →
        (∀ t ∈ Icc 0 θ, ∀ x : standardCapWindow D, ‖x.val‖ ≤ ρ →
          nablaKRm04NormSqIntrinsic L 0 t x ≤ K) →
        ∀ j ≤ N, ∀ t ∈ Icc 0 θ, ∀ x : standardCapWindow D, ‖x.val‖ ≤ ρ/32 →
          nablaKRm04NormSqIntrinsic L j t x ≤ B := by
  classical
  choose A hA hinit using exists_uniform_window_curvature_derivative_bounds
  obtain ⟨B,hB,hbound⟩ :=
    exists_uniform_initial_curvature_derivative_bound_on_compact_ball_of_open_regular_interval
    (I := ThreeModel) N T (ρ/4) K (by positivity) (fun j => (A j)^2)
    (fun _ _ _ => sq_nonneg _)
  refine ⟨B,hB,?_⟩
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ δ k d A₀ hA₀ D m ζ w hζ hm hρD
    J θ hθ hθT hslab hreg L hL hzero hgram hcurv j hj t ht x hx
  obtain ⟨p,hp,hcompact,hcapture,hinner⟩ :=
    CanonicalStaticInsertionWitness.exists_window_intrinsic_ball_control w hζ hρ hρD
  have hcompactL : IsCompact {y : standardCapWindow D |
      riemannianEDistOf (L.base.metric 0) p y ≤ ENNReal.ofReal (ρ/4)} := by
    rwa [hzero]
  have houter (y : standardCapWindow D)
      (hy : riemannianEDistOf (L.base.metric 0) p y ≤ ENNReal.ofReal (ρ/4)) :
      ‖y.val‖ ≤ ρ := by
    rw [hzero] at hy
    exact hcapture hy
  apply hbound (standardCapWindow D) J L θ hθ hθT hL hslab hreg hgram p hcompactL
    (fun s hs y hy => hcurv s hs y (houter y hy))
    (fun k hk hkN y hy => initial_curvature_norm_le_of_metric_bound L w.windowMetric
      hzero k y (hinit k w hζ (by omega) y ((houter y hy).trans_lt hρD))) j hj t ht x
  rw [hzero]
  have hb := hinner x hx
  simpa only [div_div,show (4:ℝ)*2=8 by norm_num] using hb

end DifferentialGeometry.PDE.RicciFlow.StandardCap
