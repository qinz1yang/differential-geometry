import DifferentialGeometry.Geometry.Metric.LoopDistance



noncomputable section

open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal Uniformity

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T3Space M] [PreconnectedSpace M]

omit [T3Space M] [PreconnectedSpace M] in
theorem riemannianLoopDistance_self (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M) :
    riemannianLoopDistance g γ γ = 0 := by
  simp [riemannianLoopDistance, riemannianEDistOf_self]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem continuous_riemannianLoopDistance {X : Type*} [TopologicalSpace X]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Γ Δ : X → freeLoop M}
    (hΓ : Continuous Γ) (hΔ : Continuous Δ) :
    Continuous (fun x => (riemannianLoopDistance g (Γ x) (Δ x) : ℝ)) := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let : MetricSpace M := EMetricSpace.toMetricSpace DifferentialGeometry.Analysis.edist_ne_top_of_preconnected
  have hd (γ₀ γ₁ : freeLoop M) : (riemannianLoopDistance g γ₀ γ₁ : ℝ) = dist γ₀ γ₁ := by
    rw [riemannianLoopDistance_eq_iSup]
    change (⨆ θ, (edist (γ₀ θ) (γ₁ θ)).toReal) = dist γ₀ γ₁
    simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using!
      (ContinuousMap.dist_eq_iSup (f := γ₀) (g := γ₁)).symm
  exact (hΓ.dist hΔ).congr (fun x => (hd (Γ x) (Δ x)).symm)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [PreconnectedSpace M] in
theorem eventually_forall_riemannianEDist_lt (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ : freeLoop M) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ γ : freeLoop M in 𝓝 γ₀, ∀ θ : loopCircle, riemannianEDistOf g (γ θ) (γ₀ θ) < ε := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let metricM : EMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hed : ∀ x y : M, edist x y = riemannianEDistOf g x y := fun _ _ => rfl
  have hV : {p : M × M | edist p.1 p.2 < ε} ∈ uniformity M :=
    (mem_uniformity_edist).mpr ⟨ε, hε, fun {_ _} h => h⟩
  have hE : {fg : freeLoop M × freeLoop M |
      ∀ x ∈ (univ : Set loopCircle),
        (fg.1 x, fg.2 x) ∈ {p : M × M | edist p.1 p.2 < ε}} ∈
      uniformity (freeLoop M) := by
    rw [ContinuousMap.mem_compactConvergence_entourage_iff]
    exact ⟨univ, {p : M × M | edist p.1 p.2 < ε}, isCompact_univ, hV, subset_rfl⟩
  filter_upwards [UniformSpace.ball_mem_nhds γ₀ hE] with γ hγ θ
  have h : riemannianEDistOf g (γ₀ θ) (γ θ) < ε := by
    simpa only [hed] using hγ θ (mem_univ θ)
  rwa [riemannianEDistOf_comm] at h

end DifferentialGeometry.Geometry
