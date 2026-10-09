import DifferentialGeometry.Geometry.Measure.Area.GeodesicStripArea
import DifferentialGeometry.Topology.LoopSpace.CylinderLipschitz



noncomputable section

open Bundle Manifold Set DifferentialGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]



def geodesicAnnulus (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : loopCircle → M) (p : ℝ × loopCircle) : M :=
  geodesicInterpolation g (γ₀ p.2) (γ₁ p.2) (projIcc 0 1 zero_le_one p.1)

theorem geodesicAnnulus_lift (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : loopCircle → M) (z : ℂ) :
    geodesicAnnulus g γ₀ γ₁ (z.re, (z.im : loopCircle)) =
      extendedGeodesicStrip g (fun t => γ₀ (t : loopCircle)) (fun t => γ₁ (t : loopCircle)) z := rfl

theorem geodesicAnnulus_zero [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ₀ γ₁ : loopCircle → M) (θ : loopCircle) :
    geodesicAnnulus g γ₀ γ₁ (0, θ) = γ₀ θ := by
  simp only [geodesicAnnulus, projIcc_of_mem zero_le_one (left_mem_Icc.mpr zero_le_one)]
  exact (geodesicInterpolation_spec g).1 _ _

theorem geodesicAnnulus_one [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ₀ γ₁ : loopCircle → M) (θ : loopCircle)
    (h : riemannianEDistOf g (γ₀ θ) (γ₁ θ) ≠ ⊤) :
    geodesicAnnulus g γ₀ γ₁ (1, θ) = γ₁ θ := by
  simp only [geodesicAnnulus, projIcc_of_mem zero_le_one (right_mem_Icc.mpr zero_le_one)]
  exact (geodesicInterpolation_spec g).2.1 _ _ h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem geodesicAnnulus_lipschitz_of_strip
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ₀ γ₁ : loopCircle → M} {K : ℝ≥0}
    (hK : ∀ z w : ℂ,
      riemannianEDistOf g
        (extendedGeodesicStrip g (fun t => γ₀ (t : loopCircle)) (fun t => γ₁ (t : loopCircle)) z)
        (extendedGeodesicStrip g (fun t => γ₀ (t : loopCircle)) (fun t => γ₁ (t : loopCircle)) w) ≤
          (K : ℝ≥0∞) * edist z w) :
    ∃ C : ℝ≥0, ∀ p q : ℝ × loopCircle,
      riemannianEDistOf g (geodesicAnnulus g γ₀ γ₁ p) (geodesicAnnulus g γ₀ γ₁ q) ≤
        (C : ℝ≥0∞) * edist p q := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hs : LipschitzWith K
      (extendedGeodesicStrip g (fun t => γ₀ (t : loopCircle)) (fun t => γ₁ (t : loopCircle))) := hK
  have hp := hs.comp Complex.equivRealProdCLM.symm.toContinuousLinearMap.lipschitzWith
  have hc := cylinder_lipschitz_of_lift (F := geodesicAnnulus g γ₀ γ₁) hp
  exact ⟨_, hc⟩



def geodesicAnnulusArea (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : loopCircle → M) : ℝ :=
  riemannianArea g
    (extendedGeodesicStrip g (fun t => γ₀ (t : loopCircle)) (fun t => γ₁ (t : loopCircle))) unitSquare

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_geodesicAnnulus_area_bound [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    ∃ ρ C : ℝ≥0, 0 < ρ ∧ 0 < C ∧ ∀ (γ₀ γ₁ : loopCircle → M) (L₀ L₁ D : ℝ≥0),
      (∀ s t, riemannianEDistOf g (γ₀ s) (γ₀ t) ≤ (L₀ : ℝ≥0∞) * edist s t) →
      (∀ s t, riemannianEDistOf g (γ₁ s) (γ₁ t) ≤ (L₁ : ℝ≥0∞) * edist s t) →
      D ≤ ρ → (∀ t, riemannianEDistOf g (γ₀ t) (γ₁ t) ≤ (D : ℝ≥0∞)) →
      (∃ K : ℝ≥0, ∀ p q : ℝ × loopCircle,
        riemannianEDistOf g (geodesicAnnulus g γ₀ γ₁ p) (geodesicAnnulus g γ₀ γ₁ q) ≤
          (K : ℝ≥0∞) * edist p q) ∧
      geodesicAnnulusArea g γ₀ γ₁ ≤ C * D *
        (riemannianCurveLength g (fun t => γ₀ (t : loopCircle)) 0 1 +
          riemannianCurveLength g (fun t => γ₁ (t : loopCircle)) 0 1) := by
  obtain ⟨ρ, C, hρ, hC, hstrip⟩ := exists_geodesicStrip_area_bound g
  refine ⟨ρ, C, hρ, hC, fun γ₀ γ₁ L₀ L₁ D h₀ h₁ hD hnear => ?_⟩
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have h₀' : LipschitzWith L₀ γ₀ := h₀
  have h₁' : LipschitzWith L₁ γ₁ := h₁
  have hl₀ : LipschitzWith L₀ (fun t : ℝ => γ₀ (t : loopCircle)) := by
    simpa only [mul_one, Function.comp_def] using! h₀'.comp loopCircle_projection_lipschitz
  have hl₁ : LipschitzWith L₁ (fun t : ℝ => γ₁ (t : loopCircle)) := by
    simpa only [mul_one, Function.comp_def] using! h₁'.comp loopCircle_projection_lipschitz
  obtain ⟨⟨K, hK⟩, ha⟩ := hstrip _ _ L₀ L₁ D hl₀ hl₁ hD (fun t => hnear (t : loopCircle))
  exact ⟨geodesicAnnulus_lipschitz_of_strip g hK, ha⟩

end DifferentialGeometry.Geometry
