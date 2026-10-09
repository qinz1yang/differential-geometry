import DifferentialGeometry.Geometry.Measure.Area.GeodesicStrip
import DifferentialGeometry.Geometry.Metric.CompactSourceLipschitz



noncomputable section

open Bundle Manifold Set DifferentialGeometry
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [Nonempty M] [PreconnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace




theorem exists_geodesicStrip_lipschitz_radius (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ∀ (γ₀ γ₁ : ℝ → M) (L₀ L₁ : ℝ≥0),
      (∀ s t, riemannianEDistOf g (γ₀ s) (γ₀ t) ≤ (L₀ : ℝ≥0∞) * edist s t) →
      (∀ s t, riemannianEDistOf g (γ₁ s) (γ₁ t) ≤ (L₁ : ℝ≥0∞) * edist s t) →
      (∀ t, riemannianEDistOf g (γ₀ t) (γ₁ t) ≤ (ρ : ℝ≥0∞)) →
      ∃ K : ℝ≥0, ∀ z : ℂ, z.re ∈ Icc (0 : ℝ) 1 →
        ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 →
          riemannianEDistOf g (geodesicStrip g γ₀ γ₁ z) (geodesicStrip g γ₀ γ₁ w) ≤
            (K : ℝ≥0∞) * edist z w := by
  obtain ⟨n, e, r, he, hleft, ρ, _, O, hρ, hO, hF, hregion⟩ :=
    exists_geodesicInterpolation_ambient_bound g
  let F := fun p : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
    geodesicInterpolation g (r p.2.1) (r p.2.2) p.1
  let B : Set (ℝ × (M × M)) := Icc 0 1 ×ˢ
    {p | riemannianEDistOf g p.1 p.2 ≤ (ρ : ℝ≥0∞)}
  have hB : IsCompact B := by
    let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
    exact isCompact_Icc.prod (isClosed_le (continuous_fst.edist continuous_snd) continuous_const).isCompact
  let eB : ℝ × (M × M) → ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    fun p => (p.1, (e p.2.1, e p.2.2))
  have heB : Continuous eB := continuous_fst.prodMk
    ((he.continuous.comp (continuous_fst.comp continuous_snd)).prodMk
      (he.continuous.comp (continuous_snd.comp continuous_snd)))
  have hBO : eB '' B ⊆ O := by
    rintro _ ⟨⟨t, x, y⟩, hp, rfl⟩
    exact (hregion t hp.1 x y hp.2).1
  obtain ⟨Cf, hCf⟩ := exists_compact_source_riemannian_lipschitz g hO
    (hF.of_le (by simp)) (hB.image heB) hBO
  obtain ⟨Ce, _, hCe⟩ := exists_riemannian_lipschitz_of_contMDiff g (he.of_le (by simp))
  refine ⟨ρ, hρ, fun γ₀ γ₁ L₀ L₁ h₀ h₁ hnear => ?_⟩
  have hcomp (γ : ℝ → M) (L : ℝ≥0)
      (hγ : ∀ s t, riemannianEDistOf g (γ s) (γ t) ≤ (L : ℝ≥0∞) * edist s t) :
      LipschitzWith (Ce * L) (e ∘ γ) := by
    intro s t
    apply (hCe (γ s) (γ t)).trans
    have hm : (Ce : ℝ≥0∞) * riemannianEDistOf g (γ s) (γ t) ≤
        (Ce : ℝ≥0∞) * ((L : ℝ≥0∞) * edist s t) := by
      gcongr
      exact hγ s t
    simpa only [ENNReal.coe_mul, mul_assoc] using hm
  let P : ℂ → ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    fun z => (z.re, (e (γ₀ z.im), e (γ₁ z.im)))
  obtain ⟨Kp, hP⟩ : ∃ Kp : ℝ≥0, LipschitzWith Kp P :=
    ⟨_, Complex.reCLM.lipschitzWith.prodMk
      (((hcomp γ₀ L₀ h₀).comp Complex.imCLM.lipschitzWith).prodMk
        ((hcomp γ₁ L₁ h₁).comp Complex.imCLM.lipschitzWith))⟩
  have hPB (z : ℂ) (hz : z.re ∈ Icc (0 : ℝ) 1) : P z ∈ eB '' B :=
    mem_image_of_mem eB (show (z.re, (γ₀ z.im, γ₁ z.im)) ∈ B from ⟨hz, hnear z.im⟩)
  refine ⟨Cf * Kp, fun z hz w hw => ?_⟩
  have hm : (Cf : ℝ≥0∞) * edist (P z) (P w) ≤ (Cf : ℝ≥0∞) * ((Kp : ℝ≥0∞) * edist z w) := by
    gcongr
    exact hP z w
  have h := (hCf (P z) (hPB z hz) (P w) (hPB w hw)).trans hm
  simpa only [F, P, hleft, geodesicStrip, ENNReal.coe_mul, mul_assoc] using h

end DifferentialGeometry.Geometry
