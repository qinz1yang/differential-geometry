import DifferentialGeometry.Geometry.Measure.Area.GeodesicStripLipschitz
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Strip
import DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz



noncomputable section

open Bundle Manifold Set DifferentialGeometry Filter MeasureTheory
open DifferentialGeometry.Analysis
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]



def extendedGeodesicStrip (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ₀ γ₁ : ℝ → M) : ℂ → M :=
  geodesicStrip g γ₀ γ₁ ∘ stripClamp

theorem extendedGeodesicStrip_eq (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : ℝ → M) {z : ℂ} (hz : z ∈ unitStrip) :
    extendedGeodesicStrip g γ₀ γ₁ z = geodesicStrip g γ₀ γ₁ z := by
  simp only [extendedGeodesicStrip, Function.comp_apply, stripClamp_eq_self hz]

theorem extendedGeodesicStrip_density_eq (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : ℝ → M) {z : ℂ} (hz : z.re ∈ Ioo (0 : ℝ) 1) :
    riemannianAreaDensity g (extendedGeodesicStrip g γ₀ γ₁) z =
      riemannianAreaDensity g (geodesicStrip g γ₀ γ₁) z := by
  apply riemannianAreaDensity_congr
  filter_upwards [stripClamp_eventually_eq_id hz] with w hw
  exact congrArg (geodesicStrip g γ₀ γ₁) hw



theorem exists_extendedGeodesicStrip_lipschitz_radius [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ∀ (γ₀ γ₁ : ℝ → M) (L₀ L₁ : ℝ≥0),
      (∀ s t, riemannianEDistOf g (γ₀ s) (γ₀ t) ≤ (L₀ : ℝ≥0∞) * edist s t) →
      (∀ s t, riemannianEDistOf g (γ₁ s) (γ₁ t) ≤ (L₁ : ℝ≥0∞) * edist s t) →
      (∀ t, riemannianEDistOf g (γ₀ t) (γ₁ t) ≤ (ρ : ℝ≥0∞)) →
      ∃ K : ℝ≥0, ∀ z w : ℂ,
        riemannianEDistOf g (extendedGeodesicStrip g γ₀ γ₁ z) (extendedGeodesicStrip g γ₀ γ₁ w) ≤
          (K : ℝ≥0∞) * edist z w := by
  obtain ⟨ρ, hρ, hstrip⟩ := exists_geodesicStrip_lipschitz_radius g
  obtain ⟨C, hC⟩ := exists_lipschitz_stripClamp
  refine ⟨ρ, hρ, fun γ₀ γ₁ L₀ L₁ h₀ h₁ hnear => ?_⟩
  obtain ⟨K, hK⟩ := hstrip γ₀ γ₁ L₀ L₁ h₀ h₁ hnear
  refine ⟨K * C, fun z w => ?_⟩
  apply (hK (stripClamp z) (stripClamp_mem z) (stripClamp w) (stripClamp_mem w)).trans
  have h : (K : ℝ≥0∞) * edist (stripClamp z) (stripClamp w) ≤
      (K : ℝ≥0∞) * ((C : ℝ≥0∞) * edist z w) := by
    gcongr
    exact hC z w
  simpa only [ENNReal.coe_mul, mul_assoc] using h



theorem integrable_extendedGeodesicStrip_density
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ₀ γ₁ : ℝ → M} {K : ℝ≥0}
    (hK : ∀ z w : ℂ,
      riemannianEDistOf g (extendedGeodesicStrip g γ₀ γ₁ z) (extendedGeodesicStrip g γ₀ γ₁ w) ≤
        (K : ℝ≥0∞) * edist z w) :
    IntegrableOn (riemannianAreaDensity g (extendedGeodesicStrip g γ₀ γ₁)) unitSquare := by
  have : IsFiniteMeasure (volume.restrict unitSquare) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isCompact_unitSquare.measure_lt_top (μ := volume))⟩
  exact integrableOn_riemannianAreaDensity_of_lipschitz g hK unitSquare

end DifferentialGeometry.Geometry
