import DifferentialGeometry.Geometry.Measure.Area.AttachmentArea
import DifferentialGeometry.Geometry.Measure.Area.SpanningCompetitors
import DifferentialGeometry.Geometry.Metric.LoopDistance



noncomputable section

open Bundle Manifold Set DifferentialGeometry MeasureTheory Metric
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [PreconnectedSpace M]



theorem exists_competitor_attach_geodesicAnnulus
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ₀ γ₁ : freeLoop M} {Kh : ℝ≥0}
    (hH : ∀ p q, riemannianEDistOf g (geodesicAnnulus g γ₀ γ₁ p) (geodesicAnnulus g γ₀ γ₁ q) ≤
      (Kh : ℝ≥0∞) * edist p q) {u : C(closedDisk, M)}
    (hu : u ∈ spanningDiskCompetitors g γ₀) :
    ∃ v ∈ spanningDiskCompetitors g γ₁,
      riemannianDiskArea g v = riemannianDiskArea g u + geodesicAnnulusArea g γ₀ γ₁ := by
  obtain ⟨htrace, Ku, hKu⟩ := hu
  let U := diskExtension u
  have hU := diskExtension_riemannian_lipschitz g hKu
  let H := geodesicAnnulus g γ₀ γ₁
  have hglue (θ : loopCircle) : U (AddCircle.toCircle θ : ℂ) = H (0, θ) := by
    have ht : u (diskBoundary θ) = γ₀ θ := congrArg (fun f : freeLoop M => f θ) htrace
    change diskExtension u (diskBoundary θ) = geodesicAnnulus g γ₀ γ₁ (0, θ)
    rw [diskExtension_coe, ht, geodesicAnnulus_zero]
  obtain ⟨Ka, hKa⟩ := attachDiskAnnulus_riemannian_lipschitz g hU hH hglue
  let A := attachDiskAnnulus U H
  let v : C(closedDisk, M) := ⟨fun z => A z,
    (continuous_of_riemannian_lipschitz g hKa).comp continuous_subtype_val⟩
  have hvtrace : diskTrace v = γ₁ := by
    ext θ
    change attachDiskAnnulus U H (AddCircle.toCircle θ : ℂ) = γ₁ θ
    rw [attachDiskAnnulus_boundary]
    exact geodesicAnnulus_one g γ₀ γ₁ θ
      (ne_top_of_le_ne_top ENNReal.coe_ne_top (riemannianEDist_le_loopDistance g γ₀ γ₁ θ))
  refine ⟨v, ⟨hvtrace, Ka, fun z w => hKa z w⟩, ?_⟩
  rw [riemannianDiskArea_eq_of_extension g v A (fun _ => rfl), attachDiskAnnulus_area g hU hH hglue]
  rw [← geodesicAnnulusArea_eq_cylinderArea]
  rfl




theorem exists_nearby_loop_annulus [Nonempty M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    ∃ ρ C : ℝ≥0, 0 < ρ ∧ 0 < C ∧ ∀ (γ₀ γ₁ : freeLoop M) (L₀ L₁ : ℝ≥0),
      (∀ s t, riemannianEDistOf g (γ₀ s) (γ₀ t) ≤ (L₀ : ℝ≥0∞) * edist s t) →
      (∀ s t, riemannianEDistOf g (γ₁ s) (γ₁ t) ≤ (L₁ : ℝ≥0∞) * edist s t) →
      riemannianLoopDistance g γ₀ γ₁ < ρ →
      (∃ K : ℝ≥0, ∀ p q,
        riemannianEDistOf g (geodesicAnnulus g γ₀ γ₁ p) (geodesicAnnulus g γ₀ γ₁ q) ≤
          (K : ℝ≥0∞) * edist p q) ∧
      geodesicAnnulusArea g γ₀ γ₁ ≤ C * riemannianLoopDistance g γ₀ γ₁ *
        (riemannianCurveLength g (fun t => γ₀ (t : loopCircle)) 0 1 +
          riemannianCurveLength g (fun t => γ₁ (t : loopCircle)) 0 1) ∧
      ∀ u ∈ spanningDiskCompetitors g γ₀, ∃ v ∈ spanningDiskCompetitors g γ₁,
        riemannianDiskArea g v = riemannianDiskArea g u + geodesicAnnulusArea g γ₀ γ₁ := by
  obtain ⟨ρ, C, hρ, hC, h⟩ := exists_geodesicAnnulus_area_bound g
  refine ⟨ρ, C, hρ, hC, fun γ₀ γ₁ L₀ L₁ h₀ h₁ hnear => ?_⟩
  obtain ⟨⟨K, hK⟩, ha⟩ := h γ₀ γ₁ L₀ L₁ (riemannianLoopDistance g γ₀ γ₁)
    h₀ h₁ hnear.le (riemannianEDist_le_loopDistance g γ₀ γ₁)
  exact ⟨⟨K, hK⟩, ha, fun _ hu => exists_competitor_attach_geodesicAnnulus g hK hu⟩

end DifferentialGeometry.Geometry
