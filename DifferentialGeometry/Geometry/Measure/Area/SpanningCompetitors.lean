import DifferentialGeometry.Geometry.Measure.Area.GeodesicAnnulus
import DifferentialGeometry.Topology.LoopSpace.AttachAnnulus
import DifferentialGeometry.Topology.LoopSpace.ContinuousFilling
import DifferentialGeometry.Geometry.Metric.ManifoldApproximation










noncomputable section

open Bundle Manifold Set DifferentialGeometry MeasureTheory
open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]



def spanningDiskCompetitors (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : freeLoop M) :
    Set C(closedDisk, M) :=
  {u | diskTrace u = γ ∧ ∃ L : ℝ≥0, ∀ z w : closedDisk,
    riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem spanningDiskCompetitors_nonempty [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {L : ℝ≥0}
    (hγ : ∀ s t, riemannianEDistOf g (γ s) (γ t) ≤ (L : ℝ≥0∞) * edist s t)
    (hnull : γ.Nullhomotopic) : (spanningDiskCompetitors g γ).Nonempty := by
  obtain ⟨ρ, _, hρ, _, hann⟩ := exists_geodesicAnnulus_area_bound g
  obtain ⟨v₀, htrace⟩ := exists_continuous_disk_of_nullhomotopic hnull
  obtain ⟨v, hv, hvnear⟩ := exists_smooth_disk_approximation g v₀ (ε := (ρ : ℝ))
    (by exact_mod_cast hρ)
  obtain ⟨Cv, hCv⟩ := exists_compact_source_riemannian_lipschitz g isOpen_univ
    (hv.of_le (by simp)).contMDiffOn (isCompact_closedBall (0 : ℂ) 1) (subset_univ _)
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let : MetricSpace M := EMetricSpace.toMetricSpace DifferentialGeometry.Analysis.edist_ne_top_of_preconnected
  let U : ℂ → M := diskExtension (fun z : closedDisk => v z)
  have hUv : LipschitzWith Cv (fun z : closedDisk => v z) :=
    fun z w => hCv z z.property w w.property
  have hU : LipschitzWith Cv U := diskExtension_lipschitz hUv
  let η : loopCircle → M := fun θ => U (AddCircle.toCircle θ : ℂ)
  have hη := hU.comp circle_boundary_lipschitz
  have hnear (θ : loopCircle) : riemannianEDistOf g (η θ) (γ θ) ≤ (ρ : ℝ≥0∞) := by
    have h := (hvnear (diskBoundary θ)).le
    have ht : v₀ (diskBoundary θ) = γ θ := congrArg (fun f : freeLoop M => f θ) htrace
    have he : η θ = v (diskBoundary θ) := diskExtension_coe _ (diskBoundary θ)
    rw [he, ← ht, ← ENNReal.ofReal_coe_nnreal]
    exact h
  obtain ⟨⟨Kh, hKh⟩, _⟩ := hann η γ _ L ρ hη hγ le_rfl hnear
  have hH : LipschitzWith Kh (geodesicAnnulus g η γ) := hKh
  have hglue (θ : loopCircle) : U (AddCircle.toCircle θ : ℂ) = geodesicAnnulus g η γ (0, θ) :=
    (geodesicAnnulus_zero g η γ θ).symm
  have hA := attachDiskAnnulus_lipschitz hU hH hglue
  let u : C(closedDisk, M) := ⟨fun z => attachDiskAnnulus U (geodesicAnnulus g η γ) z,
    hA.continuous.comp continuous_subtype_val⟩
  refine ⟨u, ?_, ⟨_, fun z w => hA z w⟩⟩
  ext θ
  change attachDiskAnnulus U (geodesicAnnulus g η γ) (AddCircle.toCircle θ : ℂ) = γ θ
  rw [attachDiskAnnulus_boundary]
  exact geodesicAnnulus_one g η γ θ (ne_top_of_le_ne_top ENNReal.coe_ne_top (hnear θ))

omit [CompactSpace M] in
theorem spanningDiskCompetitor_integrable
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : u ∈ spanningDiskCompetitors g γ) :
    IntegrableOn (riemannianAreaDensity g (diskExtension u)) (Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨_, L, hL⟩ := hu
  exact integrable_riemannianDiskAreaDensity g hL

end DifferentialGeometry.Geometry
