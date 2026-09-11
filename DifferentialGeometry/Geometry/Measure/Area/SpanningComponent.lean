import DifferentialGeometry.Topology.LoopSpace.ManifoldComponent
import DifferentialGeometry.Geometry.Metric.Restriction
import DifferentialGeometry.Geometry.Measure.Area.OpenTarget
import DifferentialGeometry.Geometry.Measure.Area.SpanningCompetitors








noncomputable section

open Set Bundle Manifold DifferentialGeometry ContinuousMap
open DifferentialGeometry.Topology
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]

omit [CompactSpace M] in
theorem spanningDiskCompetitor_open_inclusion
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : TopologicalSpace.Opens M)
    {γ : freeLoop U} {u : C(closedDisk, U)}
    (hu : u ∈ spanningDiskCompetitors (g.restrictOpen U) γ) :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)).comp u ∈ spanningDiskCompetitors g
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)).comp γ) := by
  obtain ⟨ht, L, hL⟩ := hu
  refine ⟨?_, L, fun z w => (riemannianEDistOf_le_restrictOpen g U (u z) (u w)).trans (hL z w)⟩
  ext θ
  exact congrArg Subtype.val (congrArg (fun f : freeLoop U => f θ) ht)



theorem spanningDiskCompetitors_nonempty_of_compact
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M} {L : ℝ≥0}
    (hγ : ∀ s t, riemannianEDistOf g (γ s) (γ t) ≤ (L : ℝ≥0∞) * edist s t)
    (hnull : γ.Nullhomotopic) : (spanningDiskCompetitors g γ).Nonempty := by
  let U := loopComponentOpen E γ
  let γU : freeLoop U := loopInComponent γ
  have hγU (s t : loopCircle) :
      riemannianEDistOf (g.restrictOpen U) (γU s) (γU t) ≤ (L : ℝ≥0∞) * edist s t := by
    rw [riemannianEDistOf_restrictOpen_of_isClosed g U (isClosed_loopComponentOpen E γ)]
    exact hγ s t
  obtain ⟨u, hu⟩ := spanningDiskCompetitors_nonempty (g.restrictOpen U) hγU
    (loopInComponent_nullhomotopic γ hnull)
  exact ⟨_, spanningDiskCompetitor_open_inclusion g U hu⟩

end DifferentialGeometry.Geometry
