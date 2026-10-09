import DifferentialGeometry.Geometry.HarmonicMap.CompactTargetCriticalValues
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Restriction

set_option autoImplicit false
noncomputable section

open Set Metric Manifold DifferentialGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry
open scoped Topology ContDiff Manifold

/-- Both literal disks used by the proper-restriction seed have locally finite
critical values away from their SAME induced trace. The original restriction's
Morrey property is derived from the original disk and metric. No alternative
filling, new parametrization, or boundary singleton premise is introduced. -/
theorem IMS03Embeddedness.ConsumerAudit.actual_proper_restriction_pair_critical_values_away_trace
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (QOriginal : ℂ → M) (hQOriginal : SmoothDiskExtension (E := E) u QOriginal)
    (a : ℂ) (r : ℝ) (hr : 0 < r) (hinside : ‖a‖ + r < 1)
    (hloop : IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk u a r)))
    (qAlt : C(closedDisk, M))
    (hqAlt : IsMorreyDisk g (diskTrace (affineSubdisk u a r)) qAlt) :
    let qRest := affineSubdisk u a r
    let Γ := Set.range (diskTrace qRest)
    IsMorreyDisk g (diskTrace qRest) qRest ∧
      ∀ y ∉ Γ, ∃ V : Set M, IsOpen V ∧ y ∈ V ∧ V ⊆ Γᶜ ∧
        ((diskInteriorCriticalValues (E := E) qRest ∪
          diskInteriorCriticalValues (E := E) qAlt) ∩ V).Finite := by
  obtain ⟨L, huLip⟩ := hQOriginal.lipschitz g
  have hqRest := hu.affineSubdisk huLip a r hr hinside hloop.immersed
  refine ⟨hqRest, ?_⟩
  intro y hy
  obtain ⟨V₁, hV₁, hy₁, haway₁, hf₁⟩ :=
    hqRest.locally_finite_critical_values_away_trace hloop hy
  obtain ⟨V₂, hV₂, hy₂, haway₂, hf₂⟩ :=
    hqAlt.locally_finite_critical_values_away_trace hloop hy
  refine ⟨V₁ ∩ V₂, hV₁.inter hV₂, ⟨hy₁, hy₂⟩,
    inter_subset_left.trans haway₁, ?_⟩
  apply (hf₁.union hf₂).subset
  intro z hz
  rcases hz.1 with h | h
  · exact Or.inl ⟨h, hz.2.1⟩
  · exact Or.inr ⟨h, hz.2.2⟩
