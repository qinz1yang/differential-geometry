import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BranchedCoordinate
import DifferentialGeometry.Analysis.Complex.BranchedCoordinateFibers
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Choose

set_option autoImplicit false

noncomputable section

open Set Metric Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold

private theorem morrey_interior_locally_finite_fibers
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (a : closedDisk) (ha : (a : ℂ) ∈ Metric.ball (0 : ℂ) 1) :
    ∃ s : Set closedDisk, IsOpen s ∧ a ∈ s ∧
      ∀ y : M, (s ∩ u ⁻¹' {y}).Finite := by
  obtain ⟨m, B, _, _, _, hrest⟩ :=
    DiskRegularity.ConsumerAudit.morrey_leading_projection_branched_coordinate hu hγ ha
  dsimp only at hrest
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ρ, hρ, _, e,
    hesource, he, _, _, _, _, _, _, hepower⟩ := hrest
  let p := diskExtension u a
  let π : M → ℂ := fun y =>
    chartLeadingPlaneProjection g p p (B a) (extChartAt 𝓘(ℝ, E) p y)
  have hpower : ∀ z ∈ e.source,
      π (diskExtension u z) = π (diskExtension u a) +
        (e z) ^ (m + 1) / ((m + 1 : ℕ) : ℂ) := by
    intro z hz
    rw [he]
    exact hepower z hz
  let s : Set closedDisk := Subtype.val ⁻¹' e.source
  refine ⟨s, e.open_source.preimage continuous_subtype_val, ?_, ?_⟩
  · change (a : ℂ) ∈ e.source
    rw [hesource]
    exact Metric.mem_ball_self hρ
  · intro y
    have hf := Analysis.finite_fiber_of_normalized_power_coordinate hpower y
    refine Set.Finite.of_injOn (f := (Subtype.val : closedDisk → ℂ)) ?_
      (Subtype.val_injective.injOn) hf
    intro z hz
    have hzy : u z = y := hz.2
    exact ⟨hz.1, by simpa only [diskExtension_coe] using hzy⟩

/-- The same original Morrey disk has finite fibers once its actual boundary
values have singleton fibers. Interior finiteness comes from its literal branched
power coordinates and does not assume injectivity at branch points. -/
theorem DiskRegularity.ConsumerAudit.morrey_finite_fibers_of_boundary_fibers_singleton
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hboundary : ∀ a : closedDisk, ‖(a : ℂ)‖ = 1 →
      ∀ z : closedDisk, u z = u a → z = a) :
    ∀ y : M, (u ⁻¹' {y}).Finite := by
  classical
  intro y
  let K : Set closedDisk := u ⁻¹' {y}
  have hK : IsCompact K := (isClosed_singleton.preimage u.continuous).isCompact
  by_cases hb : ∃ a ∈ K, ‖(a : ℂ)‖ = 1
  · obtain ⟨a, hay, ha⟩ := hb
    apply (Set.finite_singleton a).subset
    intro z hz
    exact hboundary a ha z (hz.trans hay.symm)
  · have hinterior (a : K) : (a.val : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      have hle : ‖(a.val : ℂ)‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using a.val.property
      have hlt : ‖(a.val : ℂ)‖ < 1 := by
        rcases lt_or_eq_of_le hle with h | h
        · exact h
        · exact False.elim (hb ⟨a.val, a.property, h⟩)
      simpa only [Metric.mem_ball, dist_zero_right] using hlt
    choose s hsopen hsmem hsfin using fun a : K =>
      morrey_interior_locally_finite_fibers hu hγ a.val (hinterior a)
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover s hsopen (by
      intro a ha
      exact mem_iUnion.mpr ⟨⟨a, ha⟩, hsmem ⟨a, ha⟩⟩)
    have hfin : (⋃ a ∈ t, s a ∩ K).Finite :=
      t.finite_toSet.biUnion fun a _ => hsfin a y
    apply hfin.subset
    intro z hz
    obtain ⟨a, hat, hza⟩ := mem_iUnion₂.mp (ht hz)
    exact mem_iUnion₂.mpr ⟨a, hat, hza, hz⟩
