import DifferentialGeometry.Topology.Ehresmann.CompletionAtlas
import DifferentialGeometry.Geometry.Metric.Basic

noncomputable section
open Set Topology Manifold
open DifferentialGeometry
open scoped ContDiff

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Geometry.Boundary DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I]
  [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_level_compatible_completion [CompactSpace M]
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {a b : ℝ}
    (hab : a < b) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) u x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b)
    (ha : a ∈ range u) (hb : b ∈ range u) :
    ∃ ε > 0, 4 * ε < b - a ∧
      ∃ C : ChartedSpace E (IntervalCompletionSpace u a b), letI := C
        IsManifold 𝓘(ℝ, E) ∞ (IntervalCompletionSpace u a b) ∧
        ContMDiff I 𝓘(ℝ, E) ∞ (intervalCompletionInclusion u a b) ∧
        (∀ x, Function.Injective (mfderiv I 𝓘(ℝ, E) (intervalCompletionInclusion u a b) x)) ∧
        IsClosedEmbedding (intervalCompletionInclusion u a b) ∧
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (intervalCompletionHeight u a b) ∧
        (∀ x, intervalCompletionHeight u a b (intervalCompletionInclusion u a b x) = u x) ∧
        intervalCompletionHeight u a b ⁻¹' Icc a b = range (intervalCompletionInclusion u a b) ∧
        (∀ q, a - 2 * ε < intervalCompletionHeight u a b q →
          intervalCompletionHeight u a b q < b + 2 * ε →
          mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (intervalCompletionHeight u a b) q ≠ 0) ∧
        IsCompact (intervalCompletionHeight u a b ⁻¹' Icc (a - 2 * ε) (b + 2 * ε)) ∧
        ∃ c₀ c₁ : PartialDiffeomorph (hI.boundaryI.prod (𝓡∂ 1)) I
            (BoundaryManifold I M × EuclideanHalfSpace 1) M ∞,
          c₀.source = {x : BoundaryManifold I M | u x.1 = a} ×ˢ
            {t : EuclideanHalfSpace 1 | t.1 0 < 2 * ε} ∧
          c₁.source = {x : BoundaryManifold I M | u x.1 = b} ×ˢ
            {t : EuclideanHalfSpace 1 | t.1 0 < 2 * ε} ∧
          (∀ x : BoundaryManifold I M, u x.1 = a → c₀ (x, 0) = x.1) ∧
          (∀ x : BoundaryManifold I M, u x.1 = b → c₁ (x, 0) = x.1) ∧
          (∀ z ∈ c₀.source, u (c₀ z) = a + z.2.1 0) ∧
          (∀ z ∈ c₁.source, u (c₁ z) = b - z.2.1 0) ∧
          u ⁻¹' {a} ⊆ c₀.target ∧ u ⁻¹' {b} ⊆ c₁.target ∧ Disjoint c₀.target c₁.target := by
  obtain ⟨C, hm, hi, hj, hf, hr⟩ := exists_smooth_intervalCompletion g hab hu hreg hboundary ha hb
  obtain ⟨ρ, hρ, hgap, c₀, c₁, hc₀, hc₁, hz₀, hz₁, hh₀, hh₁, ht₀, ht₁, hd, _, _⟩ :=
    exists_disjoint_adapted_endpoint_collars g hab hu hreg hboundary ha hb
  have hwidth : 2 * (ρ / 2) = ρ := by ring
  refine ⟨ρ / 2, by positivity, by linarith, C, hm, hi, hj,
    isClosedEmbedding_intervalCompletionInclusion hu.continuous a b, hf, (fun _ ↦ rfl),
    preimage_Icc_intervalCompletionHeight (fun x ↦
      range_subset_Icc_of_boundary_values hab.le hreg hboundary (mem_range_self x)),
    (fun q _ _ ↦ hr q),
    isCompact_preimage_Icc_intervalCompletionHeight hu.continuous a b _ _,
    c₀, c₁, ?_, ?_, hz₀, hz₁, hh₀, hh₁, ht₀, ht₁, hd⟩
  · rwa [hwidth]
  · rwa [hwidth]

end DifferentialGeometry.Topology.Ehresmann
