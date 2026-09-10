import DifferentialGeometry.Geometry.Boundary.EndpointStrips
import DifferentialGeometry.Geometry.Boundary.LevelComponents
import Mathlib.Geometry.Manifold.Instances.Icc

noncomputable section
open Set Filter Function Topology Manifold
open scoped ContDiff

namespace Poincare.Geometry.Boundary

open DifferentialGeometry
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Integral.Measure

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I]
  [IsManifold I ∞ M] [CompactSpace M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_smooth_embedded_endpoint_strips
    (g : SmoothRiemannianMetric I M) {u : M → ℝ} {a b : ℝ}
    (hab : a < b) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) u x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b) :
    ∃ (ε : ℝ) (hε : 0 < ε),
      let _ : Fact ((0 : ℝ) < ε) := ⟨hε⟩
      ∃ c₀ : boundaryLevel u a b hab.ne hu.continuous hboundary × Icc (0 : ℝ) ε → M,
      ∃ c₁ : boundaryLevel u b a hab.ne.symm hu.continuous
        (fun x hx ↦ (hboundary x hx).symm) × Icc (0 : ℝ) ε → M,
        2 * ε < b - a ∧
        ContMDiff (hI.boundaryI.prod (𝓡∂ 1)) I ∞ c₀ ∧
        ContMDiff (hI.boundaryI.prod (𝓡∂ 1)) I ∞ c₁ ∧
        IsClosedEmbedding c₀ ∧ IsClosedEmbedding c₁ ∧
        (∀ x, c₀ (x, ⟨0, le_rfl, hε.le⟩) = x.1.1) ∧
        (∀ x, c₁ (x, ⟨0, le_rfl, hε.le⟩) = x.1.1) ∧
        (∀ z, u (c₀ z) = a + z.2.1) ∧ (∀ z, u (c₁ z) = b - z.2.1) ∧
        (∀ z, 0 < z.2.1 → I.IsInteriorPoint (c₀ z)) ∧
        (∀ z, 0 < z.2.1 → I.IsInteriorPoint (c₁ z)) ∧
        Disjoint (range c₀) (range c₁) := by
  obtain ⟨ε, hε, hgap, U₀, U₁, _, _, hU₀, hU₁, Φ₀, Φ₁, hzero₀, hzero₁,
    hΦ₀, hΦ₁, _, _, hheight₀, hheight₁, hemb₀, hemb₁, hdisj, hinside₀, hinside₁⟩ :=
    exists_disjoint_adapted_endpoint_strips g hab hu hreg hboundary
  let : Fact ((0 : ℝ) < ε) := ⟨hε⟩
  let B₀ := boundaryLevel u a b hab.ne hu.continuous hboundary
  let B₁ := boundaryLevel u b a hab.ne.symm hu.continuous (fun x hx ↦ (hboundary x hx).symm)
  let c₀ : B₀ × Icc (0 : ℝ) ε → M := fun z ↦ Φ₀ (z.1.1.1, z.2.1)
  let c₁ : B₁ × Icc (0 : ℝ) ε → M := fun z ↦ Φ₁ (z.1.1.1, z.2.1)
  have hc₀ : ContMDiff (hI.boundaryI.prod (𝓡∂ 1)) I ∞ c₀ :=
    hΦ₀.comp_contMDiff
      (((contMDiff_boundaryLevelInclusion u a b hab.ne hu.continuous hboundary).comp contMDiff_fst).prodMk
        (contMDiff_subtypeVal_Icc.comp contMDiff_snd))
      (fun z ↦ ⟨hU₀ z.1.2, z.2.2⟩)
  have hc₁ : ContMDiff (hI.boundaryI.prod (𝓡∂ 1)) I ∞ c₁ :=
    hΦ₁.comp_contMDiff
      (((contMDiff_boundaryLevelInclusion u b a hab.ne.symm hu.continuous
        (fun x hx ↦ (hboundary x hx).symm)).comp contMDiff_fst).prodMk
        (contMDiff_subtypeVal_Icc.comp contMDiff_snd))
      (fun z ↦ ⟨hU₁ z.1.2, z.2.2⟩)
  let : CompactSpace B₀ := boundaryLevel_compactSpace u a b hab.ne hu.continuous hboundary
  let : CompactSpace B₁ := boundaryLevel_compactSpace u b a hab.ne.symm hu.continuous
    (fun x hx ↦ (hboundary x hx).symm)
  have he₀ : IsClosedEmbedding c₀ := by
    apply hc₀.continuous.isClosedEmbedding
    intro z w heq
    have hh := hemb₀.injective (a₁ := (⟨z.1.1.1, z.1.2⟩, z.2))
      (a₂ := (⟨w.1.1.1, w.1.2⟩, w.2)) heq
    exact Prod.ext (Subtype.ext (Subtype.ext (congrArg (fun p ↦ p.1.1) hh))) (Prod.mk.inj hh).2
  have he₁ : IsClosedEmbedding c₁ := by
    apply hc₁.continuous.isClosedEmbedding
    intro z w heq
    have hh := hemb₁.injective (a₁ := (⟨z.1.1.1, z.1.2⟩, z.2))
      (a₂ := (⟨w.1.1.1, w.1.2⟩, w.2)) heq
    exact Prod.ext (Subtype.ext (Subtype.ext (congrArg (fun p ↦ p.1.1) hh))) (Prod.mk.inj hh).2
  refine ⟨ε, hε, c₀, c₁, hgap, hc₀, hc₁, he₀, he₁,
    (fun x ↦ hzero₀ x.1.1 (hU₀ x.2)), (fun x ↦ hzero₁ x.1.1 (hU₁ x.2)),
    (fun z ↦ hheight₀ z.1.1.1 z.1.2 z.2.1 z.2.2),
    (fun z ↦ hheight₁ z.1.1.1 z.1.2 z.2.1 z.2.2),
    (fun z hz ↦ hinside₀ z.1.1.1 (hU₀ z.1.2) z.2.1 ⟨hz, z.2.2.2⟩),
    (fun z hz ↦ hinside₁ z.1.1.1 (hU₁ z.1.2) z.2.1 ⟨hz, z.2.2.2⟩), ?_⟩
  apply hdisj.mono
  · rintro _ ⟨z, rfl⟩
    exact ⟨(z.1.1.1, z.2.1), ⟨z.1.2, z.2.2⟩, rfl⟩
  · rintro _ ⟨z, rfl⟩
    exact ⟨(z.1.1.1, z.2.1), ⟨z.1.2, z.2.2⟩, rfl⟩

end Poincare.Geometry.Boundary
