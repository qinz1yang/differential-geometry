import DifferentialGeometry.Topology.Manifold.BoundaryCollar.CollarStrip

open Set Function Filter Manifold Topology
open scoped ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.BoundaryCollar


def halfOpenStrip {B M : Type*} {ε δ : ℝ} (c : B × Icc (0 : ℝ) ε → M)
    (hδε : δ ≤ ε) : B × Ico (0 : ℝ) δ → M :=
  fun q => c (q.1, ⟨q.2, q.2.2.1, q.2.2.2.le.trans hδε⟩)


theorem range_halfOpenStrip {B M : Type*} {ε δ : ℝ}
    (c : B × Icc (0 : ℝ) ε → M) (hδε : δ ≤ ε) :
    range (halfOpenStrip c hδε) = c '' {q | (q.2 : ℝ) < δ} := by
  ext y
  constructor
  · rintro ⟨⟨b, t⟩, rfl⟩
    exact ⟨(b, ⟨t, t.2.1, t.2.2.le.trans hδε⟩), t.2.2, rfl⟩
  · rintro ⟨⟨b, t⟩, ht, rfl⟩
    exact ⟨(b, ⟨t, t.2.1, ht⟩), rfl⟩


theorem isEmbedding_halfOpenStrip {B M : Type*} [TopologicalSpace B] [TopologicalSpace M]
    {ε δ : ℝ} {c : B × Icc (0 : ℝ) ε → M} (hc : IsEmbedding c) (hδε : δ ≤ ε) :
    IsEmbedding (halfOpenStrip c hδε) := by
  have hsub : Ico (0 : ℝ) δ ⊆ Icc (0 : ℝ) ε := fun _ ht => ⟨ht.1, ht.2.le.trans hδε⟩
  exact hc.comp (IsEmbedding.id.prodMap (IsEmbedding.inclusion hsub))

theorem exists_boundary_collar_homeomorph
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (U : TopologicalSpace.Opens M),
      (𝓡∂ (n + 1)).boundary M ⊆ U ∧
      ∃ e : (BoundaryManifold (𝓡∂ (n + 1)) M × Ico (0 : ℝ) δ) ≃ₜ U,
        (∀ p, (e (p, ⟨0, ⟨le_rfl, hδ⟩⟩) : M) = boundaryInclusion (𝓡∂ (n + 1)) M p) ∧
        ∀ p (t : Ico (0 : ℝ) δ), 0 < (t : ℝ) →
          (𝓡∂ (n + 1)).IsInteriorPoint (e (p, t) : M) := by
  obtain ⟨ε, hε, hc⟩ := exists_smooth_boundary_collar_strip hK
  let : Fact ((0 : ℝ) < ε) := ⟨hε⟩
  obtain ⟨c, hclosed, _, hzero, hi, δ, hδ, hδε, hopen, hboundary⟩ := hc
  let f := halfOpenStrip c hδε.le
  have hf : IsEmbedding f := isEmbedding_halfOpenStrip hclosed.isEmbedding hδε.le
  let U : TopologicalSpace.Opens M := ⟨range f, by rw [range_halfOpenStrip]; exact hopen⟩
  refine ⟨δ, hδ, U, ?_, hf.toHomeomorph, ?_, ?_⟩
  · intro p hp
    change p ∈ range f
    rw [range_halfOpenStrip]
    exact hboundary hp
  · intro p
    change c (p, ⟨0, ⟨le_rfl, hε.le⟩⟩) = boundaryInclusion (𝓡∂ (n + 1)) M p
    exact hzero p
  · intro p t ht
    exact hi p ⟨t, t.2.1, t.2.2.le.trans hδε.le⟩ ht

end Poincare.Manifold.BoundaryCollar
