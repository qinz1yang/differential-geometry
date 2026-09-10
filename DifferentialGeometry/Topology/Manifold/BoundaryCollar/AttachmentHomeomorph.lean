import DifferentialGeometry.Topology.Manifold.BoundaryCollar.Attachment
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.CollarStrip
import DifferentialGeometry.Topology.Collar.Attachment

open Set Function Manifold Topology
open scoped ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.BoundaryCollar

theorem exists_boundaryAttachment_realization
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ∃ (ε : ℝ) (hε : 0 < ε),
      let : Fact ((0 : ℝ) < ε) := ⟨hε⟩
      ∃ (δ : ℝ) (hδ : 0 < δ) (hδε : δ < ε)
        (c : C(BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) ε, M))
        (hc : IsClosedEmbedding c),
        ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
          (𝓡∂ (n + 1)) ∞ c ∧
        (∀ p, c (p, ⟨0, ⟨le_rfl, hε.le⟩⟩) = boundaryInclusion (𝓡∂ (n + 1)) M p) ∧
        ∃ h : BoundaryAttachment (M := M) (𝓡∂ (n + 1)) ≃ₜ M,
          (∀ x, h (attachmentOriginal (𝓡∂ (n + 1)) x) =
            Poincare.Topology.Collar.rescale c hc.isEmbedding
              (Poincare.Topology.intervalPush (δ / 4) (by linarith)) x) ∧
          ∀ q : BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) 1,
            h (attachmentProduct (𝓡∂ (n + 1)) q) =
              c (q.1, ⟨δ / 4 * (1 - q.2.val),
                ⟨mul_nonneg (by positivity) (sub_nonneg.mpr q.2.property.2), by
                  have ht := q.2.property.1
                  nlinarith⟩⟩) := by
  obtain ⟨ε, hε, hc⟩ := exists_smooth_boundary_collar_strip hK
  refine ⟨ε, hε, ?_⟩
  let : Fact ((0 : ℝ) < ε) := ⟨hε⟩
  obtain ⟨c, hclosed, hsmooth, hzero, _, δ, hδ, hδε, hopen, _⟩ := hc
  let C : C(BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) ε, M) := ⟨c, hclosed.continuous⟩
  let f : C(BoundaryManifold (𝓡∂ (n + 1)) M, M) :=
    ⟨boundaryInclusion (𝓡∂ (n + 1)) M, continuous_subtype_val⟩
  let : CompactSpace (BoundaryManifold (𝓡∂ (n + 1)) M) := isCompact_iff_compactSpace.mp hK
  obtain ⟨h, hOriginal, hProduct⟩ := Poincare.Topology.Collar.exists_attachment_homeomorph
    f (a := δ / 4) (by positivity) (by linarith) hδε.le C hclosed.isEmbedding hzero hopen
  exact ⟨δ, hδ, hδε, C, hclosed, hsmooth, hzero, h, hOriginal, hProduct⟩

theorem exists_boundaryAttachment_homeomorph
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ∃ h : BoundaryAttachment (M := M) (𝓡∂ (n + 1)) ≃ₜ M,
      (∀ p : BoundaryManifold (𝓡∂ (n + 1)) M,
        h (attachmentProduct (𝓡∂ (n + 1)) (p, 1)) = boundaryInclusion (𝓡∂ (n + 1)) M p) ∧
      h ⁻¹' (𝓡∂ (n + 1)).boundary M =
        range (fun p : BoundaryManifold (𝓡∂ (n + 1)) M => attachmentProduct (𝓡∂ (n + 1)) (p, 1)) := by
  obtain ⟨ε, hε, δ, hδ, hδε, c, hc, _, hzero, h, _, hProduct⟩ :=
    exists_boundaryAttachment_realization hK
  have houter (p : BoundaryManifold (𝓡∂ (n + 1)) M) :
      h (attachmentProduct (𝓡∂ (n + 1)) (p, 1)) = boundaryInclusion (𝓡∂ (n + 1)) M p := by
    rw [hProduct]
    convert hzero p using 1
    congr 1
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      norm_num
  refine ⟨h, houter, ?_⟩
  ext z
  constructor
  · intro hz
    refine ⟨⟨h z, hz⟩, h.injective ?_⟩
    exact houter ⟨h z, hz⟩
  · rintro ⟨p, rfl⟩
    change h (attachmentProduct (𝓡∂ (n + 1)) (p, 1)) ∈ (𝓡∂ (n + 1)).boundary M
    rw [houter]
    exact p.property

end Poincare.Manifold.BoundaryCollar
