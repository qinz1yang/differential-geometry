import DifferentialGeometry.Topology.Manifold.BoundaryCollar.Attachment
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.ClosedStripDiffeomorph
import DifferentialGeometry.Topology.Manifold.Collar.Attachment

open Set Function Manifold Topology TopologicalSpace
open scoped ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.BoundaryCollar

theorem exists_boundaryAttachment_smooth_realization
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ∃ (ε : ℝ) (hε : 0 < ε),
      let : Fact ((0 : ℝ) < ε) := ⟨hε⟩
      ∃ (r : ℝ) (_ : 0 < r) (hrε : 2 * r < ε)
        (a : ℝ) (ha : 0 < a) (har : a < r)
        (c : C(BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) ε, M))
        (hc : IsClosedEmbedding c),
        ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
          (𝓡∂ (n + 1)) ∞ c ∧
        (∀ p, c (p, ⟨0, ⟨le_rfl, hε.le⟩⟩) = boundaryInclusion (𝓡∂ (n + 1)) M p) ∧
        ∃ σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε),
          ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ σ ∧
          (∀ t : Icc (0 : ℝ) ε, t.val ≤ r → (σ t).val = t.val + a) ∧
          ∃ h : BoundaryAttachment (M := M) (𝓡∂ (n + 1)) ≃ₜ M,
            (∀ x, h (attachmentOriginal (𝓡∂ (n + 1)) x) =
              Poincare.Topology.Collar.rescale c hc.isEmbedding σ x) ∧
            (∀ q : BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) 1,
              h (attachmentProduct (𝓡∂ (n + 1)) q) =
                c (q.1, ⟨a * (1 - q.2.val),
                  ⟨mul_nonneg ha.le (sub_nonneg.mpr q.2.property.2), by
                    have ht := q.2.property.1
                    nlinarith⟩⟩)) ∧
            ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞
              (fun x => h (attachmentOriginal (𝓡∂ (n + 1)) x)) ∧
            ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
              (𝓡∂ (n + 1)) ∞ (fun q => h (attachmentProduct (𝓡∂ (n + 1)) q)) ∧
            (∀ p : BoundaryManifold (𝓡∂ (n + 1)) M,
              h (attachmentProduct (𝓡∂ (n + 1)) (p, 1)) = boundaryInclusion (𝓡∂ (n + 1)) M p) ∧
            h ⁻¹' (𝓡∂ (n + 1)).boundary M =
              range (fun p : BoundaryManifold (𝓡∂ (n + 1)) M =>
                attachmentProduct (𝓡∂ (n + 1)) (p, 1)) := by
  obtain ⟨ε, hε, c, hc, hcs, hc0, _, δ, hδ, hδε, Y, _, hY, e, hec⟩ :=
    exists_closed_boundary_collar_diffeomorph hK
  refine ⟨ε, hε, ?_⟩
  let _ : Fact ((0 : ℝ) < ε) := ⟨hε⟩
  let I := 𝓡∂ (n + 1)
  let B := BoundaryManifold I M
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp hK
  let r := δ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : 2 * r < ε := by dsimp [r]; linarith
  let f : C(B, M) := ⟨boundaryInclusion I M, continuous_subtype_val⟩
  obtain ⟨a, ha, har, σ, _, _, hσs, _, _, hσnear, _, h, hO, hP, hOs, hPs⟩ :=
    Poincare.Manifold.Collar.exists_smooth_attachment_realization hr hrε.le
      (by dsimp [r]; linarith) f c hc.isEmbedding hcs hc0 Y e hec
  have houter (p : B) : h (attachmentProduct I (p, 1)) = boundaryInclusion I M p := by
    change h (Poincare.Topology.mappingCylinderProduct f (p, 1)) = _
    rw [hP]
    convert hc0 p using 1
    congr 1
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      norm_num
  refine ⟨r, hr, hrε, a, ha, har, c, hc, hcs, hc0, σ, hσs, hσnear, h, hO, hP, hOs, hPs, houter, ?_⟩
  ext z
  constructor
  · intro hz
    exact ⟨⟨h z, hz⟩, h.injective (houter ⟨h z, hz⟩)⟩
  · rintro ⟨p, rfl⟩
    change h (attachmentProduct I (p, 1)) ∈ I.boundary M
    rw [houter]
    exact p.property

end Poincare.Manifold.BoundaryCollar
