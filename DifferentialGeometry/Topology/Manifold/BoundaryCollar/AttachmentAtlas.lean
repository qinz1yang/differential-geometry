import DifferentialGeometry.Topology.Manifold.BoundaryCollar.SmoothAttachment
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport

open Set Function Manifold Topology
open scoped ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.BoundaryCollar

theorem exists_boundaryAttachment_smooth_atlas
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ∃ C : ChartedSpace (EuclideanHalfSpace (n + 1)) (BoundaryAttachment (M := M) (𝓡∂ (n + 1))),
      let _ := C
      IsManifold (𝓡∂ (n + 1)) ∞ (BoundaryAttachment (M := M) (𝓡∂ (n + 1))) ∧
      ∃ d : Diffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
          (BoundaryAttachment (M := M) (𝓡∂ (n + 1))) M ∞,
        ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ (attachmentOriginal (M := M) (𝓡∂ (n + 1))) ∧
        ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
          (𝓡∂ (n + 1)) ∞ (attachmentProduct (M := M) (𝓡∂ (n + 1))) ∧
        (∀ p : BoundaryManifold (𝓡∂ (n + 1)) M,
          d (attachmentProduct (𝓡∂ (n + 1)) (p, 1)) = boundaryInclusion (𝓡∂ (n + 1)) M p) ∧
        (𝓡∂ (n + 1)).boundary (BoundaryAttachment (M := M) (𝓡∂ (n + 1))) =
          range (fun p : BoundaryManifold (𝓡∂ (n + 1)) M => attachmentProduct (𝓡∂ (n + 1)) (p, 1)) := by
  obtain ⟨ε, hε, r, hr, hrε, a, ha, har, c, hc, hcs, hc0, σ, hσ, hnear,
    h, hO, hP, hOs, hPs, houter, hboundary⟩ := exists_boundaryAttachment_smooth_realization hK
  let I := 𝓡∂ (n + 1)
  let Q := BoundaryAttachment (M := M) I
  let C := Poincare.Manifold.Homeomorph.pullbackChartedSpace (H := EuclideanHalfSpace (n + 1)) h
  let _ : ChartedSpace (EuclideanHalfSpace (n + 1)) Q := C
  let d : Diffeomorph I I Q M ∞ := Poincare.Manifold.Homeomorph.pullbackDiffeomorph h
  have hOrig : ContMDiff I I ∞ (attachmentOriginal (M := M) I) := by
    have hh := d.symm.contMDiff.comp hOs
    apply hh.congr
    intro x
    exact (h.symm_apply_apply (attachmentOriginal I x)).symm
  have hProd : ContMDiff ((HasSmoothBoundary.boundaryModel I).prod (𝓡∂ 1)) I ∞
      (attachmentProduct (M := M) I) := by
    have hh := d.symm.contMDiff.comp hPs
    apply hh.congr
    intro q
    exact (h.symm_apply_apply (attachmentProduct I q)).symm
  refine ⟨C, inferInstance, d, hOrig, hProd, houter, ?_⟩
  exact (d.preimage_boundary (by simp)).symm.trans hboundary

end Poincare.Manifold.BoundaryCollar
