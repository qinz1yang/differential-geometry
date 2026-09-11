import DifferentialGeometry.Topology.Manifold.BoundaryCollar.Attachment
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.ClosedStripDiffeomorph
import DifferentialGeometry.Topology.Manifold.Collar.Attachment
import DifferentialGeometry.Topology.Manifold.Collar.SeamDiffeomorph

open Set Function Manifold Topology TopologicalSpace
open scoped ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.BoundaryCollar

local instance : Fact ((-1 : ℝ) < 1) := ⟨by norm_num⟩

theorem exists_boundaryAttachment_signed_seam
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ∃ (ε : ℝ) (hε : 0 < ε),
      let _ : Fact ((0 : ℝ) < ε) := ⟨hε⟩
      ∃ (c : C(BoundaryManifold (𝓡∂ (n + 1)) M × Icc (0 : ℝ) ε, M))
        (hzero : ∀ p, c (p, ⟨0, ⟨le_rfl, hε.le⟩⟩) = boundaryInclusion (𝓡∂ (n + 1)) M p),
        IsClosedEmbedding c ∧
        ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ∞ c ∧
        ∃ a : Icc (0 : ℝ) ε, 0 < a.val ∧ 2 * a.val < ε ∧
          let f : C(BoundaryManifold (𝓡∂ (n + 1)) M, M) :=
            ⟨boundaryInclusion (𝓡∂ (n + 1)) M, continuous_subtype_val⟩
          ∃ C : ChartedSpace (EuclideanHalfSpace (n + 1)) (BoundaryAttachment (M := M) (𝓡∂ (n + 1))),
            let _ := C
            IsManifold (𝓡∂ (n + 1)) ∞ (BoundaryAttachment (M := M) (𝓡∂ (n + 1))) ∧
            ∃ D : Diffeomorph (𝓡∂ (n + 1)) (𝓡∂ (n + 1))
                (BoundaryAttachment (M := M) (𝓡∂ (n + 1))) M ∞,
              ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ (attachmentOriginal (M := M) (𝓡∂ (n + 1))) ∧
              ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
                (𝓡∂ (n + 1)) ∞ (attachmentProduct (M := M) (𝓡∂ (n + 1))) ∧
              (∀ p, D (attachmentProduct (𝓡∂ (n + 1)) (p, 1)) = boundaryInclusion (𝓡∂ (n + 1)) M p) ∧
              (𝓡∂ (n + 1)).boundary (BoundaryAttachment (M := M) (𝓡∂ (n + 1))) =
                range (fun p : BoundaryManifold (𝓡∂ (n + 1)) M => attachmentProduct (𝓡∂ (n + 1)) (p, 1)) ∧
              let U : Opens (BoundaryManifold (𝓡∂ (n + 1)) M × Icc (-1 : ℝ) 1) :=
                ⟨{q | -1 < q.2.val ∧ q.2.val < 1},
                  (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
                    (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)⟩
              ∃ Z : Opens (BoundaryAttachment (M := M) (𝓡∂ (n + 1))),
                (Z : Set _) = DifferentialGeometry.Topology.Collar.attachmentSeam f c a hzero '' (U : Set _) ∧
                range (fun p : BoundaryManifold (𝓡∂ (n + 1)) M =>
                  attachmentOriginal (𝓡∂ (n + 1)) p.val) ⊆ Z ∧
                ∃ d : Diffeomorph ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
                    (𝓡∂ (n + 1)) U Z ∞,
                  (∀ q : U, (d q : BoundaryAttachment (M := M) (𝓡∂ (n + 1))) =
                    DifferentialGeometry.Topology.Collar.attachmentSeam f c a hzero q.val) ∧
                  ∀ z : Z, DifferentialGeometry.Topology.Collar.attachmentSeam f c a hzero (d.symm z).val = z.val := by
  obtain ⟨ε, hε, c, hc, hcs, hc0, _, δ, hδ, hδε, Y, _, _, e, he⟩ :=
    exists_closed_boundary_collar_diffeomorph hK
  refine ⟨ε, hε, ?_⟩
  let _ : Fact ((0 : ℝ) < ε) := ⟨hε⟩
  let I := 𝓡∂ (n + 1)
  let B := BoundaryManifold I M
  let J := (HasSmoothBoundary.boundaryModel I).prod (𝓡∂ 1)
  let _ : CompactSpace B := isCompact_iff_compactSpace.mp hK
  let r := δ / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : 2 * r < ε := by dsimp [r]; linarith
  have hrδ : 2 * r < δ := by dsimp [r]; linarith
  let f : C(B, M) := ⟨boundaryInclusion I M, continuous_subtype_val⟩
  obtain ⟨a, ha, har, σ, _, _, _, _, _, hnear, _, h, hO, hP, hOs, hPs⟩ :=
    DifferentialGeometry.Manifold.Collar.exists_smooth_attachment_realization hr hrε.le hrδ
      f c hc.isEmbedding hcs hc0 Y e he
  let cut : Icc (0 : ℝ) ε := ⟨a, ha.le, by linarith⟩
  have h2aε : 2 * a < ε := by linarith
  have h2aδ : 2 * a < δ := by linarith
  let C := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace (H := EuclideanHalfSpace (n + 1)) h
  let _ := C
  let D : Diffeomorph I I (BoundaryAttachment (M := M) I) M ∞ :=
    DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph h
  have hOrig : ContMDiff I I ∞ (attachmentOriginal (M := M) I) := by
    have hh := D.symm.contMDiff.comp hOs
    exact hh.congr (fun x => (h.symm_apply_apply (attachmentOriginal I x)).symm)
  have hProd : ContMDiff J I ∞ (attachmentProduct (M := M) I) := by
    have hh := D.symm.contMDiff.comp hPs
    exact hh.congr (fun q => (h.symm_apply_apply (attachmentProduct I q)).symm)
  have houter (p : B) : D (attachmentProduct I (p, 1)) = boundaryInclusion I M p := by
    change h (DifferentialGeometry.Topology.mappingCylinderProduct f (p, 1)) = _
    rw [hP]
    convert hc0 p using 1
    congr 1
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      norm_num
  have hboundary : h ⁻¹' I.boundary M =
      range (fun p : B => attachmentProduct I (p, 1)) := by
    ext z
    constructor
    · intro hz
      exact ⟨⟨h z, hz⟩, h.injective (houter ⟨h z, hz⟩)⟩
    · rintro ⟨p, rfl⟩
      change D (attachmentProduct I (p, 1)) ∈ I.boundary M
      rw [houter]
      exact p.property
  obtain ⟨Z, hZ, d, hd, hdi⟩ := DifferentialGeometry.Manifold.Collar.exists_attachmentSeam_diffeomorph
    f c cut ha h2aε.le hc0 hc.isEmbedding e he (fun _ hq => hq.2.trans h2aδ)
    σ (fun t ht => hnear t (ht.trans har.le)) h hO hP
  refine ⟨c, hc0, hc, hcs, cut, ha, h2aε, C, inferInstance, D, hOrig, hProd, houter,
    (D.preimage_boundary (by simp)).symm.trans hboundary, Z, hZ, ?_, d, hd, hdi⟩
  rintro z ⟨p, rfl⟩
  change DifferentialGeometry.Topology.mappingCylinderOriginal f p.val ∈ (Z : Set _)
  rw [hZ]
  refine ⟨(p, ⟨0, by norm_num⟩), by constructor <;> norm_num, ?_⟩
  exact (DifferentialGeometry.Topology.Collar.attachmentSeam_nonneg f c cut hc0
    (p, ⟨0, by norm_num⟩) (by norm_num)).trans (DifferentialGeometry.Topology.mappingCylinder_seam f p)

end DifferentialGeometry.Manifold.BoundaryCollar
