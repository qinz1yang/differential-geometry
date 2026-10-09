import DifferentialGeometry.Topology.Manifold.HalfClosedInterval
import DifferentialGeometry.Topology.Manifold.Attachment.RadialCap
import DifferentialGeometry.Geometry.Metric.PolarCoordinates

set_option autoImplicit false
noncomputable section
open Set Manifold IsManifold TopologicalSpace Function
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Topology.Manifold.Attachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev E1 := EuclideanSpace ℝ (Fin 1)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev Retained (B : ℝ) := S2 × Ico (0 : ℝ) B
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private def radialBall (L B : ℝ) : Opens E3 :=
  ⟨{x | ‖x‖ < L + B}, isOpen_lt continuous_norm continuous_const⟩

def retainedRadialMap {L B : ℝ} (hL : 0 < L) : Retained B → radialBall L B :=
  fun q => ⟨(L + q.2.val) • q.1.val, by
    change ‖(L + q.2.val) • q.1.val‖ < L + B
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (add_pos_of_pos_of_nonneg hL q.2.property.1),
      norm_eq_of_mem_sphere, mul_one]
    linarith [q.2.property.2]⟩

@[simp] theorem retainedRadialMap_apply {L B : ℝ} (hL : 0 < L) (q : Retained B) :
    (retainedRadialMap hL q : E3) = (L + q.2.val) • q.1.val := rfl

theorem retainedRadialMap_norm {L B : ℝ} (hL : 0 < L) (q : Retained B) :
    ‖(retainedRadialMap hL q : E3)‖ = L + q.2.val := by
  rw [retainedRadialMap_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (add_pos_of_pos_of_nonneg hL q.2.property.1), norm_eq_of_mem_sphere, mul_one]

theorem range_retainedRadialMap {L B : ℝ} (hL : 0 < L) :
    range (retainedRadialMap (B := B) hL) = {x : radialBall L B | L ≤ ‖x.val‖} := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    change L ≤ ‖(retainedRadialMap hL q : E3)‖
    rw [retainedRadialMap_norm hL q]
    linarith [q.2.property.1]
  · intro hx
    obtain ⟨q, hq⟩ := (retainedCylinderHomeomorphShell (B := B) hL).surjective ⟨x, hx⟩
    exact ⟨q, congrArg Subtype.val hq⟩

theorem retainedRadialMap_eq_attachment {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (q : Retained B) :
    retainedRadialMap hL q = radialCapAttachmentHomeomorph hL hB
      (DifferentialGeometry.Topology.adjunctionLower
        (i := radialCapBoundary hL) (retainedBoundary hB) q) := by
  apply Subtype.ext
  exact (radialCapAttachmentHomeomorph_retained hL hB q).symm

theorem retainedCylinder_boundary_eq {B : ℝ} (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    IR.boundary (Retained B) = {q | q.2.val = 0} := by
  let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) B) := halfClosedIntervalChartedSpace hB
  let : IsManifold (𝓡∂ 1) ∞ (Ico (0 : ℝ) B) := halfClosedInterval_isManifold hB
  rw [ModelWithCorners.boundary_of_boundaryless_left, halfClosedInterval_boundary_eq hB]
  ext q
  change (True ∧ q.2.val = 0) ↔ q.2.val = 0
  exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

private def modelEquiv : (E2 × ℝ) ≃L[ℝ] E3 :=
  ((ContinuousLinearEquiv.refl ℝ E2).prodCongr
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm).trans
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).symm

private def sphereCylinderChart (L : ℝ) (y : S2) :
    OpenPartialHomeomorph (S2 × ℝ) (E2 × ℝ) :=
  (chartAt E2 y).prod (Homeomorph.addLeft (-L)).toOpenPartialHomeomorph

private theorem sphereCylinderChart_smooth (L : ℝ) (y : S2) :
    ContMDiffOn IC IC ∞ (sphereCylinderChart L y) (sphereCylinderChart L y).source := by
  exact (contMDiffOn_chart (I := 𝓡 2)).prodMap
    (show ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) ∞ (Homeomorph.addLeft (-L)) univ from
      (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => -L + t)).contMDiff.contMDiffOn)

private theorem sphereCylinderChart_symm_smooth (L : ℝ) (y : S2) :
    ContMDiffOn IC IC ∞ (sphereCylinderChart L y).symm (sphereCylinderChart L y).target := by
  apply (contMDiffOn_chart_symm (I := 𝓡 2)).prodMap
  simpa [Homeomorph.addLeft] using
    (show ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ => L + t) univ from
      (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => L + t)).contMDiff.contMDiffOn)

private def ambientRadialChart (L : ℝ) (y : S2) : OpenPartialHomeomorph E3 E3 :=
  (euclideanPolarDiffeomorph (E := E3) (n := 2)).symm.toOpenPartialHomeomorph.trans
    ((sphereCylinderChart L y).trans modelEquiv.toHomeomorph.toOpenPartialHomeomorph)

private theorem modelEquiv_smooth : ContMDiff IC (𝓡 3) ∞ modelEquiv := by
  dsimp only [IC]
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact modelEquiv.contDiff.contMDiff

private theorem modelEquiv_symm_smooth : ContMDiff (𝓡 3) IC ∞ modelEquiv.symm := by
  dsimp only [IC]
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact modelEquiv.symm.contDiff.contMDiff

private theorem ambientRadialChart_mem_maximalAtlas (L : ℝ) (y : S2) :
    ambientRadialChart L y ∈ maximalAtlas (𝓡 3) ∞ E3 := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · apply (modelEquiv_smooth.contMDiffOn (s := univ)).comp
    · apply (sphereCylinderChart_smooth L y).comp
      · exact (euclideanPolarDiffeomorph (E := E3) (n := 2)).contMDiffOn_invFun.mono
          (fun _ hx => hx.1)
      · exact fun _ hx => hx.2.1
    · exact fun _ _ => mem_univ _
  · apply (euclideanPolarDiffeomorph (E := E3) (n := 2)).contMDiffOn_toFun.comp
    · apply (sphereCylinderChart_symm_smooth L y).comp modelEquiv_symm_smooth.contMDiffOn
      exact fun _ hx => hx.1.2
    · exact fun _ hx => hx.2

private theorem polar_symm_retained {L B : ℝ} (hL : 0 < L) (q : Retained B) :
    (euclideanPolarDiffeomorph (E := E3) (n := 2)).symm
      (retainedRadialMap hL q : E3) = (q.1, L + q.2.val) := by
  change (euclideanPolarDiffeomorph (E := E3) (n := 2)).symm
    (euclideanPolarDiffeomorph (E := E3) (n := 2) (q.1, L + q.2.val)) = _
  exact (euclideanPolarDiffeomorph (E := E3) (n := 2)).left_inv
    (add_pos_of_pos_of_nonneg hL q.2.property.1)

private theorem ambientRadialChart_apply {L B : ℝ} (hL : 0 < L)
    (y : S2) (q : Retained B) :
    ambientRadialChart L y (retainedRadialMap hL q : E3) =
      modelEquiv ((chartAt E2 y) q.1, q.2.val) := by
  change modelEquiv (sphereCylinderChart L y
    ((euclideanPolarDiffeomorph (E := E3) (n := 2)).symm
      (retainedRadialMap hL q : E3))) = _
  rw [polar_symm_retained hL q]
  congr 1
  change ((chartAt E2 y) q.1, -L + (L + q.2.val)) = _
  rw [neg_add_cancel_left]

private theorem retained_mem_ambientRadialChart_source {L B : ℝ} (hL : 0 < L)
    (q : Retained B) :
    (retainedRadialMap hL q : E3) ∈ (ambientRadialChart L q.1).source := by
  change (retainedRadialMap hL q : E3) ≠ 0 ∧
    (euclideanPolarDiffeomorph (E := E3) (n := 2)).symm
      (retainedRadialMap hL q : E3) ∈
      ((sphereCylinderChart L q.1).trans modelEquiv.toHomeomorph.toOpenPartialHomeomorph).source
  refine ⟨?_, ?_⟩
  · exact euclideanPolarMap_ne_zero (q := (q.1, L + q.2.val))
      (add_pos_of_pos_of_nonneg hL q.2.property.1)
  · rw [polar_symm_retained hL q]
    exact ⟨⟨mem_chart_source E2 q.1, mem_univ _⟩, mem_univ _⟩

private theorem restrictedChart_mem_maximalAtlas (U : Opens E3) (hU : Nonempty U)
    (e : OpenPartialHomeomorph E3 E3) (he : e ∈ maximalAtlas (𝓡 3) ∞ E3) :
    e.subtypeRestr hU ∈ maximalAtlas (𝓡 3) ∞ U := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e ∘ (Subtype.val : U → E3))
      (e.subtypeRestr hU).source
    exact (contMDiffOn_of_mem_maximalAtlas he).comp
      (contMDiff_subtype_val (U := U)).contMDiffOn
      (fun x hx => by simpa only [e.subtypeRestr_source hU] using hx)
  · intro z hz
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U (e.subtypeRestr hU).symm
      (e.subtypeRestr hU).target z).mp
    apply ((contMDiffOn_symm_of_mem_maximalAtlas he).mono
      (e.subtypeRestr_target_subset hU)).congr
      (fun w hw => e.subtypeRestr_symm_apply hU hw) z hz

private def normalEquiv : ((E2 × E1) × Unit) ≃L[ℝ] E3 :=
  (ContinuousLinearEquiv.prodUnique ℝ (E2 × E1) Unit).trans
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).symm

theorem isSmoothEmbedding_retainedRadialMap {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    IsSmoothEmbedding IR (𝓡 3) ∞ (retainedRadialMap (B := B) hL) := by
  let : ChartedSpace (EuclideanHalfSpace 1) (Ico (0 : ℝ) B) := halfClosedIntervalChartedSpace hB
  let : IsManifold (𝓡∂ 1) ∞ (Ico (0 : ℝ) B) := halfClosedInterval_isManifold hB
  refine ⟨?_, ?_⟩
  · suffices h : IsImmersionOfComplement Unit IR (𝓡 3) ∞
        (retainedRadialMap (B := B) hL) from h.isImmersion
    intro q
    have hBall : Nonempty (radialBall L B) := ⟨⟨0, by simpa [radialBall] using add_pos hL hB⟩⟩
    let e := ambientRadialChart L q.1
    let c := e.subtypeRestr hBall
    refine IsImmersionAtOfComplement.mk_of_continuousAt
      (show ContinuousAt (retainedRadialMap (B := B) hL) q from by
        unfold retainedRadialMap
        fun_prop) normalEquiv
      (chartAt (ModelProd E2 (EuclideanHalfSpace 1)) q) c
      (mem_chart_source _ q) (by
        simpa only [c, e, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using
          retained_mem_ambientRadialChart_source hL q)
      (chart_mem_maximalAtlas _) (restrictedChart_mem_maximalAtlas _ hBall e
        (ambientRadialChart_mem_maximalAtlas L q.1)) ?_
    intro z hz
    let p : Retained B := ((chartAt (ModelProd E2 (EuclideanHalfSpace 1)) q).extend IR).symm z
    have heq := ((chartAt (ModelProd E2 (EuclideanHalfSpace 1)) q).extend IR).right_inv hz
    have hcoords : extChartAt IR q p =
        ((chartAt E2 q.1) p.1, (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm p.2.val) := by
      apply Prod.ext
      · rfl
      · ext i
        fin_cases i
        change (extChartAt (𝓡∂ 1) q.2 p.2) 0 = p.2.val
        simpa using halfClosedInterval_extChartAt_apply hB q.2 p.2
    change ambientRadialChart L q.1 (retainedRadialMap hL p : E3) = normalEquiv (z, 0)
    rw [ambientRadialChart_apply hL q.1 p]
    have hzcoords : z =
        ((chartAt E2 q.1) p.1, (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm p.2.val) :=
      heq.symm.trans hcoords
    rw [hzcoords]
    rfl
  · exact _root_.Topology.IsEmbedding.subtypeVal.comp
      (retainedCylinderHomeomorphShell (B := B) hL).isEmbedding

end DifferentialGeometry.Topology.Manifold.Attachment
