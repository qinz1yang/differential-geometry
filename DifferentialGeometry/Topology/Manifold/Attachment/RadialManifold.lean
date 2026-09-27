import DifferentialGeometry.Topology.Manifold.Attachment.RadialEmbedding
import DifferentialGeometry.Topology.Manifold.ScaledClosedBall

set_option autoImplicit false
noncomputable section
open Set Manifold IsManifold TopologicalSpace Function
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Handle
open DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.Manifold.Attachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev Retained (B : ℝ) := S2 × Ico (0 : ℝ) B
private abbrev IR := (𝓡 2).prod (𝓡∂ 1)
private def radialBall (L B : ℝ) : Opens E3 :=
  ⟨{x | ‖x‖ < L + B}, isOpen_lt continuous_norm continuous_const⟩
private abbrev Attachment {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :=
  AdjunctionSpace (radialCapBoundary hL) (retainedBoundary hB)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

@[reducible] def radialCapAttachmentChartedSpace {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    ChartedSpace E3 (Attachment hL hB) :=
  chartedSpaceOfHomeomorph (M := radialBall L B) (radialCapAttachmentHomeomorph hL hB : Attachment hL hB ≃ₜ radialBall L B)

theorem radialCapAttachment_chartAt {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (x : Attachment hL hB) :
    letI := radialCapAttachmentChartedSpace hL hB
    chartAt E3 x = (radialCapAttachmentHomeomorph hL hB).toOpenPartialHomeomorph.trans
      (chartAt (M := radialBall L B) E3 (radialCapAttachmentHomeomorph hL hB x)) := rfl

theorem radialCapAttachment_t2Space {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    T2Space (Attachment hL hB) :=
  (radialCapAttachmentHomeomorph hL hB).isEmbedding.t2Space

theorem radialCapAttachment_secondCountableTopology {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    SecondCountableTopology (Attachment hL hB) :=
  (radialCapAttachmentHomeomorph hL hB).secondCountableTopology

theorem radialCapAttachment_isManifold {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := radialCapAttachmentChartedSpace hL hB
    IsManifold (𝓡 3) ∞ (Attachment hL hB) := by
  let := radialCapAttachmentChartedSpace hL hB
  exact @isManifoldOfHomeomorph ℝ _ E3 E3 _ _ _ (𝓡 3) (radialBall L B) _
    ((radialBall L B).instChartedSpace) ∞ (Attachment hL hB) _
    (radialCapAttachmentHomeomorph hL hB) inferInstance

theorem radialCapAttachment_boundary_eq_empty {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := radialCapAttachmentChartedSpace hL hB
    (𝓡 3).boundary (Attachment hL hB) = ∅ := by
  let := radialCapAttachmentChartedSpace hL hB
  exact ModelWithCorners.Boundaryless.boundary_eq_empty

def radialCapAttachmentDiffeomorph {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := radialCapAttachmentChartedSpace hL hB
    Attachment hL hB ≃ₘ⟮𝓡 3, 𝓡 3⟯ radialBall L B := by
  let := radialCapAttachmentChartedSpace hL hB
  let e : Attachment hL hB ≃ₜ radialBall L B := radialCapAttachmentHomeomorph hL hB
  exact
    { toEquiv := e.toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph e (𝓡 3) ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph e (𝓡 3) ∞ }

@[simp] theorem radialCapAttachmentDiffeomorph_apply {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (x : Attachment hL hB) :
    letI := radialCapAttachmentChartedSpace hL hB
    radialCapAttachmentDiffeomorph hL hB x = radialCapAttachmentHomeomorph hL hB x := rfl

@[simp] theorem radialCapAttachmentDiffeomorph_symm_apply {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    (x : radialBall L B) :
    letI := radialCapAttachmentChartedSpace hL hB
    (radialCapAttachmentDiffeomorph hL hB).symm x =
      (radialCapAttachmentHomeomorph hL hB).symm x := rfl

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

private theorem smoothEmbedding_into_open
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (U : Opens E3) (f : M → U)
    (hf : IsSmoothEmbedding I (𝓡 3) ∞ (fun x => (f x : E3))) :
    IsSmoothEmbedding I (𝓡 3) ∞ f := by
  refine ⟨?_, (_root_.Topology.IsEmbedding.subtypeVal.of_comp_iff).mp hf.isEmbedding⟩
  obtain ⟨F, hF, hF', hfimm⟩ := hf.isImmersion
  let := hF
  let := hF'
  refine ⟨F, hF, hF', ?_⟩
  intro x
  let h := hfimm x
  have hU : Nonempty U := ⟨f x⟩
  let c := h.codChart.subtypeRestr hU
  refine IsImmersionAtOfComplement.mk_of_continuousAt
    (show ContinuousAt f x from (continuous_induced_rng.mpr hf.contMDiff.continuous).continuousAt)
    h.equiv h.domChart c h.mem_domChart_source ?_ h.domChart_mem_maximalAtlas
    (restrictedChart_mem_maximalAtlas U hU h.codChart h.codChart_mem_maximalAtlas) ?_
  · simpa only [c, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using h.mem_codChart_source
  · exact h.writtenInCharts

private theorem smoothEmbedding_into_attachment {L B : ℝ} (hL : 0 < L) (hB : 0 < B)
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (f : M → Attachment hL hB)
    (hf : IsSmoothEmbedding I (𝓡 3) ∞
      (radialCapAttachmentHomeomorph hL hB ∘ f : M → radialBall L B)) :
    letI := radialCapAttachmentChartedSpace hL hB
    IsSmoothEmbedding I (𝓡 3) ∞ f := by
  let := radialCapAttachmentChartedSpace hL hB
  let := radialCapAttachment_isManifold hL hB
  let d := radialCapAttachmentDiffeomorph hL hB
  refine ⟨?_, ((radialCapAttachmentHomeomorph hL hB).isEmbedding.of_comp_iff).mp hf.isEmbedding⟩
  obtain ⟨F, hF, hF', hfimm⟩ := hf.isImmersion
  let := hF
  let := hF'
  refine ⟨F, hF, hF', ?_⟩
  intro x
  let h := hfimm x
  let c := d.toHomeomorph.toOpenPartialHomeomorph.trans h.codChart
  have hc : c ∈ maximalAtlas (𝓡 3) ∞ (Attachment hL hB) := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        d.contMDiff.contMDiffOn (fun _ hy => hy.2)
    · change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (d.symm ∘ h.codChart.symm) c.target
      have hd : ContMDiffOn (𝓡 3) (𝓡 3) ∞ d.symm univ := d.symm.contMDiff.contMDiffOn
      exact hd.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mono
          (fun _ hy => hy.1)) (fun _ _ => mem_univ _)
  refine IsImmersionAtOfComplement.mk_of_continuousAt
    (show ContinuousAt f x from
      ((radialCapAttachmentHomeomorph hL hB).isEmbedding.continuous_iff.mpr
        hf.contMDiff.continuous).continuousAt)
    h.equiv h.domChart c h.mem_domChart_source ⟨mem_univ _, h.mem_codChart_source⟩
    h.domChart_mem_maximalAtlas hc ?_
  exact h.writtenInCharts

theorem isSmoothEmbedding_radialCapAttachment_cap {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := closedBallChartedSpace hL
    letI := radialCapAttachmentChartedSpace hL hB
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞
      (adjunctionCell (radialCapBoundary hL) (retainedBoundary hB)) := by
  let := closedBallChartedSpace hL
  apply smoothEmbedding_into_attachment hL hB
  apply smoothEmbedding_into_open (radialBall L B)
  exact isSmoothEmbedding_closedBall_inclusion hL

theorem isSmoothEmbedding_radialCapAttachment_retained {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :
    letI := halfClosedIntervalChartedSpace hB
    letI := radialCapAttachmentChartedSpace hL hB
    IsSmoothEmbedding IR (𝓡 3) ∞
      (adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB)) := by
  let := halfClosedIntervalChartedSpace hB
  apply smoothEmbedding_into_attachment hL hB
  have hmap : (radialCapAttachmentHomeomorph hL hB ∘
      adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB) :
      Retained B → radialBall L B) = retainedRadialMap hL := by
    apply funext
    intro q
    exact (retainedRadialMap_eq_attachment hL hB q).symm
  rw [hmap]
  exact isSmoothEmbedding_retainedRadialMap hL hB

end DifferentialGeometry.Topology.Manifold.Attachment
