import DifferentialGeometry.Topology.Manifold.ClosedBall
import DifferentialGeometry.Geometry.Boundary.Metric.Induced
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace

set_option autoImplicit false
noncomputable section
open Set Manifold IsManifold Filter
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Handle
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  closedCellChartedSpaceSucc 2
private local instance : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) := closedCellIsManifold 2

private local instance : Nonempty (HasSmoothBoundary.boundaryH (𝓡∂ 3)) :=
  show Nonempty (EuclideanSpace ℝ (Fin 2)) from inferInstance

private local instance {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) (BoundaryManifold (𝓡∂ 3) M) :=
  BoundaryManifold.chartedSpace (I := 𝓡∂ 3)

private local instance {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] : IsManifold (𝓡 2) ∞ (BoundaryManifold (𝓡∂ 3) M) :=
  BoundaryManifold.isManifold (I := 𝓡∂ 3)

def closedBallUnitHomeomorph {L : ℝ} (hL : 0 < L) :
    {x : E3 // ‖x‖ ≤ L} ≃ₜ ClosedCell 3 where
  toFun x := ⟨L⁻¹ • x.val, by
    change ‖L⁻¹ • x.val‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    calc L⁻¹ * ‖x.val‖ ≤ L⁻¹ * L := mul_le_mul_of_nonneg_left x.property (by positivity)
      _ = 1 := inv_mul_cancel₀ hL.ne'⟩
  invFun x := ⟨L • x.val, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
    nlinarith [x.property]⟩
  left_inv x := by apply Subtype.ext; simp [smul_smul, hL.ne']
  right_inv x := by apply Subtype.ext; simp [smul_smul, hL.ne']
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[reducible] def closedBallChartedSpace {L : ℝ} (hL : 0 < L) :
    ChartedSpace (EuclideanHalfSpace 3) {x : E3 // ‖x‖ ≤ L} :=
  chartedSpaceOfHomeomorph (closedBallUnitHomeomorph hL)

theorem closedBall_chartAt {L : ℝ} (hL : 0 < L) (x : {x : E3 // ‖x‖ ≤ L}) :
    letI := closedBallChartedSpace hL
    chartAt (EuclideanHalfSpace 3) x =
      (closedBallUnitHomeomorph hL).toOpenPartialHomeomorph.trans
        (chartAt (EuclideanHalfSpace 3) (closedBallUnitHomeomorph hL x)) := rfl

theorem closedBall_isManifold {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    IsManifold (𝓡∂ 3) ∞ {x : E3 // ‖x‖ ≤ L} :=
  isManifoldOfHomeomorph (𝓡∂ 3) (closedBallUnitHomeomorph hL)

def closedBallUnitDiffeomorph {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    {x : E3 // ‖x‖ ≤ L} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3 := by
  letI := closedBallChartedSpace hL
  exact
    { toEquiv := (closedBallUnitHomeomorph hL).toEquiv
      contMDiff_toFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph
        (closedBallUnitHomeomorph hL) (𝓡∂ 3) ∞
      contMDiff_invFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph
        (closedBallUnitHomeomorph hL) (𝓡∂ 3) ∞ }

@[simp] theorem closedBallUnitDiffeomorph_apply {L : ℝ} (hL : 0 < L)
    (x : {x : E3 // ‖x‖ ≤ L}) :
    letI := closedBallChartedSpace hL
    (closedBallUnitDiffeomorph hL x).val = L⁻¹ • x.val := rfl

@[simp] theorem closedBallUnitDiffeomorph_symm_apply {L : ℝ} (hL : 0 < L)
    (x : ClosedCell 3) :
    letI := closedBallChartedSpace hL
    ((closedBallUnitDiffeomorph hL).symm x).val = L • x.val := rfl

theorem closedBall_boundary_eq_sphere {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    (𝓡∂ 3).boundary {x : E3 // ‖x‖ ≤ L} = {x | ‖x.val‖ = L} := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  rw [← (closedBallUnitDiffeomorph hL).preimage_boundary (by simp),
    closedCell_boundary_eq_sphere 2]
  ext x
  change ‖L⁻¹ • x.val‖ = 1 ↔ ‖x.val‖ = L
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
  constructor
  · intro h
    have h' := congrArg (fun t : ℝ => L * t) h
    simpa [← mul_assoc, hL.ne'] using h'
  · intro h
    rw [h, inv_mul_cancel₀ hL.ne']

private def ambientNormalization {L : ℝ} (hL : 0 < L) : E3 ≃ₜ E3 :=
  Homeomorph.smulOfNeZero L⁻¹ (inv_ne_zero hL.ne')

private theorem ambientNormalization_smooth {L : ℝ} (hL : 0 < L) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (ambientNormalization hL) := by
  change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : E3 => L⁻¹ • x)
  exact (by fun_prop : ContDiff ℝ ∞ (fun x : E3 => L⁻¹ • x)).contMDiff

private theorem ambientNormalization_symm_smooth {L : ℝ} (hL : 0 < L) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (ambientNormalization hL).symm := by
  change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : E3 => (L⁻¹)⁻¹ • x)
  exact (by fun_prop : ContDiff ℝ ∞ (fun x : E3 => (L⁻¹)⁻¹ • x)).contMDiff

theorem isSmoothEmbedding_closedBall_inclusion {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val : {x : E3 // ‖x‖ ≤ L} → E3) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  refine ⟨?_, _root_.Topology.IsEmbedding.subtypeVal⟩
  have hu : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val : ClosedCell 3 → E3) :=
    isSmoothEmbedding_closedCell_inclusion 2
  obtain ⟨F, hF, hF', hunit⟩ := hu.isImmersion
  let := hF
  let := hF'
  refine ⟨F, hF, hF', ?_⟩
  intro x
  let d := closedBallUnitDiffeomorph hL
  let a := ambientNormalization hL
  let h := hunit (d x)
  let c := d.toHomeomorph.toOpenPartialHomeomorph.trans h.domChart
  let c' := a.toOpenPartialHomeomorph.trans h.codChart
  have hc : c ∈ maximalAtlas (𝓡∂ 3) ∞ {x : E3 // ‖x‖ ≤ L} := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).comp
        d.contMDiff.contMDiffOn (fun _ hy => hy.2)
    · change ContMDiffOn (𝓡∂ 3) (𝓡∂ 3) ∞ (d.symm ∘ h.domChart.symm) c.target
      have hd : ContMDiffOn (𝓡∂ 3) (𝓡∂ 3) ∞ d.symm univ := d.symm.contMDiff.contMDiffOn
      exact hd.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mono
          (fun _ hy => hy.1)) (fun _ _ => mem_univ _)
  have hc' : c' ∈ maximalAtlas (𝓡 3) ∞ E3 := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        (ambientNormalization_smooth hL).contMDiffOn (fun _ hy => hy.2)
    · change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (a.symm ∘ h.codChart.symm) c'.target
      have ha : ContMDiffOn (𝓡 3) (𝓡 3) ∞ a.symm univ :=
        (ambientNormalization_symm_smooth hL).contMDiffOn
      exact ha.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mono
          (fun _ hy => hy.1)) (fun _ _ => mem_univ _)
  apply IsImmersionAtOfComplement.mk_of_continuousAt continuous_subtype_val.continuousAt
    h.equiv c c' ⟨mem_univ _, h.mem_domChart_source⟩
    ⟨mem_univ _, h.mem_codChart_source⟩ hc hc'
  intro z hz
  have hz' : z ∈ (h.domChart.extend (𝓡∂ 3)).target := by
    rw [OpenPartialHomeomorph.extend_target] at hz ⊢
    exact ⟨hz.1.1, hz.2⟩
  have hnormal := h.writtenInCharts hz'
  change h.codChart ((h.domChart.extend (𝓡∂ 3)).symm z).val = h.equiv (z, 0) at hnormal
  change h.codChart (L⁻¹ • (L • ((h.domChart.extend (𝓡∂ 3)).symm z).val)) = h.equiv (z, 0)
  simpa only [smul_smul, inv_mul_cancel₀ hL.ne', one_smul] using hnormal

private theorem contMDiff_into_boundary
    {E H M F K N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    [hI : HasSmoothBoundary E H I] [Nonempty hI.boundaryH] [IsManifold I ∞ M]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
    {J : ModelWithCorners ℝ F K} [TopologicalSpace N] [ChartedSpace K N]
    (f : N → BoundaryManifold I M)
    (hf : ContMDiff J I ∞ (fun x => (f x : M))) : ContMDiff J hI.boundaryI ∞ f := by
  intro x
  have hc : ContinuousAt f x := (continuous_induced_rng.mpr hf.continuous).continuousAt
  rw [contMDiffAt_iff_target_of_mem_source (mem_chart_source hI.boundaryH (f x))]
  refine ⟨hc, ?_⟩
  have hext : ContMDiffAt J 𝓘(ℝ, E) ∞
      (extChartAt I (f x : M) ∘ (fun y => (f y : M))) x :=
    (contMDiffAt_extChartAt (I := I) (x := (f x : M))).comp x (hf x)
  apply (hI.projE_contDiff.contMDiff.contMDiffAt.comp x hext).congr_of_eventuallyEq
  have hevent : ∀ᶠ y in 𝓝 x, (f y : M) ∈ (chartAt H (f x : M)).source :=
    (hf x).continuousAt.eventually
      ((chartAt H (f x : M)).open_source.mem_nhds (mem_chart_source H (f x : M)))
  filter_upwards [hevent] with y hy
  change hI.boundaryI (chartAt hI.boundaryH (f x) (f y)) =
    hI.projE (I (chartAt H (f x : M) (f y : M)))
  have hchart : chartAt hI.boundaryH (f x) = BoundaryManifold.boundaryChart (I := I) (f x) :=
    BoundaryManifold.defaultBoundaryChart_eq_boundaryChart (I := I) (f x)
  rw [hchart]
  have hincl := BoundaryManifold.inclH_boundaryChart_apply (I := I) (f x) (f y) hy
  rw [← hincl]
  exact (hI.proj_inclH_compat (BoundaryManifold.boundaryChart (I := I) (f x) (f y))).symm

private theorem boundary_point_norm {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    ∀ b : BoundaryManifold (𝓡∂ 3) {x : E3 // ‖x‖ ≤ L}, ‖b.val.val‖ = L := by
  let := closedBallChartedSpace hL
  intro b
  exact (Set.ext_iff.mp (closedBall_boundary_eq_sphere hL) b.val).mp b.property

private def closedBallBoundaryForward {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    BoundaryManifold (𝓡∂ 3) {x : E3 // ‖x‖ ≤ L} → S2 := by
  letI := closedBallChartedSpace hL
  intro b
  refine ⟨L⁻¹ • b.val.val, ?_⟩
  rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL),
    boundary_point_norm hL b, inv_mul_cancel₀ hL.ne']

private def closedBallBoundaryInverseBall {L : ℝ} (hL : 0 < L) :
    S2 → {x : E3 // ‖x‖ ≤ L} := fun y =>
  ⟨L • y.val, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL, norm_eq_of_mem_sphere, mul_one]⟩

private def closedBallBoundaryInverse {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    S2 → BoundaryManifold (𝓡∂ 3) {x : E3 // ‖x‖ ≤ L} := by
  letI := closedBallChartedSpace hL
  intro y
  refine ⟨closedBallBoundaryInverseBall hL y, ?_⟩
  rw [closedBall_boundary_eq_sphere hL]
  change ‖L • y.val‖ = L
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL, norm_eq_of_mem_sphere, mul_one]

private theorem closedBallBoundaryForward_smooth {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ContMDiff (𝓡 2) (𝓡 2) ∞ (closedBallBoundaryForward hL) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  have hi : ContMDiff (𝓡 2) (𝓡∂ 3) ∞
      (boundaryInclusion (𝓡∂ 3) {x : E3 // ‖x‖ ≤ L}) := boundaryInclusion_contMDiff
  have hb : ContMDiff (𝓡 2) (𝓡 3) ∞
      (fun b : BoundaryManifold (𝓡∂ 3) {x : E3 // ‖x‖ ≤ L} => b.val.val) :=
    (isSmoothEmbedding_closedBall_inclusion hL).isImmersion.contMDiff.comp hi
  have hc : ContMDiff (𝓡 2) 𝓘(ℝ) ∞
      (fun _ : BoundaryManifold (𝓡∂ 3) {x : E3 // ‖x‖ ≤ L} => L⁻¹) := contMDiff_const
  exact (hc.smul hb).codRestrict_sphere (fun b => (closedBallBoundaryForward hL b).property)

private theorem closedBallBoundaryInverseBall_smooth {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    ContMDiff (𝓡 2) (𝓡∂ 3) ∞ (closedBallBoundaryInverseBall hL) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  intro y
  apply (ContMDiffAt.iff_comp_isImmersionAt
    ((isSmoothEmbedding_closedBall_inclusion hL).isImmersion.isImmersionAt
      (closedBallBoundaryInverseBall hL y))).mpr
  constructor
  · exact (show Continuous (closedBallBoundaryInverseBall hL) from by
      unfold closedBallBoundaryInverseBall
      fun_prop).continuousAt
  · change ContMDiffAt (𝓡 2) (𝓡 3) ∞ (fun z : S2 => L • z.val) y
    have hc : ContMDiff (𝓡 2) 𝓘(ℝ) ∞ (fun _ : S2 => L) := contMDiff_const
    exact (hc.smul (contMDiff_coe_sphere (n := 2))).contMDiffAt

private theorem closedBallBoundaryInverse_smooth {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ContMDiff (𝓡 2) (𝓡 2) ∞ (closedBallBoundaryInverse hL) := by
  let := closedBallChartedSpace hL
  let := closedBall_isManifold hL
  apply contMDiff_into_boundary (closedBallBoundaryInverse hL)
  exact closedBallBoundaryInverseBall_smooth hL

def closedBallBoundaryDiffeomorph {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    BoundaryManifold (𝓡∂ 3) {x : E3 // ‖x‖ ≤ L} ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2 := by
  letI := closedBallChartedSpace hL
  letI := closedBall_isManifold hL
  exact
    { toFun := closedBallBoundaryForward hL
      invFun := closedBallBoundaryInverse hL
      left_inv := fun b => by
        apply BoundaryManifold.ext
        apply Subtype.ext
        change L • (L⁻¹ • b.val.val) = b.val.val
        simp [smul_smul, hL.ne']
      right_inv := fun y => by
        apply Subtype.ext
        change L⁻¹ • (L • y.val) = y.val
        simp [smul_smul, hL.ne']
      contMDiff_toFun := closedBallBoundaryForward_smooth hL
      contMDiff_invFun := closedBallBoundaryInverse_smooth hL }

@[simp] theorem closedBallBoundaryDiffeomorph_apply {L : ℝ} (hL : 0 < L) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ∀ b : BoundaryManifold (𝓡∂ 3) {x : E3 // ‖x‖ ≤ L},
      (closedBallBoundaryDiffeomorph hL b).val = L⁻¹ • b.val.val := fun _ => rfl

@[simp] theorem closedBallBoundaryDiffeomorph_symm_apply {L : ℝ} (hL : 0 < L) (y : S2) :
    letI := closedBallChartedSpace hL
    letI := closedBall_isManifold hL
    ((closedBallBoundaryDiffeomorph hL).symm y).val.val = L • y.val := rfl

end DifferentialGeometry.Topology.Manifold
