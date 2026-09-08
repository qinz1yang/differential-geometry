import DifferentialGeometry.Bundle.Equiv
import DifferentialGeometry.Geometry.Metric.BundleContinuity
import DifferentialGeometry.Geometry.Metric.OrthonormalFrame.Principal
import DifferentialGeometry.Geometry.LieGroup.Orthogonal
import DifferentialGeometry.Topology.Manifold.Atlas
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section

open Bundle Set
open scoped Topology Manifold ContDiff

namespace LinearIsometryEquiv

variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [ChartedSpace H B]
  {n : ℕ∞ω} [IsContMDiffRiemannianBundle I n F V]

theorem contMDiffOn_coframe_transition {U U' : Set B} {q r : ∀ x, V x ≃ₗᵢ[ℝ] F}
    (hq : ∀ w : F, ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
      (fun x => (⟨x, (q x).symm w⟩ : TotalSpace F V)) U)
    (hr : ∀ w : F, ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
      (fun x => (⟨x, (r x).symm w⟩ : TotalSpace F V)) U') :
    ContMDiffOn I 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)) n
      (fun x => (q x).symm.trans (r x)) (U ∩ U') := by
  apply contMDiffOn_iff.mpr
  intro x hx
  apply contMDiffWithinAt_clm_of_pointwise
  intro w
  have h : ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
      (fun y => (y, r y ((q y).symm w))) (U ∩ U') :=
    (contMDiffOn_coframe hr).comp ((hq w).mono inter_subset_left) (fun _ hy => hy.2)
  exact (h x hx).snd

end LinearIsometryEquiv

namespace FiberBundle

variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [ChartedSpace H B]
  (n : ℕ∞ω) [IsContMDiffRiemannianBundle I n F V]

private def smoothCoframeChart [IsContinuousRiemannianBundle F V]
    (U : Set B) (hU : IsOpen U) (q : ∀ x, V x ≃ₗᵢ[ℝ] F)
    (hq : ∀ w : F, ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
      (fun x => (⟨x, (q x).symm w⟩ : TotalSpace F V)) U) :
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    OpenPartialHomeomorph
      (TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) (B × (F ≃ₗᵢ[ℝ] F)) :=
  let _ := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  ((orthonormalFramePrebundle (F := F) V).trivializationOfMemPretrivializationAtlas
    ⟨U, hU, q, (fun w => (hq w).continuousOn), rfl⟩).toOpenPartialHomeomorph

@[instance_reducible]
private def smoothCoframeChartedSpace [IsContinuousRiemannianBundle F V]
    [ContMDiffVectorBundle n F V I] :
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    ChartedSpace (B × (F ≃ₗᵢ[ℝ] F))
      (TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) := by
  classical
  let := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  have hex (x : B) := LinearIsometryEquiv.exists_contMDiff_coframe (I := I) (n := n)
    x (linearIsometryEquivAt (F := F) V x)
  choose U hU hx q hq₀ hq using hex
  exact
    { atlas := {e | ∃ (U : Set B) (hU : IsOpen U) (q : ∀ x, V x ≃ₗᵢ[ℝ] F)
          (hq : ∀ w : F, ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
            (fun x => (⟨x, (q x).symm w⟩ : TotalSpace F V)) U),
          e = smoothCoframeChart V I n U hU q hq}
      chartAt z := smoothCoframeChart V I n (U z.proj) (hU z.proj) (q z.proj) (hq z.proj)
      mem_chart_source z := hx z.proj
      chart_mem_atlas z := ⟨U z.proj, hU z.proj, q z.proj, hq z.proj, rfl⟩ }

@[instance_reducible]
def orthonormalFrameChartedSpace [ContMDiffVectorBundle n F V I] :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    ChartedSpace (ModelProd H (skewAdjoint.submodule ℝ (F →L[ℝ] F)))
      (TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) := by
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
  let := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := smoothCoframeChartedSpace (F := F) V I n
  exact ChartedSpace.comp _ (B × (F ≃ₗᵢ[ℝ] F)) _

theorem orthonormalFrame_isManifold [ContMDiffVectorBundle n F V I]
    [IsManifold I n B] :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := orthonormalFrameChartedSpace (F := F) V I n
    IsManifold (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) n
      (TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) := by
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
  let := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := smoothCoframeChartedSpace (F := F) V I n
  apply isManifold_of_contMDiffOn
  rintro _ _ ⟨U, hU, q, hq, rfl⟩ ⟨U', hU', r, hr, rfl⟩
  change ContMDiffOn _ _ n
    (fun z : B × (F ≃ₗᵢ[ℝ] F) => (z.1, z.2 * ((r z.1).symm.trans (q z.1))))
    ((Pretrivialization.orthonormalFrame q U hU).target ∩
      (Pretrivialization.orthonormalFrame q U hU).toPartialEquiv.symm ⁻¹'
        (Pretrivialization.orthonormalFrame r U' hU').source)
  rw [Pretrivialization.target_inter_preimage_symm_source_eq]
  have ht : ContMDiffOn I 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)) n
      (fun x => (r x).symm.trans (q x)) (U' ∩ U) :=
    LinearIsometryEquiv.contMDiffOn_coframe_transition hr hq
  exact contMDiffOn_fst.prodMk (contMDiffOn_snd.mul
    (ht.comp contMDiffOn_fst (fun _ hz => hz.1)))

section Maps

variable [ContMDiffVectorBundle n F V I] [IsManifold I n B]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {b : P → B} {q : ∀ z, V (b z) ≃ₗᵢ[ℝ] F}

theorem contMDiffWithinAt_orthonormalFrame_of_symm {s : Set P} {z₀ : P}
    (hq : ∀ w : F, ContMDiffWithinAt IP (I.prod 𝓘(ℝ, F)) n
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) s z₀) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := orthonormalFrameChartedSpace (F := F) V I n
    ContMDiffWithinAt IP (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) n
      (fun z => (⟨b z, q z⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))) s z₀ := by
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
  let := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := smoothCoframeChartedSpace (F := F) V I n
  let := orthonormalFrameChartedSpace (F := F) V I n
  have hb : ContMDiffWithinAt IP I n b s z₀ := by
    have h := hq 0
    rw [Bundle.contMDiffWithinAt_totalSpace] at h
    exact h.1
  obtain ⟨U, hU, hx, r, hr₀, hr⟩ :=
    LinearIsometryEquiv.exists_contMDiff_coframe (I := I) (n := n) (b z₀) (q z₀)
  let e := smoothCoframeChart V I n U hU r hr
  have he : e ∈ atlas (B × (F ≃ₗᵢ[ℝ] F))
      (TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) := ⟨U, hU, r, hr, rfl⟩
  have hi : ContMDiffWithinAt IP 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)) n
      (fun z => (q z).symm.trans (r (b z))) s z₀ := by
    apply LinearIsometryEquiv.contMDiffWithinAt_iff.mpr
    apply contMDiffWithinAt_clm_of_pointwise
    intro w
    have hf := (LinearIsometryEquiv.contMDiffOn_coframe hr).contMDiffAt
      (x := (⟨b z₀, (q z₀).symm w⟩ : TotalSpace F V))
      ((hU.preimage (continuous_proj F V)).mem_nhds hx)
    exact (hf.comp_contMDiffWithinAt z₀ (hq w)).snd
  have hg : ContMDiffWithinAt IP 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)) n
      (fun z => (r (b z)).symm.trans (q z)) s z₀ := by
    simpa only [LinearIsometryEquiv.inv_def, LinearIsometryEquiv.symm_trans,
      LinearIsometryEquiv.symm_symm] using hi.inv
  have hei := ChartedSpace.contMDiffOn_symm_of_mem_atlas_comp
    (I := I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) he
    (orthonormalFrame_isManifold (F := F) V I n)
  have ht : (b z₀, (r (b z₀)).symm.trans (q z₀)) ∈ e.target := ⟨hx, mem_univ _⟩
  have h := (hei.contMDiffAt (e.open_target.mem_nhds ht)).comp_contMDiffWithinAt z₀
    (hb.prodMk hg)
  have heq (z : P) : (⟨b z, q z⟩ :
      TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) =
        e.symm (b z, (r (b z)).symm.trans (q z)) := by
    apply TotalSpace.mk_inj.mpr
    ext w
    change q z w = q z ((r (b z)).symm (r (b z) w))
    rw [LinearIsometryEquiv.symm_apply_apply]
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall heq) (heq z₀)

theorem contMDiffAt_orthonormalFrame_of_symm {z₀ : P}
    (hq : ∀ w : F, ContMDiffAt IP (I.prod 𝓘(ℝ, F)) n
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) z₀) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := orthonormalFrameChartedSpace (F := F) V I n
    ContMDiffAt IP (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) n
      (fun z => (⟨b z, q z⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))) z₀ :=
  contMDiffWithinAt_orthonormalFrame_of_symm V I n hq

theorem contMDiffOn_orthonormalFrame_of_symm {s : Set P}
    (hq : ∀ w : F, ContMDiffOn IP (I.prod 𝓘(ℝ, F)) n
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) s) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := orthonormalFrameChartedSpace (F := F) V I n
    ContMDiffOn IP (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) n
      (fun z => (⟨b z, q z⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))) s :=
  fun z hz => contMDiffWithinAt_orthonormalFrame_of_symm V I n (fun w => hq w z hz)

theorem contMDiff_orthonormalFrame_of_symm
    (hq : ∀ w : F, ContMDiff IP (I.prod 𝓘(ℝ, F)) n
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V))) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := orthonormalFrameChartedSpace (F := F) V I n
    ContMDiff IP (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) n
      (fun z => (⟨b z, q z⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))) :=
  fun z => contMDiffAt_orthonormalFrame_of_symm V I n (fun w => hq w z)

end Maps

theorem contMDiff_orthonormalFrame_symm_apply [ContMDiffVectorBundle n F V I]
    [IsManifold I n B] :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := orthonormalFrameChartedSpace (F := F) V I n
    ContMDiff ((I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))).prod 𝓘(ℝ, F))
      (I.prod 𝓘(ℝ, F)) n
      (fun z : (TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) × F =>
        (⟨z.1.proj, z.1.snd.symm z.2⟩ : TotalSpace F V)) := by
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
  let := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := smoothCoframeChartedSpace (F := F) V I n
  let := orthonormalFrameChartedSpace (F := F) V I n
  intro z
  obtain ⟨U, hU, hx, r, hr₀, hr⟩ :=
    LinearIsometryEquiv.exists_contMDiff_coframe (I := I) (n := n) z.1.proj z.1.snd
  let e := smoothCoframeChart V I n U hU r hr
  have he : e ∈ atlas (B × (F ≃ₗᵢ[ℝ] F))
      (TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) := ⟨U, hU, r, hr, rfl⟩
  have heOn := ChartedSpace.contMDiffOn_of_mem_atlas_comp
    (I := I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) he
    (orthonormalFrame_isManifold (F := F) V I n)
  have hc : ContMDiffAt ((I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))).prod 𝓘(ℝ, F))
      (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) n
      (fun y : (TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) × F => e y.1) z :=
    (heOn.contMDiffAt (e.open_source.mem_nhds hx)).comp z contMDiffAt_fst
  have hg := LinearIsometryEquiv.contMDiffAt_iff.mp hc.snd.inv
  have hv := hg.clm_apply contMDiffAt_snd
  have hri : ContMDiffOn (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F)) n
      (fun y : B × F => (⟨y.1, (r y.1).symm y.2⟩ : TotalSpace F V)) (U ×ˢ univ) :=
    ContinuousLinearMap.contMDiffOn_bundle_apply_of_pointwise
      (φ := fun x => (r x).symm.toContinuousLinearEquiv.toContinuousLinearMap) hr
  have h := (hri.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ _⟩)).comp z
    (hc.fst.prodMk hv)
  apply h.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro y
  apply TotalSpace.mk_inj.mpr
  change y.1.snd.symm y.2 = (r y.1.proj).symm
    (((r y.1.proj).symm.trans y.1.snd).symm y.2)
  simp only [LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.symm_apply_apply]

theorem contMDiff_orthonormalFrame_proj [ContMDiffVectorBundle n F V I]
    [IsManifold I n B] :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := orthonormalFrameChartedSpace (F := F) V I n
    ContMDiff (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) I n
      (TotalSpace.proj : (TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) → B) := by
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
  let := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := orthonormalFrameChartedSpace (F := F) V I n
  exact (Bundle.contMDiff_proj V).comp
    ((contMDiff_orthonormalFrame_symm_apply (F := F) V I n).comp
      (contMDiff_id.prodMk (contMDiff_const (c := (0 : F)))))

theorem contMDiff_orthonormalFrame_smul [ContMDiffVectorBundle n F V I]
    [IsManifold I n B] :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := orthonormalFrameChartedSpace (F := F) V I n
    ContMDiff (𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)).prod
      (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))))
      (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) n
      (fun z : (F ≃ₗᵢ[ℝ] F) × (TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) =>
        (⟨z.2.proj, z.1 • z.2.snd⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))) := by
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
  let := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := orthonormalFrameChartedSpace (F := F) V I n
  apply contMDiff_orthonormalFrame_of_symm V I n
  intro w
  have hg : ContMDiff (𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)).prod
      (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))) 𝓘(ℝ, F) n
      (fun z : (F ≃ₗᵢ[ℝ] F) × (TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) =>
        z.1.symm w) :=
    (LinearIsometryEquiv.contMDiff_iff.mp contMDiff_fst.inv).clm_apply contMDiff_const
  exact (contMDiff_orthonormalFrame_symm_apply (F := F) V I n).comp
    (contMDiff_snd.prodMk hg)

theorem contMDiffOn_orthonormalFrame_trivialization [ContMDiffVectorBundle n F V I]
    [IsManifold I n B] {U : Set B} (hU : IsOpen U) {q : ∀ x, V x ≃ₗᵢ[ℝ] F}
    (hq : ∀ w : F, ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
      (fun x => (⟨x, (q x).symm w⟩ : TotalSpace F V)) U) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := orthonormalFrameChartedSpace (F := F) V I n
    ContMDiffOn (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
      (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) n
      (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) =>
        (z.proj, (q z.proj).symm.trans z.snd)) (TotalSpace.proj ⁻¹' U) ∧
    ContMDiffOn (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
      (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) n
      (fun z : B × (F ≃ₗᵢ[ℝ] F) => (⟨z.1, (q z.1).trans z.2⟩ :
        TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))) (U ×ˢ univ) := by
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
  let := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := smoothCoframeChartedSpace (F := F) V I n
  let e := smoothCoframeChart V I n U hU q hq
  have he : e ∈ atlas (B × (F ≃ₗᵢ[ℝ] F))
      (TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) := ⟨U, hU, q, hq, rfl⟩
  exact ⟨ChartedSpace.contMDiffOn_of_mem_atlas_comp
    (I := I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) he
    (orthonormalFrame_isManifold (F := F) V I n),
    ChartedSpace.contMDiffOn_symm_of_mem_atlas_comp
    (I := I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) he
    (orthonormalFrame_isManifold (F := F) V I n)⟩

theorem exists_contMDiff_orthonormalFrame_trivialization [ContMDiffVectorBundle n F V I]
    [IsManifold I n B] (x₀ : B) (p₀ : V x₀ ≃ₗᵢ[ℝ] F) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := orthonormalFrameChartedSpace (F := F) V I n
    ∃ U : Set B, IsOpen U ∧ x₀ ∈ U ∧ ∃ q : ∀ x, V x ≃ₗᵢ[ℝ] F,
      q x₀ = p₀ ∧
      ContMDiffOn (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
        (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) n
        (fun z : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) =>
          (z.proj, (q z.proj).symm.trans z.snd)) (TotalSpace.proj ⁻¹' U) ∧
      ContMDiffOn (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
        (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) n
        (fun z : B × (F ≃ₗᵢ[ℝ] F) => (⟨z.1, (q z.1).trans z.2⟩ :
          TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))) (U ×ˢ univ) := by
  obtain ⟨U, hU, hx, q, hq₀, hq⟩ :=
    LinearIsometryEquiv.exists_contMDiff_coframe (I := I) (n := n) x₀ p₀
  exact ⟨U, hU, hx, q, hq₀, contMDiffOn_orthonormalFrame_trivialization V I n hU hq⟩

end FiberBundle

namespace FiberBundle

variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [ChartedSpace H B]
  (n : ℕ∞ω) [IsContMDiffRiemannianBundle I n F V]
  [ContMDiffVectorBundle n F V I] [IsManifold I n B]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]
  {b : P → B} {q : ∀ z, V (b z) ≃ₗᵢ[ℝ] F}

theorem contMDiffWithinAt_orthonormalFrame_of_symm_of_le {m : ℕ∞ω} (hmn : m ≤ n)
    {s : Set P} {z₀ : P}
    (hq : ∀ w : F, ContMDiffWithinAt IP (I.prod 𝓘(ℝ, F)) m
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) s z₀) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := orthonormalFrameChartedSpace (F := F) V I n
    ContMDiffWithinAt IP (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) m
      (fun z => (⟨b z, q z⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))) s z₀ := by
  let : IsContMDiffRiemannianBundle I m F V := IsContMDiffRiemannianBundle.of_le hmn
  let : ContMDiffVectorBundle m F V I := ContMDiffVectorBundle.of_le hmn
  let : IsManifold I m B := IsManifold.of_le hmn
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
  let := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := orthonormalFrameChartedSpace (F := F) V I n
  have hb : ContMDiffWithinAt IP I m b s z₀ := by
    have h := hq 0
    rw [Bundle.contMDiffWithinAt_totalSpace] at h
    exact h.1
  obtain ⟨U, hU, hx, r, hr₀, hr⟩ :=
    LinearIsometryEquiv.exists_contMDiff_coframe (I := I) (n := n) (b z₀) (q z₀)
  have hi : ContMDiffWithinAt IP 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)) m
      (fun z => (q z).symm.trans (r (b z))) s z₀ := by
    apply LinearIsometryEquiv.contMDiffWithinAt_iff.mpr
    apply contMDiffWithinAt_clm_of_pointwise
    intro w
    have hf := (LinearIsometryEquiv.contMDiffOn_coframe (fun v => (hr v).of_le hmn)).contMDiffAt
      (x := (⟨b z₀, (q z₀).symm w⟩ : TotalSpace F V))
      ((hU.preimage (continuous_proj F V)).mem_nhds hx)
    exact (hf.comp_contMDiffWithinAt z₀ (hq w)).snd
  have hg : ContMDiffWithinAt IP 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)) m
      (fun z => (r (b z)).symm.trans (q z)) s z₀ := by
    simpa only [LinearIsometryEquiv.inv_def, LinearIsometryEquiv.symm_trans,
      LinearIsometryEquiv.symm_symm] using hi.inv
  have hri := (contMDiffOn_orthonormalFrame_trivialization (F := F) V I n hU hr).2.of_le hmn
  have h := (hri.contMDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ _⟩)).comp_contMDiffWithinAt z₀
    (hb.prodMk hg)
  have heq (z : P) : (⟨b z, q z⟩ :
      TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) =
        (⟨b z, (r (b z)).trans ((r (b z)).symm.trans (q z))⟩ :
          TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) := by
    apply TotalSpace.mk_inj.mpr
    ext w
    change q z w = q z ((r (b z)).symm (r (b z) w))
    rw [LinearIsometryEquiv.symm_apply_apply]
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall heq) (heq z₀)

theorem contMDiffAt_orthonormalFrame_of_symm_of_le {m : ℕ∞ω} (hmn : m ≤ n)
    {z₀ : P}
    (hq : ∀ w : F, ContMDiffAt IP (I.prod 𝓘(ℝ, F)) m
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) z₀) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := orthonormalFrameChartedSpace (F := F) V I n
    ContMDiffAt IP (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) m
      (fun z => (⟨b z, q z⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))) z₀ :=
  contMDiffWithinAt_orthonormalFrame_of_symm_of_le V I n hmn hq

theorem contMDiffOn_orthonormalFrame_of_symm_of_le {m : ℕ∞ω} (hmn : m ≤ n)
    {s : Set P}
    (hq : ∀ w : F, ContMDiffOn IP (I.prod 𝓘(ℝ, F)) m
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V)) s) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := orthonormalFrameChartedSpace (F := F) V I n
    ContMDiffOn IP (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) m
      (fun z => (⟨b z, q z⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))) s :=
  fun z hz => contMDiffWithinAt_orthonormalFrame_of_symm_of_le V I n hmn (fun w => hq w z hz)

theorem contMDiff_orthonormalFrame_of_symm_of_le {m : ℕ∞ω} (hmn : m ≤ n)
    (hq : ∀ w : F, ContMDiff IP (I.prod 𝓘(ℝ, F)) m
      (fun z => (⟨b z, (q z).symm w⟩ : TotalSpace F V))) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    letI := orthonormalFrameChartedSpace (F := F) V I n
    ContMDiff IP (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) m
      (fun z => (⟨b z, q z⟩ : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F))) :=
  fun z => contMDiffAt_orthonormalFrame_of_symm_of_le V I n hmn (fun w => hq w z)

theorem contMDiff_id_orthonormalFrameChartedSpace
    (k : ℕ∞ω) [IsContMDiffRiemannianBundle I k F V]
    [ContMDiffVectorBundle k F V I] [IsManifold I k B]
    {m : ℕ∞ω} (hmn : m ≤ n) (hmk : m ≤ k) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    let cn := orthonormalFrameChartedSpace (F := F) V I n
    let ck := orthonormalFrameChartedSpace (F := F) V I k
    @ContMDiff ℝ _ _ _ _ _ _ (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) _ _ cn
      _ _ _ _ _ (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) _ _ ck m id := by
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
  let := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let := orthonormalFrameChartedSpace (F := F) V I n
  have hcol (w : F) : ContMDiff
      (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) (I.prod 𝓘(ℝ, F)) m
      (fun p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F) =>
        (⟨p.proj, p.snd.symm w⟩ : TotalSpace F V)) :=
    ((contMDiff_orthonormalFrame_symm_apply (F := F) V I n).comp
      (contMDiff_id.prodMk (contMDiff_const (c := w)))).of_le hmn
  exact contMDiff_orthonormalFrame_of_symm_of_le V I k hmk hcol

def orthonormalFrameAtlasDiffeomorph
    (k : ℕ∞ω) [IsContMDiffRiemannianBundle I k F V]
    [ContMDiffVectorBundle k F V I] [IsManifold I k B]
    {m : ℕ∞ω} (hmn : m ≤ n) (hmk : m ≤ k) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    let cn := orthonormalFrameChartedSpace (F := F) V I n
    let ck := orthonormalFrameChartedSpace (F := F) V I k
    @Diffeomorph ℝ _ _ _ _ _ _ _ _ _ _ _
      (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
      (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) _ _ cn _ _ ck m := by
  let : IsContinuousRiemannianBundle F V :=
    IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
  let := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
  let cn := orthonormalFrameChartedSpace (F := F) V I n
  let ck := orthonormalFrameChartedSpace (F := F) V I k
  refine @Diffeomorph.mk ℝ _ _ _ _ _ _ _ _ _ _ _
    (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
    (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) _ _ cn _ _ ck m
    (Equiv.refl _) ?_ ?_
  · exact contMDiff_id_orthonormalFrameChartedSpace V I n k hmn hmk
  · exact contMDiff_id_orthonormalFrameChartedSpace V I k n hmk hmn

@[simp]
theorem orthonormalFrameAtlasDiffeomorph_apply
    (k : ℕ∞ω) [IsContMDiffRiemannianBundle I k F V]
    [ContMDiffVectorBundle k F V I] [IsManifold I k B]
    {m : ℕ∞ω} (hmn : m ≤ n) (hmk : m ≤ k)
    (p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) :
    orthonormalFrameAtlasDiffeomorph V I n k hmn hmk p = p := rfl

theorem orthonormalFrameAtlasDiffeomorph_symm_apply
    (k : ℕ∞ω) [IsContMDiffRiemannianBundle I k F V]
    [ContMDiffVectorBundle k F V I] [IsManifold I k B]
    {m : ℕ∞ω} (hmn : m ≤ n) (hmk : m ≤ k)
    (p : TotalSpace (F ≃ₗᵢ[ℝ] F) (fun x => V x ≃ₗᵢ[ℝ] F)) :
    letI : IsContinuousRiemannianBundle F V :=
      IsContMDiffRiemannianBundle.isContinuousRiemannianBundle (I := I) (n := n)
    letI := (orthonormalFramePrebundle (F := F) V).totalSpaceTopology
    let cn := orthonormalFrameChartedSpace (F := F) V I n
    let ck := orthonormalFrameChartedSpace (F := F) V I k
    (@Diffeomorph.symm ℝ _ _ _ _ _ _ _ _ _ _ _
      (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F)))
      (I.prod 𝓘(ℝ, skewAdjoint.submodule ℝ (F →L[ℝ] F))) _ _ cn _ _ ck m
      (orthonormalFrameAtlasDiffeomorph (F := F) V I n k hmn hmk)) p = p := rfl

end FiberBundle
