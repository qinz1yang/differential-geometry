import DifferentialGeometry.Analysis.InnerProductSpace.Cayley
import DifferentialGeometry.Geometry.Metric.OrthonormalFrame.Topology
import Mathlib.Geometry.Manifold.Algebra.LieGroup

noncomputable section

open Set
open scoped Topology ContDiff Manifold

namespace LinearIsometryEquiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem isOpen_isUnit_one_add :
    IsOpen {p : E ≃ₗᵢ[ℝ] E | IsUnit (1 + (p : E →L[ℝ] E))} :=
  (Units.isOpen (R := E →L[ℝ] E)).preimage
    ((continuous_const (y := (1 : E →L[ℝ] E))).add
      (continuous_toContinuousLinearMap (k := ℝ) (E := E) (F := E)))

end LinearIsometryEquiv

namespace skewAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def cayleyHomeomorph : skewAdjoint.submodule ℝ (E →L[ℝ] E) ≃ₜ
    {p : E ≃ₗᵢ[ℝ] E | IsUnit (1 + (p : E →L[ℝ] E))} where
  toEquiv := cayleyEquiv
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply LinearIsometryEquiv.continuous_iff.mpr
    exact (contDiff_cayleyTransform_toContinuousLinearMap (n := 0)).continuous
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    change Continuous (fun p : {p : E ≃ₗᵢ[ℝ] E | IsUnit (1 + (p : E →L[ℝ] E))} =>
      (p.1.inverseCayleyTransform p.2 : E →L[ℝ] E))
    simp only [LinearIsometryEquiv.inverseCayleyTransform_toContinuousLinearMap]
    apply continuous_iff_continuousAt.mpr
    intro p
    have hf : Continuous (fun q : {p : E ≃ₗᵢ[ℝ] E | IsUnit (1 + (p : E →L[ℝ] E))} =>
        (q.1 : E →L[ℝ] E)) :=
      LinearIsometryEquiv.continuous_toContinuousLinearMap.comp continuous_subtype_val
    have hi : ContinuousAt Ring.inverse (1 + (p.1 : E →L[ℝ] E)) := by
      simpa only [p.2.unit_spec] using
        (contDiffAt_ringInverse ℝ (n := 0) p.2.unit).continuousAt
    have hplus : ContinuousAt
        (fun q : {p : E ≃ₗᵢ[ℝ] E | IsUnit (1 + (p : E →L[ℝ] E))} =>
          1 + (q.1 : E →L[ℝ] E)) p := (continuous_const.add hf).continuousAt
    have hminus : ContinuousAt
        (fun q : {p : E ≃ₗᵢ[ℝ] E | IsUnit (1 + (p : E →L[ℝ] E))} =>
          1 - (q.1 : E →L[ℝ] E)) p := (continuous_const.sub hf).continuousAt
    exact hminus.mul (ContinuousAt.comp
      (f := fun q : {p : E ≃ₗᵢ[ℝ] E | IsUnit (1 + (p : E →L[ℝ] E))} =>
        1 + (q.1 : E →L[ℝ] E)) hi hplus)

@[simp]
theorem cayleyHomeomorph_apply (K : skewAdjoint.submodule ℝ (E →L[ℝ] E)) :
    ((cayleyHomeomorph K).1 : E ≃ₗᵢ[ℝ] E) = cayleyTransform K := rfl

@[simp]
theorem cayleyHomeomorph_symm_apply
    (p : {p : E ≃ₗᵢ[ℝ] E | IsUnit (1 + (p : E →L[ℝ] E))}) :
    cayleyHomeomorph.symm p = p.1.inverseCayleyTransform p.2 := rfl

end skewAdjoint

namespace LinearIsometryEquiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def cayleyChart : OpenPartialHomeomorph (E ≃ₗᵢ[ℝ] E)
    (skewAdjoint.submodule ℝ (E →L[ℝ] E)) :=
  let U : TopologicalSpace.Opens (E ≃ₗᵢ[ℝ] E) :=
    ⟨{p | IsUnit (1 + (p : E →L[ℝ] E))}, isOpen_isUnit_one_add⟩
  let hU : Nonempty U := ⟨⟨skewAdjoint.cayleyTransform 0,
    skewAdjoint.isUnit_one_add_cayleyTransform 0⟩⟩
  (U.openPartialHomeomorphSubtypeCoe hU).symm.trans
    skewAdjoint.cayleyHomeomorph.symm.toOpenPartialHomeomorph

@[simp]
theorem cayleyChart_source : (cayleyChart (E := E)).source =
    {p : E ≃ₗᵢ[ℝ] E | IsUnit (1 + (p : E →L[ℝ] E))} := by
  simp [cayleyChart]

@[simp]
theorem cayleyChart_target : (cayleyChart (E := E)).target = univ := by
  simp [cayleyChart]

@[simp]
theorem cayleyChart_symm_apply (K : skewAdjoint.submodule ℝ (E →L[ℝ] E)) :
    cayleyChart.symm K = skewAdjoint.cayleyTransform K := rfl

theorem cayleyChart_apply (p : E ≃ₗᵢ[ℝ] E) (hp : IsUnit (1 + (p : E →L[ℝ] E))) :
    cayleyChart p = p.inverseCayleyTransform hp := by
  have h : cayleyChart (cayleyChart.symm (p.inverseCayleyTransform hp)) =
      p.inverseCayleyTransform hp :=
    cayleyChart.right_inv (by rw [cayleyChart_target]; exact mem_univ _)
  change cayleyChart (skewAdjoint.cayleyTransform (p.inverseCayleyTransform hp)) = _ at h
  rwa [cayleyTransform_inverseCayleyTransform] at h

def cayleyChartAt (p : E ≃ₗᵢ[ℝ] E) :
    OpenPartialHomeomorph (E ≃ₗᵢ[ℝ] E) (skewAdjoint.submodule ℝ (E →L[ℝ] E)) :=
  (Homeomorph.mulLeft p⁻¹).toOpenPartialHomeomorph.trans cayleyChart

@[simp]
theorem cayleyChartAt_source (p : E ≃ₗᵢ[ℝ] E) :
    (cayleyChartAt p).source = {q | IsUnit (1 + ((p⁻¹ * q : E ≃ₗᵢ[ℝ] E) : E →L[ℝ] E))} := by
  simp [cayleyChartAt]

@[simp]
theorem cayleyChartAt_target (p : E ≃ₗᵢ[ℝ] E) : (cayleyChartAt p).target = univ := by
  simp [cayleyChartAt]

theorem mem_cayleyChartAt_source (p : E ≃ₗᵢ[ℝ] E) : p ∈ (cayleyChartAt p).source := by
  rw [cayleyChartAt_source]
  change IsUnit (1 + ((p⁻¹ * p : E ≃ₗᵢ[ℝ] E) : E →L[ℝ] E))
  rw [inv_mul_cancel]
  change IsUnit (1 + ContinuousLinearMap.id ℝ E)
  simpa using skewAdjoint.isUnit_one_add_cayleyTransform (0 : skewAdjoint (E →L[ℝ] E))

instance instChartedSpace : ChartedSpace (skewAdjoint.submodule ℝ (E →L[ℝ] E)) (E ≃ₗᵢ[ℝ] E) where
  atlas := range cayleyChartAt
  chartAt := cayleyChartAt
  mem_chart_source := mem_cayleyChartAt_source
  chart_mem_atlas p := ⟨p, rfl⟩

private def skewAdjointPartCLM : (E →L[ℝ] E) →L[ℝ]
    skewAdjoint.submodule ℝ (E →L[ℝ] E) where
  __ := skewAdjointPart ℝ
  cont := by
    apply continuous_induced_rng.mpr
    exact (continuous_id.sub continuous_star).const_smul (⅟ (2 : ℝ))

private theorem skewAdjointPartCLM_apply (K : skewAdjoint.submodule ℝ (E →L[ℝ] E)) :
    skewAdjointPartCLM (K : E →L[ℝ] E) = K :=
  LinearMap.congr_fun (skewAdjointPart_comp_subtype_skewAdjoint (R := ℝ) (A := E →L[ℝ] E)) K

private theorem cayleyChart_eq_skewAdjointPart (p : E ≃ₗᵢ[ℝ] E)
    (hp : IsUnit (1 + (p : E →L[ℝ] E))) :
    cayleyChart p = skewAdjointPartCLM ((1 - (p : E →L[ℝ] E)) *
      Ring.inverse (1 + (p : E →L[ℝ] E))) := by
  rw [cayleyChart_apply p hp, ← inverseCayleyTransform_toContinuousLinearMap p hp]
  exact (skewAdjointPartCLM_apply (show skewAdjoint.submodule ℝ (E →L[ℝ] E) from
    p.inverseCayleyTransform hp)).symm

private theorem contDiffWithinAt_cayleyChart_comp {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {f : X → E ≃ₗᵢ[ℝ] E} {s : Set X} {x : X} {n : ℕ∞ω}
    (hf : ContDiffWithinAt ℝ n (fun y => (f y : E →L[ℝ] E)) s x)
    (hx : IsUnit (1 + (f x : E →L[ℝ] E))) :
    ContDiffWithinAt ℝ n (fun y => cayleyChart (f y)) s x := by
  have hi : ContDiffAt ℝ n Ring.inverse (1 + (f x : E →L[ℝ] E)) := by
    simpa only [hx.unit_spec] using (contDiffAt_ringInverse ℝ (n := n) hx.unit)
  have hr : ContDiffWithinAt ℝ n (fun y => (1 - (f y : E →L[ℝ] E)) *
      Ring.inverse (1 + (f y : E →L[ℝ] E))) s x :=
    (contDiffWithinAt_const.sub hf).mul
      (hi.comp_contDiffWithinAt (f := fun y => 1 + (f y : E →L[ℝ] E)) x
        (contDiffWithinAt_const.add hf))
  have hp : ContDiff ℝ n (skewAdjointPartCLM (E := E)) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := E →L[ℝ] E)
      (F := skewAdjoint.submodule ℝ (E →L[ℝ] E)) skewAdjointPartCLM
  have h : ContDiffWithinAt ℝ n (fun y => skewAdjointPartCLM
      ((1 - (f y : E →L[ℝ] E)) * Ring.inverse (1 + (f y : E →L[ℝ] E)))) s x :=
    hp.contDiffAt.comp_contDiffWithinAt x hr
  apply h.congr_of_eventuallyEq _ (cayleyChart_eq_skewAdjointPart (f x) hx)
  have hc : ContinuousWithinAt f s x :=
    isEmbedding_toContinuousLinearMap.isInducing.continuousWithinAt_iff.mpr hf.continuousWithinAt
  filter_upwards [hc (isOpen_isUnit_one_add.mem_nhds hx)] with y hy
  exact cayleyChart_eq_skewAdjointPart (f y) hy

@[simp]
theorem cayleyChartAt_apply (p q : E ≃ₗᵢ[ℝ] E) :
    cayleyChartAt p q = cayleyChart (p⁻¹ * q) := rfl

@[simp]
theorem cayleyChartAt_symm_apply (p : E ≃ₗᵢ[ℝ] E)
    (K : skewAdjoint.submodule ℝ (E →L[ℝ] E)) :
    (cayleyChartAt p).symm K = p * skewAdjoint.cayleyTransform K := by
  change p⁻¹⁻¹ * skewAdjoint.cayleyTransform K = _
  rw [inv_inv]

theorem contDiff_cayleyChartAt_symm_toContinuousLinearMap (p : E ≃ₗᵢ[ℝ] E) {n : ℕ∞ω} :
    ContDiff ℝ n (fun K : skewAdjoint.submodule ℝ (E →L[ℝ] E) =>
      ((cayleyChartAt p).symm K : E →L[ℝ] E)) := by
  simp only [cayleyChartAt_symm_apply]
  change ContDiff ℝ n (fun K : skewAdjoint.submodule ℝ (E →L[ℝ] E) =>
    (p : E →L[ℝ] E) * (skewAdjoint.cayleyTransform K : E →L[ℝ] E))
  exact contDiff_const.mul
    (skewAdjoint.contDiff_cayleyTransform_toContinuousLinearMap (E := E))

instance instIsManifold {n : ℕ∞ω} :
    IsManifold 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E)) n (E ≃ₗᵢ[ℝ] E) := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, preimage_id, range_id, inter_univ]
  intro K hK
  change ContDiffWithinAt ℝ n (fun L => cayleyChart (q⁻¹ * (cayleyChartAt p).symm L)) _ K
  apply contDiffWithinAt_cayleyChart_comp
  · change ContDiffWithinAt ℝ n (fun L =>
        ((q⁻¹ : E ≃ₗᵢ[ℝ] E) : E →L[ℝ] E) *
          ((cayleyChartAt p).symm L : E →L[ℝ] E)) _ K
    exact contDiffWithinAt_const.mul
      (contDiff_cayleyChartAt_symm_toContinuousLinearMap p).contDiffWithinAt
  · simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage, cayleyChartAt_source,
      mem_ofPred_eq] using hK.2

theorem contMDiff_toContinuousLinearMap {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E)) 𝓘(ℝ, E →L[ℝ] E) n
      (fun p : E ≃ₗᵢ[ℝ] E => (p : E →L[ℝ] E)) := by
  intro p
  rw [_root_.contMDiffAt_iff]
  refine ⟨continuous_toContinuousLinearMap.continuousAt, ?_⟩
  rw [ModelWithCorners.range_eq_univ]
  change ContDiffWithinAt ℝ n (fun K : skewAdjoint.submodule ℝ (E →L[ℝ] E) =>
    ((cayleyChartAt p).symm K : E →L[ℝ] E)) univ _
  exact (contDiff_cayleyChartAt_symm_toContinuousLinearMap p).contDiffWithinAt

section Maps

variable {X H M : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {I : ModelWithCorners ℝ X H}
  [TopologicalSpace M] [ChartedSpace H M] {f : M → E ≃ₗᵢ[ℝ] E}
  {s : Set M} {x : M} {n : ℕ∞ω}

theorem contMDiffWithinAt_iff :
    ContMDiffWithinAt I 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E)) n f s x ↔
      ContMDiffWithinAt I 𝓘(ℝ, E →L[ℝ] E) n (fun y => (f y : E →L[ℝ] E)) s x := by
  constructor
  · intro hf
    exact contMDiff_toContinuousLinearMap.contMDiffAt.comp_contMDiffWithinAt x hf
  · intro hf
    rw [_root_.contMDiffWithinAt_iff] at hf ⊢
    refine ⟨isEmbedding_toContinuousLinearMap.isInducing.continuousWithinAt_iff.mpr hf.1, ?_⟩
    change ContDiffWithinAt ℝ n
      (fun y => cayleyChart ((f x)⁻¹ * f ((extChartAt I x).symm y))) _ _
    apply contDiffWithinAt_cayleyChart_comp
    · change ContDiffWithinAt ℝ n
        (fun y => (((f x)⁻¹ : E ≃ₗᵢ[ℝ] E) : E →L[ℝ] E) *
          (f ((extChartAt I x).symm y) : E →L[ℝ] E)) _ _
      exact contDiffWithinAt_const.mul hf.2
    · simpa only [extChartAt_to_inv, cayleyChartAt_source, mem_ofPred_eq] using
        mem_cayleyChartAt_source (f x)

theorem contMDiffAt_iff :
    ContMDiffAt I 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E)) n f x ↔
      ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) n (fun y => (f y : E →L[ℝ] E)) x :=
  contMDiffWithinAt_iff

theorem contMDiffOn_iff :
    ContMDiffOn I 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E)) n f s ↔
      ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) n (fun y => (f y : E →L[ℝ] E)) s :=
  forall₂_congr fun _ _ => contMDiffWithinAt_iff

theorem contMDiff_iff :
    ContMDiff I 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E)) n f ↔
      ContMDiff I 𝓘(ℝ, E →L[ℝ] E) n (fun y => (f y : E →L[ℝ] E)) :=
  forall_congr' fun _ => contMDiffAt_iff

end Maps

instance instLieGroup {n : ℕ∞ω} :
    LieGroup 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E)) n (E ≃ₗᵢ[ℝ] E) where
  contMDiff_mul := by
    apply contMDiff_iff.mpr
    change ContMDiff _ _ n (fun p : (E ≃ₗᵢ[ℝ] E) × (E ≃ₗᵢ[ℝ] E) =>
      (p.1 : E →L[ℝ] E) * (p.2 : E →L[ℝ] E))
    exact (contMDiff_toContinuousLinearMap.comp contMDiff_fst).clm_comp
      (contMDiff_toContinuousLinearMap.comp contMDiff_snd)
  contMDiff_inv := by
    apply contMDiff_iff.mpr
    let A : (E →L[ℝ] E) →L[ℝ] E →L[ℝ] E :=
      ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
    have h : ContMDiff 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E)) 𝓘(ℝ, E →L[ℝ] E) n
        (fun p : E ≃ₗᵢ[ℝ] E => A (p : E →L[ℝ] E)) :=
      A.contMDiff.comp contMDiff_toContinuousLinearMap
    exact h.congr fun p => p.adjoint_eq_symm.symm

end LinearIsometryEquiv

namespace skewAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem contMDiff_cayleyTransform {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E))
      𝓘(ℝ, skewAdjoint.submodule ℝ (E →L[ℝ] E)) n
      (fun K : skewAdjoint.submodule ℝ (E →L[ℝ] E) => cayleyTransform K) :=
  LinearIsometryEquiv.contMDiff_iff.mpr
    contDiff_cayleyTransform_toContinuousLinearMap.contMDiff

end skewAdjoint
