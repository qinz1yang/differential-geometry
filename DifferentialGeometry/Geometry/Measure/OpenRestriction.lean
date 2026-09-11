import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Evaluation
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section
open Set Manifold MeasureTheory Bundle TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology
namespace DifferentialGeometry.Geometry.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance (U : Opens E) : LocallyCompactSpace U := U.isOpen.locallyCompactSpace

private def openParam (U : Opens E) (x : U) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E U 1 where
  toPartialEquiv := (chartAt E x).symm.toPartialEquiv
  open_source := (chartAt E x).open_target
  open_target := (chartAt E x).open_source
  contMDiffOn_toFun := contMDiffOn_chart_symm
  contMDiffOn_invFun := contMDiffOn_chart

omit [FiniteDimensional ℝ E] in
private theorem openParam_source (U : Opens E) (x : U) : (openParam U x).source = U := by
  change ((OpenPartialHomeomorph.refl E).subtypeRestr (s := U) ⟨x⟩).target = U
  rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_refl,
    Opens.openPartialHomeomorphSubtypeCoe_target]

omit [FiniteDimensional ℝ E] in
private theorem openParam_val (U : Opens E) (x : U) {w : E} (hw : w ∈ U) :
    (openParam U x w).val = w := by
  have ht : w ∈ ((OpenPartialHomeomorph.refl E).subtypeRestr (s := U) ⟨x⟩).target :=
    by change w ∈ (openParam U x).source; rwa [openParam_source]
  exact (OpenPartialHomeomorph.refl E).subtypeRestr_symm_apply ⟨x⟩ ht

omit [FiniteDimensional ℝ E] in
private theorem openParam_mfderiv (U : Opens E) (x : U) {w : E} (hw : w ∈ U) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (openParam U x) w = ContinuousLinearMap.id ℝ E := by
  have hp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (openParam U x) w :=
    (openParam U x).mdifferentiableAt (by norm_num) ((openParam_source U x).symm ▸ hw)
  have he : (Subtype.val ∘ openParam U x : E → E) =ᶠ[𝓝 w] id :=
    Filter.eventuallyEq_of_mem (U.isOpen.mem_nhds hw) (fun y hy => openParam_val U x hy)
  have hd := he.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
  rw [mfderiv_comp w (hasMFDerivAt_subtype_val U _).mdifferentiableAt hp,
    mfderiv_subtype_val, mfderiv_id] at hd
  exact hd

private def identityParam : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E 1 :=
  (Diffeomorph.refl 𝓘(ℝ, E) E 1).toPartialDiffeomorph

private theorem openParam_density (g : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (U : Opens E) (x : U) {w : E} (hw : w ∈ U) :
    paramDensity (g.restrictOpen U) (openParam U x) w = paramDensity g identityParam w := by
  rw [paramDensity_apply, paramDensity_apply]
  congr 2
  ext i j
  simp only [paramGramMatrix_apply, SmoothRiemannianMetric.restrictOpen_inner]
  erw [openParam_mfderiv U x hw, openParam_val U x hw]
  change g.inner w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) =
    g.inner w (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
  rw [mfderiv_id]
  rfl

theorem riemannianVolumeMeasure_restrictOpen_preimage
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) (U : Opens E)
    {K : Set E} (hK : MeasurableSet K) (hKU : K ⊆ U) :
    riemannianVolumeMeasure 𝓘(ℝ, E) U (g.restrictOpen U) (Subtype.val ⁻¹' K) =
      riemannianVolumeMeasure 𝓘(ℝ, E) E g K := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp only [preimage_empty, measure_empty]
  let xU : U := ⟨x, hKU hx⟩
  have himage : (openParam U xU) '' K = Subtype.val ⁻¹' K := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      change (openParam U xU w).val ∈ K
      rwa [openParam_val U xU (hKU hw)]
    · intro hy
      refine ⟨y.val, hy, Subtype.ext ?_⟩
      exact openParam_val U xU y.property
  rw [← himage, riemannianVolumeMeasure_image_param_eq (g.restrictOpen U) (openParam U xU)
    hK (by simpa only [openParam_source] using hKU)]
  have hid := riemannianVolumeMeasure_image_param_eq g (identityParam (E := E)) hK
    (fun _ _ => mem_univ _)
  change riemannianVolumeMeasure 𝓘(ℝ, E) E g (id '' K) = _ at hid
  rw [image_id] at hid
  rw [hid]
  apply setLIntegral_congr_fun hK
  intro w hw
  exact congrArg ENNReal.ofReal (openParam_density g U xU (hKU hw))

end DifferentialGeometry.Geometry.Measure
