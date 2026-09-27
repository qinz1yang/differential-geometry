import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Integration
import DifferentialGeometry.Analysis.Integration.Measure.LocallyInjective
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section

open Set Function Filter MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [T2Space M] [SigmaCompactSpace M] in
private theorem exists_isOpen_injOn_of_paramDensity_ne_zero
    (g : SmoothRiemannianMetric I M) {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) {x : E} (hx : x ∈ U)
    (hJ : paramDensity (I := I) g f x ≠ 0) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ InjOn f W := by
  let y₀ : M := f x
  let S : Set E := U ∩ f ⁻¹' (chartAt H y₀).source
  have hSopen : IsOpen S :=
    hf.continuousOn.isOpen_inter_preimage hU (chartAt H y₀).open_source
  have hxS : x ∈ S := ⟨hx, mem_chart_source H (f x)⟩
  let φ : E → E := fun z => extChartAt I y₀ (f z)
  have hφ : ContDiffOn ℝ 1 φ S := by
    have hchart : ContMDiffOn I 𝓘(ℝ, E) 1 (extChartAt I y₀) (chartAt H y₀).source :=
      contMDiffOn_extChartAt
    exact contMDiffOn_iff_contDiffOn.mp
      (hchart.comp (hf.mono inter_subset_left) fun z hz => hz.2)
  have hφx : ContDiffAt ℝ 1 φ x := hφ.contDiffAt (hSopen.mem_nhds hxS)
  have hmd : MDifferentiableAt 𝓘(ℝ, E) I f x :=
    ((hf x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt one_ne_zero
  have hdet : (fderiv ℝ φ x).det ≠ 0 := by
    intro h0
    apply hJ
    have hy : f x ∈ (trivializationAt E (TangentSpace I) y₀).baseSet := by
      rw [trivializationAt_baseSet_eq_chartAt_source (I := I)]
      exact mem_chart_source H (f x)
    rw [paramDensity_eq_abs_det_mul_chartDensity_of_mdifferentiableAt (I := I) g f hmd y₀ hy]
    change |(fderiv ℝ φ x).det| * _ = 0
    rw [h0, abs_zero, zero_mul]
  let L : E ≃L[ℝ] E := (fderiv ℝ φ x).toContinuousLinearEquivOfDetNeZero hdet
  have hL : HasFDerivAt φ (L : E →L[ℝ] E) x := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hφx.differentiableAt one_ne_zero).hasFDerivAt
  let e := ContDiffAt.toOpenPartialHomeomorph φ hφx hL one_ne_zero
  refine ⟨e.source ∩ S, e.open_source.inter hSopen,
    ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source hφx hL one_ne_zero, hxS⟩, ?_⟩
  intro a ha b hb hab
  apply e.injOn ha.1 hb.1
  change φ a = φ b
  simp only [φ, hab]

private theorem riemannianVolumeMeasure_image_paramDensity_zero
    (g : SmoothRiemannianMetric I M) {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) :
    riemannianVolumeMeasure (I := I) (M := M) g
      (f '' {x | x ∈ U ∧ paramDensity (I := I) g f x = 0}) = 0 := by
  let V : Set E := U ∩ paramDensity (I := I) g f ⁻¹' {0}ᶜ
  have hVopen : IsOpen V :=
    (continuousOn_paramDensity (I := I) g hU hf).isOpen_inter_preimage hU isOpen_compl_singleton
  have _ : LocallyCompactSpace U := hU.locallyCompactSpace
  let L : ℕ → Set E := fun n => Subtype.val '' compactCovering U n
  have hLc : ∀ n, IsCompact (L n) := fun n =>
    (isCompact_compactCovering U n).image continuous_subtype_val
  have hLU : ∀ n, L n ⊆ U := by
    rintro n _ ⟨z, -, rfl⟩
    exact z.2
  have hcover : {x | x ∈ U ∧ paramDensity (I := I) g f x = 0} ⊆ ⋃ n, (L n \ V) := by
    intro x hx
    have hxU : (⟨x, hx.1⟩ : U) ∈ ⋃ n, compactCovering U n := by
      rw [iUnion_compactCovering]
      exact mem_univ _
    obtain ⟨n, hn⟩ := mem_iUnion.mp hxU
    exact mem_iUnion.mpr ⟨n, ⟨_, hn, rfl⟩, fun hxV => hxV.2 hx.2⟩
  refine measure_mono_null ((image_mono hcover).trans image_iUnion.subset)
    (measure_iUnion_null fun n => ?_)
  have hCn : IsCompact (L n \ V) := (hLc n).diff hVopen
  refine le_antisymm ?_ zero_le
  refine (riemannianVolumeMeasure_image_le_of_isCompact (I := I) g hU hCn
    (sdiff_subset.trans (hLU n)) hf).trans (le_of_eq ?_)
  refine (setLIntegral_congr_fun hCn.measurableSet (g := fun _ => 0) fun x hx => ?_).trans
    lintegral_zero
  have h0 : paramDensity (I := I) g f x = 0 := by
    by_contra hne
    exact hx.2 ⟨hLU n hx.1, hne⟩
  simp only [h0, ENNReal.ofReal_zero]

private theorem lintegral_image_le_of_injOn
    (g : SmoothRiemannianMetric I M) {f : E → M} {U P : Set E}
    (hU : IsOpen U) (hP : MeasurableSet P) (hPU : P ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) (hinj : InjOn f P) (φ : M → ℝ≥0∞) :
    ∫⁻ y in f '' P, φ y ∂riemannianVolumeMeasure (I := I) (M := M) g ≤
      ∫⁻ x in P, ENNReal.ofReal (paramDensity (I := I) g f x) * φ (f x)
        ∂(modelHaar (E := E)) := by
  have hJ : AEMeasurable (fun x => ENNReal.ofReal (paramDensity (I := I) g f x))
      ((modelHaar (E := E)).restrict P) :=
    (((continuousOn_paramDensity (I := I) g hU hf).mono hPU).aemeasurable hP).ennreal_ofReal
  rw [← map_withDensity_paramDensity (I := I) g hU hP hPU hf hinj,
    withDensity_congr_ae hJ.ae_eq_mk]
  refine (lintegral_map_le _ _).trans ?_
  refine (lintegral_withDensity_le_lintegral_mul _ hJ.measurable_mk _).trans (le_of_eq ?_)
  refine lintegral_congr_ae ?_
  filter_upwards [hJ.ae_eq_mk] with x hx
  rw [Pi.mul_apply, ← hx]

theorem lintegral_image_le_lintegral_paramDensity_mul
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) (φ : M → ℝ≥0∞) :
    ∫⁻ y in f '' K, φ y ∂riemannianVolumeMeasure (I := I) (M := M) g ≤
      ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := I) g f x) * φ (f x)
        ∂(modelHaar (E := E)) := by
  let V : Set E := U ∩ paramDensity (I := I) g f ⁻¹' {0}ᶜ
  have hVopen : IsOpen V :=
    (continuousOn_paramDensity (I := I) g hU hf).isOpen_inter_preimage hU isOpen_compl_singleton
  have hR : MeasurableSet (K ∩ V) := hK.inter hVopen.measurableSet
  have hloc : IsLocallyInjective ((K ∩ V).domRestrict f) := by
    intro x
    obtain ⟨W, hW, hxW, hinj⟩ :=
      exists_isOpen_injOn_of_paramDensity_ne_zero (I := I) g hU hf x.2.2.1 x.2.2.2
    exact ⟨Subtype.val ⁻¹' W, hW.preimage continuous_subtype_val, hxW,
      fun a ha b hb hab => Subtype.ext (hinj ha hb hab)⟩
  obtain ⟨P, hPmeas, hPdisj, hPcover, hPinj⟩ := hR.exists_partition_injOn hloc
  have hPK : ∀ n, P n ⊆ K := fun n =>
    (subset_iUnion P n).trans (hPcover.symm ▸ inter_subset_left)
  have hnull : riemannianVolumeMeasure (I := I) (M := M) g (f '' (K \ V)) = 0 := by
    have hsub : K \ V ⊆ {x | x ∈ U ∧ paramDensity (I := I) g f x = 0} := by
      intro x hx
      refine ⟨hKU hx.1, ?_⟩
      by_contra hne
      exact hx.2 ⟨hKU hx.1, hne⟩
    exact measure_mono_null (image_mono hsub)
      (riemannianVolumeMeasure_image_paramDensity_zero (I := I) g hU hf)
  calc
    ∫⁻ y in f '' K, φ y ∂riemannianVolumeMeasure (I := I) (M := M) g =
        ∫⁻ y in f '' (K \ V) ∪ ⋃ n, f '' P n, φ y
          ∂riemannianVolumeMeasure (I := I) (M := M) g := by
      rw [← image_iUnion, hPcover, ← image_union, sdiff_union_inter]
    _ ≤ ∫⁻ y in f '' (K \ V), φ y ∂riemannianVolumeMeasure (I := I) (M := M) g +
        ∫⁻ y in ⋃ n, f '' P n, φ y ∂riemannianVolumeMeasure (I := I) (M := M) g :=
      lintegral_union_le _ _ _
    _ = ∫⁻ y in ⋃ n, f '' P n, φ y ∂riemannianVolumeMeasure (I := I) (M := M) g := by
      rw [setLIntegral_measure_zero _ _ hnull, zero_add]
    _ ≤ ∑' n, ∫⁻ y in f '' P n, φ y ∂riemannianVolumeMeasure (I := I) (M := M) g :=
      lintegral_iUnion_le _ _
    _ ≤ ∑' n, ∫⁻ x in P n, ENNReal.ofReal (paramDensity (I := I) g f x) * φ (f x)
        ∂(modelHaar (E := E)) :=
      ENNReal.tsum_le_tsum fun n =>
        lintegral_image_le_of_injOn (I := I) g hU (hPmeas n) ((hPK n).trans hKU) hf
          (hPinj n) φ
    _ = ∫⁻ x in ⋃ n, P n, ENNReal.ofReal (paramDensity (I := I) g f x) * φ (f x)
        ∂(modelHaar (E := E)) :=
      (lintegral_iUnion hPmeas hPdisj _).symm
    _ ≤ ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := I) g f x) * φ (f x)
        ∂(modelHaar (E := E)) :=
      lintegral_mono_set (iUnion_subset hPK)

theorem lintegral_image_le_lintegral_paramDensity_mul_of_le
    (g : SmoothRiemannianMetric I M) {f : E → M} {U K : Set E}
    (hU : IsOpen U) (hK : MeasurableSet K) (hKU : K ⊆ U)
    (hf : ContMDiffOn 𝓘(ℝ, E) I 1 f U) (h : E → ℝ≥0∞) (φ : M → ℝ≥0∞)
    (hφ : ∀ x ∈ K, φ (f x) ≤ h x) :
    ∫⁻ y in f '' K, φ y ∂riemannianVolumeMeasure (I := I) (M := M) g ≤
      ∫⁻ x in K, ENNReal.ofReal (paramDensity (I := I) g f x) * h x
        ∂(modelHaar (E := E)) :=
  (lintegral_image_le_lintegral_paramDensity_mul (I := I) g hU hK hKU hf φ).trans
    (setLIntegral_mono' hK fun x hx => by gcongr; exact hφ x hx)

end DifferentialGeometry.Integral.Measure
