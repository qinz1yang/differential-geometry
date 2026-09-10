import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false
noncomputable section
open Set Filter Function MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff Topology
namespace Poincare.Morse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I 1 M]
  {f : M → E}


theorem addHaar_critical_image_chart_eq_zero (μ : Measure E) [IsAddHaarMeasure μ]
    (hf : MDifferentiable I 𝓘(ℝ, E) f) (x : M) :
    μ (f '' {y : M | y ∈ (extChartAt I x).source ∧
      ¬ Surjective (mfderiv I 𝓘(ℝ, E) f y)}) = 0 := by
  let c := extChartAt I x
  let s := {z : E | z ∈ c.target ∧ ¬ Surjective (mfderiv I 𝓘(ℝ, E) f (c.symm z))}
  let d : E → E →L[ℝ] E := fun z : E => (mfderiv I 𝓘(ℝ, E) f (c.symm z)).comp
    (mfderiv 𝓘(ℝ, E) I c.symm z)
  have hd (z : E) (hz : z ∈ s) : HasFDerivAt (f ∘ c.symm) (d z) z := by
    have hc : MDifferentiableAt 𝓘(ℝ, E) I c.symm z :=
      ((contMDiffOn_extChartAt_symm (I := I) (n := 1) x).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds hz.1)).mdifferentiableAt one_ne_zero
    exact hasMFDerivAt_iff_hasFDerivAt.mp ((hf _).hasMFDerivAt.comp z hc.hasMFDerivAt)
  have hz (z : E) (hz : z ∈ s) : (d z).det = 0 := by
    rw [LinearMap.det_eq_zero_iff_ker_ne_bot]
    intro hk
    have hi : Injective (d z) := LinearMap.ker_eq_bot.mp hk
    have hh : Surjective (d z) := (d z).toLinearMap.injective_iff_surjective.mp hi
    apply hz.2
    exact Surjective.of_comp (show Surjective ((mfderiv I 𝓘(ℝ, E) f (c.symm z)) ∘
      (mfderiv 𝓘(ℝ, E) I c.symm z)) from hh)
  have hnull := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := μ)
    (fun z hz => (hd z hz).hasFDerivWithinAt) hz
  have himage : (f ∘ c.symm) '' s = f '' {y : M | y ∈ c.source ∧
      ¬ Surjective (mfderiv I 𝓘(ℝ, E) f y)} := by
    ext v
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨c.symm z, ⟨c.map_target hz.1,hz.2⟩,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      refine ⟨c y, ⟨c.map_source hy.1, ?_⟩, ?_⟩
      · change ¬ Surjective (show E →L[ℝ] E from mfderiv I 𝓘(ℝ, E) f (c.symm (c y)))
        rw [c.left_inv hy.1]
        exact hy.2
      · simp only [comp_apply,c.left_inv hy.1]
  rwa [himage] at hnull


theorem addHaar_critical_image_eq_zero [SecondCountableTopology M]
    (μ : Measure E) [IsAddHaarMeasure μ] (hf : MDifferentiable I 𝓘(ℝ, E) f) :
    μ (f '' {y : M | ¬ Surjective (mfderiv I 𝓘(ℝ, E) f y)}) = 0 := by
  obtain ⟨t,ht,hcover⟩ := TopologicalSpace.countable_cover_nhds
    (fun x : M => extChartAt_source_mem_nhds (I := I) x)
  have hnull : ∀ x ∈ t, μ (f '' {y : M | y ∈ (extChartAt I x).source ∧
      ¬ Surjective (mfderiv I 𝓘(ℝ, E) f y)}) = 0 :=
    fun x _ => addHaar_critical_image_chart_eq_zero μ hf x
  apply measure_mono_null (t := ⋃ x ∈ t, f '' {y : M | y ∈ (extChartAt I x).source ∧
    ¬ Surjective (mfderiv I 𝓘(ℝ, E) f y)}) _ ((measure_biUnion_null_iff ht).mpr hnull)
  rintro z ⟨y,hy,rfl⟩
  have hycover : y ∈ ⋃ x ∈ t, (extChartAt I x).source := hcover ▸ mem_univ y
  rcases mem_iUnion₂.mp hycover with ⟨x,hxt,hyx⟩
  exact mem_iUnion₂.mpr ⟨x,hxt,⟨y,⟨hyx,hy⟩,rfl⟩⟩


theorem ae_regular_values [SecondCountableTopology M]
    (μ : Measure E) [IsAddHaarMeasure μ] (hf : MDifferentiable I 𝓘(ℝ, E) f) :
    ∀ᵐ z ∂μ, ∀ x : M, f x = z → Surjective (mfderiv I 𝓘(ℝ, E) f x) := by
  have h := (measure_eq_zero_iff_ae_notMem).mp (addHaar_critical_image_eq_zero μ hf)
  filter_upwards [h] with z hz x hx
  by_contra hc
  exact hz ⟨x,hc,hx⟩

end Poincare.Morse
