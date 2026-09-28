import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Lipschitz









noncomputable section

open MeasureTheory Set Filter
open scoped NNReal Topology ENNReal MeasureTheory

theorem LocallyLipschitzOn.addHaar_image_eq_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    {μ : Measure E} [μ.IsAddHaarMeasure] {ν : Measure F} [ν.IsAddHaarMeasure]
    {f : E → F} {s : Set E} (hf : LocallyLipschitzOn s f)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F) (hs : μ s = 0) : ν (f '' s) = 0 := by
  let H : Measure E := Measure.hausdorffMeasure (Module.finrank ℝ E)
  let J : Measure F := Measure.hausdorffMeasure (Module.finrank ℝ F)
  have hH : H s = 0 := (Measure.absolutelyContinuous_isAddHaarMeasure H μ) hs
  have hlocal (x : s) : ∃ V : Set E, IsOpen V ∧ x.1 ∈ V ∧ ν (f '' (V ∩ s)) = 0 := by
    obtain ⟨K, T, hT, hK⟩ := hf x.2
    obtain ⟨W, hW, hWT⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hT
    obtain ⟨V, hVW, hV, hxV⟩ := mem_nhds_iff.mp hW
    have hLip : LipschitzOnWith K f (V ∩ s) :=
      hK.mono (fun y hy => hWT ⟨hVW hy.1, hy.2⟩)
    refine ⟨V, hV, hxV, ?_⟩
    apply Measure.absolutelyContinuous_isAddHaarMeasure ν J
    have hz : H (V ∩ s) = 0 := measure_mono_null inter_subset_right hH
    have hle := hLip.hausdorffMeasure_image_le (d := (Module.finrank ℝ E : ℝ)) (by positivity)
    change Measure.hausdorffMeasure (Module.finrank ℝ E) (f '' (V ∩ s)) ≤
      (K : ℝ≥0∞) ^ (Module.finrank ℝ E : ℝ) * H (V ∩ s) at hle
    rw [hz, mul_zero, hdim] at hle
    exact le_zero_iff.mp hle
  choose V hV hxV hnull using hlocal
  obtain ⟨S, hS, hcover⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_countable_subcover
    V hV (fun x hx => mem_iUnion_of_mem ⟨x, hx⟩ (hxV ⟨x, hx⟩))
  have hsub : f '' s ⊆ ⋃ x ∈ S, f '' (V x ∩ s) := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hxV⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion₂.mpr ⟨z, hz, x, ⟨hxV, hx⟩, rfl⟩
  exact measure_mono_null hsub ((measure_biUnion_null_iff hS).mpr (fun x _ => hnull x))

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]



theorem volume_image_eq_zero_of_lipschitz {f : E → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) {s : Set E} (hs : volume s = 0) :
    volume (f '' s) = 0 := by
  exact hf.locallyLipschitz.locallyLipschitzOn.addHaar_image_eq_zero rfl hs

theorem ae_comp_of_lipschitz_leftInverse_on {f k : E → E} {K : ℝ≥0}
    (hk : LipschitzWith K k) {s : Set E} (hki : ∀ x ∈ s, k (f x) = x)
    {P : E → Prop} (hP : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ x ∂volume, x ∈ s → P (f x) := by
  have hz := volume_image_eq_zero_of_lipschitz hk (ae_iff.mp hP)
  have ha : ∀ᵐ x ∂volume, x ∉ k '' {y | ¬ P y} := by
    apply ae_iff.mpr
    convert hz using 1
    congr 1
    ext x
    simp
  filter_upwards [ha] with x hx
  intro hxs
  by_contra hp
  exact hx ⟨f x, hp, hki x hxs⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem integral_image_eq_integral_abs_det_of_lipschitz {f : E → E} {K : ℝ≥0}
    (hf : LipschitzWith K f) {s : Set E} (hs : MeasurableSet s) (hi : InjOn f s)
    (g : E → F) :
    ∫ x in f '' s, g x =
      ∫ x in s, |(fderiv ℝ f x).toLinearMap.det| • g (f x) := by
  let t : Set E := s ∩ {x | DifferentiableAt ℝ f x}
  have ht : MeasurableSet t := hs.inter (measurableSet_of_differentiableAt ℝ f)
  have hts : t =ᵐ[volume] s := by
    filter_upwards [hf.ae_differentiableAt (μ := volume)] with x hx
    apply propext
    change (x ∈ s ∧ DifferentiableAt ℝ f x) ↔ x ∈ s
    exact and_iff_left hx
  have hnull : volume (s \ t) = 0 := by
    apply measure_mono_null (show s \ t ⊆ {x | ¬ DifferentiableAt ℝ f x} from
      fun x hx hd => hx.2 ⟨hx.1, hd⟩)
    exact ae_iff.mp (hf.ae_differentiableAt (μ := volume))
  have himage : f '' t =ᵐ[volume] f '' s := by
    have hz := volume_image_eq_zero_of_lipschitz hf hnull
    have he : volume (f '' s \ f '' t) = 0 := measure_mono_null
      (by
        rintro x ⟨⟨y, hy, rfl⟩, hxt⟩
        exact ⟨y, ⟨hy, fun hyt => hxt ⟨y, hyt, rfl⟩⟩, rfl⟩) hz
    have ha : ∀ᵐ x ∂volume, x ∉ f '' s \ f '' t := by
      apply ae_iff.mpr
      convert he using 1
      congr 1
      ext x
      simp only [mem_ofPred_eq, not_not]
    filter_upwards [ha] with x hx
    apply propext
    exact ⟨fun hxt => image_mono (show t ⊆ s from inter_subset_left) hxt, fun hxs =>
      not_not.mp (fun hxt => hx ⟨hxs, hxt⟩)⟩
  rw [← setIntegral_congr_set himage, ← setIntegral_congr_set hts]
  exact integral_image_eq_integral_abs_det_fderiv_smul volume ht
    (fun x hx => hx.2.hasFDerivAt.hasFDerivWithinAt) (hi.mono inter_subset_left) g

end DifferentialGeometry.Analysis
