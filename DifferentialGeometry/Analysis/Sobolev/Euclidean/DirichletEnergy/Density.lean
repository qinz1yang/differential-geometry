import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Integrability
import DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace DifferentialGeometry.Analysis

variable {ι : Type*} [Fintype ι]

def weakMapMetricDensity
    {Ω : Set (EuclideanSpace ℝ (Fin 2))}
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι}
    (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ∑ j : Fin 2, A (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
    (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))

omit [Fintype ι] in
theorem integrable_weakMapMetricDensity [Finite ι]
    {Ω S : Set (EuclideanSpace ℝ (Fin 2))} (hSΩ : S ⊆ Ω)
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K)
    (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : ContinuousOn A K) (hfK : ∀ᵐ x ∂volume.restrict S, f x ∈ K) :
    IntegrableOn (weakMapMetricDensity A hf) S := by
  classical
  let _ := Fintype.ofFinite ι
  have hfm : AEStronglyMeasurable f (volume.restrict S) :=
    ((MemLp.of_eval_piLp fun i => (hf i).memLp).mono_measure
      (Measure.restrict_mono_set volume hSΩ)).aestronglyMeasurable
  have hm : Measurable (K.piecewise A 0) :=
    hA.measurable_piecewise continuous_zero.continuousOn hK.measurableSet
  have hAm : AEStronglyMeasurable (fun x => A (f x)) (volume.restrict S) := by
    apply (hm.comp_aemeasurable hfm.aemeasurable).aestronglyMeasurable.congr
    exact hfK.mono fun x hx => Set.piecewise_eq_of_mem K A 0 hx
  have hc : ContinuousOn (fun y => ‖A y‖) K :=
    (@continuous_norm (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
      inferInstance).comp_continuousOn hA
  obtain ⟨C, hC⟩ := hK.bddAbove_image hc
  have hb : ∀ᵐ x ∂volume.restrict S, ‖A (f x)‖ ≤ C :=
    hfK.mono fun x hx => hC (mem_image_of_mem _ hx)
  apply integrable_finsetSum
  intro j hj
  have hG : MemLp (fun x =>
      (WithLp.toLp 2 (fun i => (hf i).weakGrad x j) : EuclideanSpace ℝ ι)) 2
      (volume.restrict S) := MemLp.of_eval_piLp fun i =>
    ((hf i).weakGrad_component_memLp j).mono_measure (Measure.restrict_mono_set volume hSΩ)
  exact integrable_bilinear_of_apply_aestronglyMeasurable (fun x => A (f x))
    (fun v w => (hAm.apply_continuousLinearMap v).apply_continuousLinearMap w) hb hG hG

omit [Fintype ι] in
theorem weakMapMetricDensity_integral_eq_sum [Finite ι]
    {Ω S : Set (EuclideanSpace ℝ (Fin 2))} (hSΩ : S ⊆ Ω)
    {f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) Ω)
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K)
    (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : ContinuousOn A K) (hfK : ∀ᵐ x ∂volume.restrict S, f x ∈ K)
    (hpos : ∀ y ∈ K, ∀ v, 0 ≤ A y v v) :
    (∫ x in S, weakMapMetricDensity A hf x) =
      ∑ j : Fin 2, ∫ x in S, A (f x)
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j)) := by
  let _ := Fintype.ofFinite ι
  have hi := integrable_weakMapMetricDensity hSΩ hf hK A hA hfK
  apply integral_finsetSum
  intro j hj
  have hm : AEStronglyMeasurable (fun x => A (f x)
      (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) (volume.restrict S) := by
    classical
    have hfm := ((MemLp.of_eval_piLp fun i => (hf i).memLp).mono_measure
      (Measure.restrict_mono_set volume hSΩ)).aestronglyMeasurable
    have hAM : Measurable (K.piecewise A 0) :=
      hA.measurable_piecewise continuous_zero.continuousOn hK.measurableSet
    have hAm : AEStronglyMeasurable (fun x => A (f x)) (volume.restrict S) :=
      (hAM.comp_aemeasurable hfm.aemeasurable).aestronglyMeasurable.congr
        (hfK.mono fun x hx => Set.piecewise_eq_of_mem K A 0 hx)
    have hG : MemLp (fun x =>
        (WithLp.toLp 2 (fun i => (hf i).weakGrad x j) : EuclideanSpace ℝ ι)) 2
        (volume.restrict S) := MemLp.of_eval_piLp fun i =>
      ((hf i).weakGrad_component_memLp j).mono_measure (Measure.restrict_mono_set volume hSΩ)
    have hc := (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hAm.prodMk hG.aestronglyMeasurable)
    exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hc.prodMk hG.aestronglyMeasurable)
  apply hi.mono' hm
  filter_upwards [hfK] with x hx
  rw [Real.norm_of_nonneg (hpos _ hx _)]
  change A (f x) _ _ ≤ ∑ k : Fin 2, A (f x)
    (WithLp.toLp 2 (fun i => (hf i).weakGrad x k))
    (WithLp.toLp 2 (fun i => (hf i).weakGrad x k))
  exact Finset.single_le_sum (fun k _ => hpos (f x) hx
    (WithLp.toLp 2 (fun i => (hf i).weakGrad x k))) (Finset.mem_univ j)

end DifferentialGeometry.Analysis

end
