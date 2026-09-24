import DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses
import DifferentialGeometry.Analysis.Integration.Lp.Bilinear
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry.Analysis

theorem integrable_sum_quadratic_weakGrad
    {d : ℕ} {ι : Type*} [Finite ι]
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {w : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ ι}
    (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) Ω)
    {K : Set (EuclideanSpace ℝ ι)} (hK : IsCompact K)
    (A : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hA : ContinuousOn A K) (hwK : ∀ᵐ x ∂volume.restrict Ω, w x ∈ K) :
    IntegrableOn (fun x => ∑ j : Fin d, A (w x)
      (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
      (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) Ω := by
  classical
  let _ := Fintype.ofFinite ι
  have hwm : AEStronglyMeasurable w (volume.restrict Ω) :=
    (MemLp.of_eval_piLp fun i => (hw i).memLp).aestronglyMeasurable
  have hm : Measurable (K.piecewise A 0) :=
    hA.measurable_piecewise continuous_zero.continuousOn hK.measurableSet
  have hAm : AEStronglyMeasurable (fun x => A (w x)) (volume.restrict Ω) :=
    (hm.comp_aemeasurable hwm.aemeasurable).aestronglyMeasurable.congr
      (hwK.mono fun x hx => Set.piecewise_eq_of_mem K A 0 hx)
  obtain ⟨C, hC⟩ := hK.bddAbove_image
    ((@continuous_norm (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
      inferInstance).comp_continuousOn hA)
  have hb : ∀ᵐ x ∂volume.restrict Ω, ‖A (w x)‖ ≤ C :=
    hwK.mono fun x hx => hC (mem_image_of_mem _ hx)
  apply integrable_finsetSum
  intro j hj
  have hG : MemLp (fun x =>
      (WithLp.toLp 2 (fun i => (hw i).weakGrad x j) : EuclideanSpace ℝ ι)) 2
      (volume.restrict Ω) := MemLp.of_eval_piLp fun i => (hw i).weakGrad_component_memLp j
  exact integrable_bilinear_of_apply_aestronglyMeasurable (fun x => A (w x))
    (fun v z => (hAm.apply_continuousLinearMap v).apply_continuousLinearMap z) hb hG hG

end DifferentialGeometry.Analysis

end
