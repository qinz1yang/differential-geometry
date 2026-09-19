import DifferentialGeometry.Analysis.Integration.Lp.ContinuousOn
import Mathlib.Analysis.Calculus.ContDiff.Comp

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis

variable {Z E F : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace (Z × E)]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem memLp_top_and_spatial_fderiv_of_contDiffOn
    {S J : Set Z} (hS : IsOpen S) (hJ : IsCompact J) (hJS : J ⊆ S)
    {U Ω : Set E} (hU : IsOpen U) (hΩ : MeasurableSet Ω)
    (hΩc : IsCompact (closure Ω)) (hΩU : closure Ω ⊆ U)
    {A : Z → E → F}
    (hA : ContDiffOn ℝ 1 (fun p : Z × E => A p.1 p.2) (S ×ˢ U))
    (μ : Measure (Z × E)) :
    MemLp (fun p : Z × E => A p.1 p.2) ∞ (μ.restrict (J ×ˢ Ω)) ∧
      (∀ v : E, MemLp (fun p : Z × E => fderiv ℝ (A p.1) p.2 v)
        ∞ (μ.restrict (J ×ˢ Ω))) := by
  constructor
  · exact (hA.continuousOn.mono (prod_mono hJS hΩU)).memLp_top_of_subset_isCompact
      (hJ.prod hΩc) (hJ.measurableSet.prod hΩ) (prod_mono Subset.rfl subset_closure)
  · intro v
    have hc : ContinuousOn (fun p : Z × E =>
        fderiv ℝ (fun q : Z × E => A q.1 q.2) p (0, v)) (S ×ˢ U) :=
      (hA.continuousOn_fderiv_of_isOpen (hS.prod hU) le_rfl).clm_apply continuousOn_const
    have heq (p : Z × E) (hp : p ∈ S ×ˢ U) :
        fderiv ℝ (A p.1) p.2 v = fderiv ℝ (fun q : Z × E => A q.1 q.2) p (0, v) := by
      have hd := ((hA.differentiableOn (by norm_num) p hp).differentiableAt
        ((hS.prod hU).mem_nhds hp)).hasFDerivAt
      have hh := hd.comp p.2 ((hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2))
      exact congrArg (fun L : E →L[ℝ] F => L v) hh.fderiv
    have hs : ContinuousOn (fun p : Z × E => fderiv ℝ (A p.1) p.2 v) (S ×ˢ U) :=
      hc.congr (fun p hp => heq p hp)
    exact (hs.mono (prod_mono hJS hΩU)).memLp_top_of_subset_isCompact
      (hJ.prod hΩc) (hJ.measurableSet.prod hΩ) (prod_mono Subset.rfl subset_closure)

end DifferentialGeometry.Analysis
