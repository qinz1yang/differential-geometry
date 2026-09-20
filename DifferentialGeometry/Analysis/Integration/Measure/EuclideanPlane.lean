import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace DifferentialGeometry.Analysis

def euclideanPlaneProdEquiv : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] ℝ × ℝ :=
  Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.trans Complex.equivRealProdCLM

@[simp] theorem euclideanPlaneProdEquiv_apply (x : EuclideanSpace ℝ (Fin 2)) :
    euclideanPlaneProdEquiv x = (x 0, x 1) := by
  simp [euclideanPlaneProdEquiv, Complex.orthonormalBasisOneI_repr_symm_apply]

@[simp] theorem euclideanPlaneProdEquiv_symm_apply (p : ℝ × ℝ) :
    euclideanPlaneProdEquiv.symm p = WithLp.toLp 2 ![p.1, p.2] := by
  apply euclideanPlaneProdEquiv.injective
  simp

theorem measurePreserving_euclideanPlaneProdEquiv :
    MeasurePreserving euclideanPlaneProdEquiv volume volume := by
  exact Complex.volume_preserving_equiv_real_prod.comp
    Complex.orthonormalBasisOneI.measurePreserving_repr_symm

theorem euclideanPlaneProdEquiv_preimage_unit_disk :
    euclideanPlaneProdEquiv ⁻¹' {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1} =
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
  ext x
  rw [mem_preimage, euclideanPlaneProdEquiv_apply]
  change x 0 ^ 2 + x 1 ^ 2 < 1 ↔ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1
  rw [EuclideanSpace.ball_zero_eq 1 (by norm_num : (0 : ℝ) ≤ 1)]
  simp [Fin.sum_univ_two]

theorem integral_unit_disk_prod_eq_integral_ball
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ × ℝ → F) :
    (∫ p in {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}, f p) =
      ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1, f (euclideanPlaneProdEquiv x) := by
  have h := measurePreserving_euclideanPlaneProdEquiv.setIntegral_preimage_emb
    euclideanPlaneProdEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding f
    {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
  rw [euclideanPlaneProdEquiv_preimage_unit_disk] at h
  exact h.symm

theorem measurePreserving_euclideanPlaneProdEquiv_unit_ball :
    MeasurePreserving euclideanPlaneProdEquiv
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1))
      (volume.restrict {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}) := by
  have h := measurePreserving_euclideanPlaneProdEquiv.restrict_preimage
    (show MeasurableSet {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1} from
      (isOpen_lt (by fun_prop) continuous_const).measurableSet)
  rw [euclideanPlaneProdEquiv_preimage_unit_disk] at h
  exact h

theorem measurePreserving_euclideanPlaneProdEquiv_symm_unit_disk :
    MeasurePreserving euclideanPlaneProdEquiv.symm
      (volume.restrict {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1})
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) :=
  MeasurePreserving.symm euclideanPlaneProdEquiv.toHomeomorph.toMeasurableEquiv
    measurePreserving_euclideanPlaneProdEquiv_unit_ball

theorem fderiv_comp_euclideanPlaneProdEquiv_symm_snd
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (f ∘ euclideanPlaneProdEquiv.symm) p (0, 1) =
      fderiv ℝ f (euclideanPlaneProdEquiv.symm p) (EuclideanSpace.single 1 1) := by
  rw [euclideanPlaneProdEquiv.symm.comp_right_fderiv]
  change fderiv ℝ f (euclideanPlaneProdEquiv.symm p)
    (euclideanPlaneProdEquiv.symm (0, 1)) = _
  congr 1
  rw [euclideanPlaneProdEquiv_symm_apply]
  ext i
  fin_cases i <;> simp

theorem eLpNorm_comp_euclideanPlaneProdEquiv_symm
    {F : Type*} [NormedAddCommGroup F] {f : EuclideanSpace ℝ (Fin 2) → F}
    (hf : AEStronglyMeasurable f
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1))) (p : ℝ≥0∞) :
    eLpNorm (f ∘ euclideanPlaneProdEquiv.symm) p
      (volume.restrict {q : ℝ × ℝ | q.1 ^ 2 + q.2 ^ 2 < 1}) =
      eLpNorm f p (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) :=
  eLpNorm_comp_measurePreserving hf measurePreserving_euclideanPlaneProdEquiv_symm_unit_disk

end DifferentialGeometry.Analysis
