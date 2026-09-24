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

end

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem measurePreserving_complex_plane_repr_closedBall (b : ℝ) :
    MeasurePreserving Complex.orthonormalBasisOneI.repr
      (volume.restrict (Metric.closedBall (0 : ℂ) b))
      (volume.restrict (Metric.closedBall (0 : V) b)) := by
  have h := Complex.orthonormalBasisOneI.repr.measurePreserving.restrict_preimage
    (s := Metric.closedBall (0 : V) b) measurableSet_closedBall
  have heq : Complex.orthonormalBasisOneI.repr ⁻¹' Metric.closedBall (0 : V) b =
      Metric.closedBall (0 : ℂ) b := by
    ext z
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right,
      LinearIsometryEquiv.norm_map]
  simpa only [heq] using h

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

theorem restrict_ball_eq_restrict_closedBall_complex (b : ℝ) :
    volume.restrict (Metric.ball (0 : ℂ) b) =
      volume.restrict (Metric.closedBall (0 : ℂ) b) := by
  apply Measure.restrict_congr_set
  have hnull : ∀ᵐ z : ℂ ∂volume, z ∉ Metric.sphere (0 : ℂ) b :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume (0 : ℂ) b)
  filter_upwards [hnull] with z hz
  apply propext
  change dist z (0 : ℂ) < b ↔ dist z (0 : ℂ) ≤ b
  have hne : dist z (0 : ℂ) ≠ b := hz
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hne⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

local notation "E" => EuclideanSpace ℝ (Fin 2)

theorem measurePreserving_complex_plane_repr_ball (a : ℝ) :
    MeasurePreserving Complex.orthonormalBasisOneI.repr
      (volume.restrict (Metric.ball (0 : ℂ) a))
      (volume.restrict (Metric.ball (0 : E) a)) := by
  have h := Complex.orthonormalBasisOneI.repr.measurePreserving.restrict_preimage
    (s := Metric.ball (0 : E) a) Metric.isOpen_ball.measurableSet
  have heq : Complex.orthonormalBasisOneI.repr ⁻¹' Metric.ball (0 : E) a =
      Metric.ball (0 : ℂ) a := by
    ext z
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right,
      LinearIsometryEquiv.norm_map]
  simpa only [heq] using h

theorem eLpNorm_comp_complex_plane_repr_ball
    {F : Type*} [NormedAddCommGroup F] (f : E → F) (p : ℝ≥0∞) (a : ℝ) :
    eLpNorm (f ∘ Complex.orthonormalBasisOneI.repr) p
      (volume.restrict (Metric.ball (0 : ℂ) a)) =
      eLpNorm f p (volume.restrict (Metric.ball (0 : E) a)) := by
  have h :=
    Complex.orthonormalBasisOneI.repr.toMeasurableEquiv.measurableEmbedding.eLpNorm_map_measure
    (g := f) (p := p) (μ := volume.restrict (Metric.ball (0 : ℂ) a))
  rw [LinearIsometryEquiv.coe_toMeasurableEquiv,
    (measurePreserving_complex_plane_repr_ball a).map_eq] at h
  exact h.symm

theorem integral_comp_complex_plane_repr_ball (f : E → ℝ) (a : ℝ) :
    (∫ z in Metric.ball (0 : ℂ) a, f (Complex.orthonormalBasisOneI.repr z)) =
      ∫ x in Metric.ball (0 : E) a, f x :=
  (measurePreserving_complex_plane_repr_ball a).integral_comp
    Complex.orthonormalBasisOneI.repr.toMeasurableEquiv.measurableEmbedding f

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
