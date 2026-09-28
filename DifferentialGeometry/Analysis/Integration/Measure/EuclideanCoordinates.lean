import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section

open MeasureTheory

namespace EuclideanSpace

variable (d : ℕ)

def finSuccEquivProd : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ]
    ℝ × EuclideanSpace ℝ (Fin d) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (d + 1) => ℝ)).trans
    ((Fin.consEquivL ℝ (fun _ : Fin (d + 1) => ℝ)).symm.trans
      (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm))

theorem finSuccEquivProd_apply (x : EuclideanSpace ℝ (Fin (d + 1))) :
    finSuccEquivProd d x = (x 0, WithLp.toLp 2 (fun i => x i.succ)) := rfl

theorem measurePreserving_finSuccEquivProd : MeasurePreserving (finSuccEquivProd d) := by
  have h₁ := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (d + 1))
  have h₂ := volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have h₃ := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).symm
  convert h₃.comp (h₂.comp h₁) using 1
  · funext x
    simp [finSuccEquivProd_apply, Function.comp_def, MeasurableEquiv.piFinSuccAbove]
    rfl

theorem finSuccEquivProd_single_zero :
    finSuccEquivProd d (EuclideanSpace.single 0 1) = (1, 0) := by
  rw [finSuccEquivProd_apply]
  ext i <;> simp

theorem finSuccEquivProd_single_succ (i : Fin d) :
    finSuccEquivProd d (EuclideanSpace.single i.succ 1) =
      (0, EuclideanSpace.single i 1) := by
  rw [finSuccEquivProd_apply]
  ext j <;> simp

end EuclideanSpace

end
