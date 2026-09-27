import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Strip
import Mathlib.MeasureTheory.Integral.Prod



noncomputable section

open Set MeasureTheory

namespace DifferentialGeometry.Analysis


theorem integrable_unitSquare_coordinates {f : ℂ → ℝ} (hf : IntegrableOn f unitSquare) :
    IntegrableOn (fun p : ℝ × ℝ => f (Complex.measurableEquivRealProd.symm p))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (volume.prod volume) := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm.integrableOn_comp_preimage
    Complex.measurableEquivRealProd.symm.measurableEmbedding).mpr hf
  exact h



theorem integral_unitSquare_eq_iterated {f : ℂ → ℝ} (hf : IntegrableOn f unitSquare) :
    ∫ z in unitSquare, f z =
      ∫ v in Icc (0 : ℝ) 1, ∫ θ in Icc (0 : ℝ) 1, f (Complex.measurableEquivRealProd.symm (v, θ)) := by
  have h := Complex.volume_preserving_equiv_real_prod.symm.integral_comp' (unitSquare.indicator f)
  change (∫ p : ℝ × ℝ, (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1).indicator
    (fun q => f (Complex.measurableEquivRealProd.symm q)) p) = _ at h
  rw [integral_indicator (measurableSet_Icc.prod measurableSet_Icc),
    integral_indicator isCompact_unitSquare.measurableSet] at h
  exact h.symm.trans (setIntegral_prod _ (integrable_unitSquare_coordinates hf))

end DifferentialGeometry.Analysis
