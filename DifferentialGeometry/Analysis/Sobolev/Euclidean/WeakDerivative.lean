import DifferentialGeometry.External.DeGiorgi.SobolevSpace.WeakDerivatives
import DifferentialGeometry.Analysis.Integration.Integral.LocalIntegrationByParts

noncomputable section

open MeasureTheory Set

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem hasWeakPartialDeriv_of_contDiffOn
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ}
    (hf : ContDiffOn ℝ 1 f Ω) (i : Fin d) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) f Ω := by
  intro φ hφ hφc hφs
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_contDiffOn hΩ hf
    (hφ.of_le (by simp)) hφc hφs (EuclideanSpace.single i 1)

end DifferentialGeometry.Analysis.Sobolev.Euclidean
