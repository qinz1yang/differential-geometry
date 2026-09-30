import DifferentialGeometry.Geometry.Comparison.PairedPacketDimension
import DifferentialGeometry.Geometry.Comparison.CurvatureWeakening

set_option autoImplicit false

open Set Metric
open scoped ENNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X ι : Type*} [MetricSpace X] [Fintype ι] [Nonempty ι]

theorem not_pairedComparisonPacket_of_dimH_le_one
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    (hcomp : fourPointComparison 0 (univ : Set X))
    (hcomplete : ∀ z : X, ∃ R : ℝ, 0 < R ∧ IsComplete (closedBall z R))
    (hdim : dimH (univ : Set X) ≤ 1) (hcard : Fintype.card ι = 2)
    (q : X) (a b : ι → X) : ¬ PairedComparisonPacket (1/1000) {q} a b := by
  intro hp
  have h := hp.card_le_dimH hcurves (hcomp.of_zero (by norm_num))
    Filter.univ_mem (subset_univ _) (by norm_num) (by norm_num [hcard]) (fun z _ => hcomplete z)
  have h' := h.trans hdim
  norm_num [hcard] at h'

end DifferentialGeometry.Geometry.Comparison.Toponogov
