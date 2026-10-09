import DifferentialGeometry.Geometry.Comparison.PairedDistanceLocalOpenness

set_option autoImplicit false

open Set Metric Real
open scoped Topology ENNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X ι : Type*} [MetricSpace X] [Fintype ι] [Nonempty ι]

theorem PairedComparisonPacket.card_le_dimH
    {β : ℝ} {q : X} {Ω : Set X} {a b : ι → X}
    (hpacket : PairedComparisonPacket β {q} a b)
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    (hcomp : fourPointComparison 1 Ω) (hΩ : Ω ∈ 𝓝 q)
    (hanchors : range a ∪ range b ⊆ Ω)
    (hβ : 0 < β) (hβm : β ≤ 1 / (200 * Fintype.card ι))
    (hcomplete : ∀ z ∈ Ω, ∃ R : ℝ, 0 < R ∧ IsComplete (closedBall z R)) :
    (Fintype.card ι : ℝ≥0∞) ≤ dimH Ω := by
  have hm : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hp : PairedComparisonPacket ((2 * β) / 2) {q} a b := by
    simpa only [mul_div_cancel_left₀ β (by norm_num : (2 : ℝ) ≠ 0)] using hpacket
  have hquality : 2 * β ≤ 1 / (100 * Fintype.card ι) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have h := (le_div_iff₀ (show 0 < 200 * (Fintype.card ι : ℝ) by positivity)).mp hβm
    nlinarith
  obtain ⟨V, _, _, hV, _, _, _, _, _, _, hd⟩ :=
    exists_open_distanceCoordinates_of_pointwise_packet hcurves hp hcomp hΩ hanchors
      (show 0 < 2 * β by positivity) hquality hcomplete
  exact hd.trans (dimH_mono hV)

end DifferentialGeometry.Geometry.Comparison.Toponogov
