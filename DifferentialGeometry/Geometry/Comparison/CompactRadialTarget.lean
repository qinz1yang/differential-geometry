import DifferentialGeometry.Geometry.Comparison.PackingTransport
import DifferentialGeometry.Topology.MetricSpace.CompactPackingTransport

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem totallyBounded_annulus_of_compact_radial_target
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    {Ω W : Set X} (hcomp : fourPointComparison 1 Ω) {q : X} (hq : q ∈ Ω)
    {a D t ρ : ℝ} (ha : 0 < a) (haD : a ≤ D) (ht : t ∈ Ioo 0 1)
    (htD : t * D < ρ) (hB : ball q ρ ⊆ Ω) (hW : W ⊆ Ω)
    (hrad : ∀ x ∈ W, dist q x ∈ Icc a D)
    (hcompact : IsCompact (closedBall q ρ)) : TotallyBounded W := by
  have hK : 0 < (t * D / sinh D) / 2 :=
    div_pos (div_pos (mul_pos ht.1 (ha.trans_le haD)) (sinh_pos_iff.mpr (ha.trans_le haD)))
      (by norm_num)
  apply totallyBounded_of_finite_transport_to_compact hcompact hK
  intro ε hε A hA hsep
  obtain ⟨B, hB', hcard, hsepB⟩ := exists_radial_finset_image hcurves hcomp hq
    ha haD ht htD hε hB hW hrad A hA hsep
  exact ⟨B, hB'.trans ball_subset_closedBall, hcard.ge, hsepB⟩


end DifferentialGeometry.Geometry.Comparison.Toponogov
