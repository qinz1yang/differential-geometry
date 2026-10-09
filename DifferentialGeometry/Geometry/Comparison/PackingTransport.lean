import DifferentialGeometry.Geometry.Comparison.RadialTransport
import DifferentialGeometry.Topology.MetricSpace.FinitePacking

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem exists_radial_finset_image
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    {Ω W : Set X} (hcomp : fourPointComparison 1 Ω) {q : X} (hq : q ∈ Ω)
    {a D t ρ ε : ℝ} (ha : 0 < a) (haD : a ≤ D) (ht : t ∈ Ioo 0 1)
    (htD : t * D < ρ) (hε : 0 < ε) (hB : ball q ρ ⊆ Ω) (hW : W ⊆ Ω)
    (hrad : ∀ x ∈ W, dist q x ∈ Icc a D)
    (A : Finset X) (hA : (A : Set X) ⊆ W)
    (hsep : (A : Set X).Pairwise (fun x y => ε ≤ dist x y)) :
    ∃ B : Finset X, (B : Set X) ⊆ ball q ρ ∧ B.card = A.card ∧
      (B : Set X).Pairwise (fun x y => ((t * D / sinh D) / 2) * ε ≤ dist x y) := by
  obtain ⟨f, _, hlower⟩ := exists_radial_map_of_arbitrarily_short_curves hcurves hcomp hq
    ha haD ht htD hε hB hW hrad
  have hK : 0 < (t * D / sinh D) / 2 :=
    div_pos (div_pos (mul_pos ht.1 (ha.trans_le haD)) (sinh_pos_iff.mpr (ha.trans_le haD)))
      (by norm_num)
  exact exists_finset_image_of_lower_dist hε hK hlower A hA hsep

theorem finitePackingNumber_le_radial_ball
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    {Ω W : Set X} (hcomp : fourPointComparison 1 Ω) {q : X} (hq : q ∈ Ω)
    {a D t ρ ε : ℝ} (ha : 0 < a) (haD : a ≤ D) (ht : t ∈ Ioo 0 1)
    (htD : t * D < ρ) (hε : 0 < ε) (hB : ball q ρ ⊆ Ω) (hW : W ⊆ Ω)
    (hrad : ∀ x ∈ W, dist q x ∈ Icc a D) :
    finitePackingNumber ε W ≤
      finitePackingNumber (((t * D / sinh D) / 2) * ε) (ball q ρ) := by
  apply finitePackingNumber_le_of_finite_images
  intro A hA hsep
  obtain ⟨B, hB', hcard, hsepB⟩ := exists_radial_finset_image hcurves hcomp hq
    ha haD ht htD hε hB hW hrad A hA hsep
  exact ⟨B, hB', hcard.ge, hsepB⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
