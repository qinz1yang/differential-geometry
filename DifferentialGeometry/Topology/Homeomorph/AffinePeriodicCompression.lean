import DifferentialGeometry.Topology.LoopSpace.PeriodicExtension
import DifferentialGeometry.Topology.Homeomorph.AffinePeriodic

section

noncomputable section
open Set
open scoped NNReal

namespace DifferentialGeometry.Analysis

theorem exists_affinePeriodic_homeomorph_eq_mul_on_Icc
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ (F : ℝ ≃ₜ ℝ) (L : ℝ≥0),
      (∀ t, F (t + 1) = F t + 1) ∧ LipschitzWith 4 F ∧ LipschitzWith L F.symm ∧
      ∀ t ∈ Icc (0 : ℝ) (3 / 4), F t = q * t := by
  let P := fun t : ℝ => q * t + 4 * (1 - q) * max (t - 3 / 4) 0
  have hPc : Continuous P := by fun_prop
  have hP0 : P 0 = 0 := by norm_num [P]
  have hP1 : P 1 = 1 := by norm_num [P]; ring
  obtain ⟨G, hGc, hG⟩ := AddConstMap.exists_continuous_extension_Icc 0 hPc.continuousOn
    (by rw [zero_add, hP0, hP1, zero_add])
  have hGp (t : ℝ) : G (t + 1) = G t + 1 := G.map_add_const' t
  have hslope {x y : ℝ} (hxy : x ≤ y) :
      q * (y - x) ≤ P y - P x ∧ P y - P x ≤ 4 * (y - x) := by
    have hmax : 0 ≤ max (y - 3 / 4) 0 - max (x - 3 / 4) 0 :=
      sub_nonneg.mpr (max_le_max (by linarith) le_rfl)
    have hmax' : max (y - 3 / 4) 0 - max (x - 3 / 4) 0 ≤ y - x := by
      rcases le_or_gt y (3 / 4) with hy | hy
      · rw [max_eq_right (by linarith), max_eq_right (by linarith)]
        linarith
      · rcases le_or_gt x (3 / 4) with hx | hx
        · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
          linarith
        · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
          linarith
    dsimp only [P]
    constructor <;> nlinarith
  let H : AddConstMap ℝ ℝ 1 (1 - q) :=
    ⟨fun t => G t - q * t, fun t => by rw [hGp]; ring⟩
  have hHm : Monotone H := (AddConstMapClass.monotone_iff_Icc
    (f := H) (by norm_num : (0 : ℝ) < 1) 0).mpr (by
      intro x hx y hy hxy
      change G x - q * x ≤ G y - q * y
      rw [hG hx, hG hy]
      have hh := (hslope hxy).1
      linarith)
  let J : AddConstMap ℝ ℝ 1 3 :=
    ⟨fun t => 4 * t - G t, fun t => by rw [hGp]; ring⟩
  have hJm : Monotone J := (AddConstMapClass.monotone_iff_Icc
    (f := J) (by norm_num : (0 : ℝ) < 1) 0).mpr (by
      intro x hx y hy hxy
      change 4 * x - G x ≤ 4 * y - G y
      rw [hG hx, hG hy]
      have hh := (hslope hxy).2
      linarith)
  have hlo (x y : ℝ) (hxy : x ≤ y) : q * (y - x) ≤ G y - G x := by
    have hh := hHm hxy
    change G x - q * x ≤ G y - q * y at hh
    linarith
  have hhi (x y : ℝ) (hxy : x ≤ y) : G y - G x ≤ 4 * (y - x) := by
    have hh := hJm hxy
    change 4 * x - G x ≤ 4 * y - G y at hh
    linarith
  have hgm : Monotone G := fun x y hxy => by
    have hh := hlo x y hxy
    nlinarith
  have hLip : LipschitzWith 4 G := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rcases le_total x y with hxy | hyx
    · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy),
        abs_of_nonpos (sub_nonpos.mpr (hgm hxy)), neg_sub, NNReal.coe_ofNat] using hhi x y hxy
    · simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx),
        abs_of_nonneg (sub_nonneg.mpr (hgm hyx)), NNReal.coe_ofNat] using hhi y x hyx
  obtain ⟨F, L, hF, hL⟩ := exists_homeomorph_affinePeriodic_of_lowerSlope hGc hGp hq hlo
  refine ⟨F, L, fun t => by rw [hF, hGp, hF], ?_, hL, ?_⟩
  · exact (funext hF : (F : ℝ → ℝ) = G).symm ▸ hLip
  · intro t ht
    rw [hF, hG (show t ∈ Icc (0 : ℝ) (0 + 1) from ⟨ht.1, by linarith [ht.2]⟩)]
    have hmax : max (t - 3 / 4) 0 = 0 := max_eq_right (by linarith [ht.2])
    simp only [P, hmax, mul_zero, add_zero]

end DifferentialGeometry.Analysis

end

end
