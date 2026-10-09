import DifferentialGeometry.Geometry.Exponential.Flat.InvolutionAxis

/-!
A positive nontrivial involution negates the plane orthogonal to its fixed axis. The square
of an actual fourfold positive rotation therefore negates that perpendicular plane.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem involution_orthogonal_neg (L : E3 ≃ₗᵢ[ℝ] E3) (hp : L ^ 2 = 1) (hn : L ≠ 1)
    (hpos : 0 < LinearMap.det L.toLinearMap) (q x : E3) (hq : q ≠ 0)
    (hfix : L q = q) (horth : inner ℝ q x = 0) : L x = -x := by
  have hLL : L (L x) = x := congrArg (fun K : E3 ≃ₗᵢ[ℝ] E3 => K x) hp
  let s := x + L x
  have hs : L s = s := by
    change L (x + L x) = x + L x
    rw [map_add, hLL]
    abel
  obtain ⟨a, ha⟩ := involution_fixedVector_uniqueLine L hp hn hpos q s hq hfix hs
  have hi : inner ℝ q (L x) = 0 := by
    have he := L.inner_map_map q x
    rw [hfix, horth] at he
    exact he
  have his : inner ℝ q s = 0 := by
    change inner ℝ q (x + L x) = 0
    rw [inner_add_right, horth, hi]
    norm_num
  rw [ha, real_inner_smul_right] at his
  have hqq : inner ℝ q q ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hq)
  have hz : a = 0 := (mul_eq_zero.mp his).resolve_right hqq
  have hs0 : s = 0 := by simpa only [hz, zero_smul] using ha
  apply add_eq_zero_iff_eq_neg.mp
  simpa only [s, add_comm] using hs0

theorem orderFour_orthogonal_square_neg (L : E3 ≃ₗᵢ[ℝ] E3) (horder : orderOf L = 4)
    (hpos : 0 < LinearMap.det L.toLinearMap) (q x : E3) (hq : q ≠ 0)
    (hfix : L q = q) (horth : inner ℝ q x = 0) : (L ^ 2) x = -x := by
  have hp : (L ^ 2) ^ 2 = 1 := by
    rw [← pow_mul]
    simpa only [horder] using pow_orderOf_eq_one L
  have hn : L ^ 2 ≠ 1 := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    norm_num [horder] at hd
  have hpos2 : 0 < LinearMap.det (L ^ 2).toLinearMap := by
    change 0 < LinearMap.det (L.toLinearMap * L.toLinearMap)
    rw [map_mul]
    exact mul_pos hpos hpos
  have hfix2 : (L ^ 2) q = q := by
    change L (L q) = q
    rw [hfix, hfix]
  exact involution_orthogonal_neg (L ^ 2) hp hn hpos2 q x hq hfix2 horth

end DifferentialGeometry.Geometry.FlatSurface
