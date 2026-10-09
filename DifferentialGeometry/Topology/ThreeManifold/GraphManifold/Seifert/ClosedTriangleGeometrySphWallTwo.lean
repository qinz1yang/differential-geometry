import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphPhase

/-!
# The closing identity of the spherical gauges along wall 2

Lane B3d (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §4, with
review 32 §5.2–5.5). Let `a > 0` be real (the vertex `v₂`), `b` complex (the vertex `v₁`),
`w = (z - a)/(1 + a z)` the disc coordinate at `a` and `w₁` that of `b`. Then
`(1 + b̄ z)/(1 + a z) = conj (1 + a b)/(1 + a²) · (1 + w̄₁ w)` (`one_add_conj_mul_div`). If the
reflection in the geodesic through `a`, `b` is `w ↦ κ w̄` in the disc coordinate (`‖κ‖ = 1`,
`κ w̄₁ = w₁`), the gauge defect of a point and its mirror image is `2 arg (1 + a b)` modulo `2π`
(`psiS_wallTwo_angle`). On the wall itself (`1 + w̄₁ w > 0`) the defect is exact
(`psiS_sub_psiS_of_wall`), and a real number which is `2 arg (1 + a b)` modulo `2π` and within
`2π` of it is equal to it (`eq_of_coe_angle_eq`): this fixes the branch of the real closing
identity on every neighbourhood of the wall on which the defect stays within `π`.
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open scoped ComplexConjugate

namespace GC.Seifert

namespace ClosedTriangle

namespace Sph

def discA (a : ℝ) (z : ℂ) : ℂ := (z - a) / (1 + a * z)

def discInvA (a : ℝ) (w : ℂ) : ℂ := (w + a) / (1 - a * w)

def reflA (a : ℝ) (κ z : ℂ) : ℂ := discInvA a (κ * conj (discA a z))

theorem one_add_conj_mul_div {a : ℝ} {b z : ℂ} (hz : 1 + a * z ≠ 0) (hb : 1 + a * b ≠ 0) :
    (1 + conj b * z) / (1 + a * z) =
      conj (1 + a * b) / (1 + (a : ℂ) ^ 2) * (1 + conj (discA a b) * discA a z) := by
  have ha : (1 + (a : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 + a ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hcb : conj (1 + (a : ℂ) * b) = 1 + a * conj b := by
    rw [map_add, map_one, map_mul, conj_ofReal]
  have hb' : (1 + (a : ℂ) * conj b) ≠ 0 := by
    rw [← hcb]
    exact (map_ne_zero _).2 hb
  unfold discA
  rw [map_div₀, map_sub, conj_ofReal, hcb]
  have key : 1 + (conj b - a) / (1 + a * conj b) * ((z - a) / (1 + a * z)) =
      (1 + (a : ℂ) ^ 2) * (1 + conj b * z) / ((1 + a * conj b) * (1 + a * z)) := by
    rw [div_mul_div_comm, one_add_div (mul_ne_zero hb' hz)]
    congr 1
    ring
  rw [key, mul_div_assoc', eq_div_iff (mul_ne_zero hb' hz), div_mul_eq_mul_div,
    div_mul_eq_mul_div, div_eq_div_iff hz ha]
  ring

theorem discA_discInvA {a : ℝ} {u : ℂ} (hu : 1 - a * u ≠ 0) : discA a (discInvA a u) = u := by
  unfold discA discInvA
  have h : 1 + (a : ℂ) * ((u + a) / (1 - a * u)) = (1 + (a : ℂ) ^ 2) / (1 - a * u) := by
    field_simp
    ring
  have ha : (1 + (a : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 + a ^ 2 := by positivity
    exact_mod_cast this.ne'
  have e1 : (u + a) / (1 - a * u) - a = u * (1 + (a : ℂ) ^ 2) / (1 - a * u) := by
    rw [eq_div_iff hu, sub_mul, div_mul_cancel₀ _ hu]
    ring
  rw [e1, h, div_div_div_cancel_right₀ hu, mul_div_assoc, div_self ha, mul_one]

theorem one_add_mul_discInvA {a : ℝ} {u : ℂ} (hu : 1 - a * u ≠ 0) :
    1 + a * discInvA a u ≠ 0 := by
  unfold discInvA
  have ha : (1 + (a : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 + a ^ 2 := by positivity
    exact_mod_cast this.ne'
  have h : 1 + (a : ℂ) * ((u + a) / (1 - a * u)) = (1 + (a : ℂ) ^ 2) / (1 - a * u) := by
    field_simp
    ring
  rw [h]
  exact div_ne_zero ha hu

theorem psiS_ofReal (a : ℝ) (z : ℂ) : psiS a z = -arg (1 + a * z) := by
  rw [psiS, conj_ofReal]

theorem arg_conj_div_ofReal (B : ℂ) (a : ℝ) :
    (arg (conj B / (1 + (a : ℂ) ^ 2)) : Real.Angle) = -(arg B : Real.Angle) := by
  have hr : (0 : ℝ) < 1 / (1 + a ^ 2) := by positivity
  rw [div_eq_mul_inv, mul_comm, show ((1 + (a : ℂ) ^ 2))⁻¹ = ((1 / (1 + a ^ 2) : ℝ) : ℂ) by
    push_cast; ring, arg_real_mul _ hr, arg_conj_coe_angle]

theorem psiS_wallTwo_angle {a : ℝ} {b κ z : ℂ} (hw₁ : κ * conj (discA a b) = discA a b)
    (hz : 1 + a * z ≠ 0) (hb : 1 + a * b ≠ 0) (hd : 1 - a * (κ * conj (discA a z)) ≠ 0)
    (h1 : 1 + conj b * z ≠ 0) (h1' : 1 + conj b * reflA a κ z ≠ 0) :
    ((psiS b z + psiS b (reflA a κ z) - psiS a z - psiS a (reflA a κ z) : ℝ) : Real.Angle) =
      ((2 * arg (1 + a * b) : ℝ) : Real.Angle) := by
  set z' := reflA a κ z with hz'
  set w := discA a z with hw
  set w₁ := discA a b with hw₁def
  have hdz' : discA a z' = κ * conj w := discA_discInvA hd
  have hz'0 : 1 + a * z' ≠ 0 := one_add_mul_discInvA hd
  have hB : (1 + (a : ℂ) * b) ≠ 0 := hb
  have hR := one_add_conj_mul_div hz hb
  have hR' := one_add_conj_mul_div (z := z') hz'0 hb
  rw [← hw₁def, ← hw] at hR
  rw [← hw₁def, hdz'] at hR'
  have hY' : 1 + conj w₁ * (κ * conj w) = conj (1 + conj w₁ * w) := by
    have hk : conj w₁ * κ = w₁ := by
      rw [mul_comm]
      exact hw₁
    rw [map_add, map_one, map_mul, conj_conj, ← mul_assoc, hk]
  rw [hY'] at hR'
  have ha : (1 + (a : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 + a ^ 2 := by positivity
    exact_mod_cast this.ne'
  have hY : 1 + conj w₁ * w ≠ 0 := by
    intro h
    rw [h, mul_zero] at hR
    exact div_ne_zero h1 hz hR
  have hcB : conj (1 + (a : ℂ) * b) / (1 + (a : ℂ) ^ 2) ≠ 0 :=
    div_ne_zero ((map_ne_zero _).2 hB) ha
  have e1 := arg_div_coe_angle h1 hz
  have e2 := arg_div_coe_angle h1' hz'0
  rw [hR, arg_mul_coe_angle hcB hY, arg_conj_div_ofReal _ a] at e1
  rw [hR', arg_mul_coe_angle hcB ((map_ne_zero _).2 hY), arg_conj_div_ofReal _ a,
    arg_conj_coe_angle] at e2
  have key : ((psiS b z + psiS b z' - psiS a z - psiS a z' : ℝ) : Real.Angle) =
      -((arg (1 + conj b * z) : Real.Angle) - arg (1 + a * z)) -
        ((arg (1 + conj b * z') : Real.Angle) - arg (1 + a * z')) := by
    rw [psiS_ofReal, psiS_ofReal]
    unfold psiS
    simp only [Real.Angle.coe_add, Real.Angle.coe_sub, Real.Angle.coe_neg]
    abel
  rw [key, ← e1, ← e2, show (2 * arg (1 + (a : ℂ) * b) : ℝ) =
    arg (1 + (a : ℂ) * b) + arg (1 + (a : ℂ) * b) by ring, Real.Angle.coe_add]
  abel

theorem eq_of_coe_angle_eq {x y : ℝ} (h : (x : Real.Angle) = y) (hxy : |x - y| < 2 * Real.pi) :
    x = y := by
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 h
  rw [hk] at hxy
  have hpi := Real.pi_pos
  have hk0 : k = 0 := by
    by_contra hk0
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hk0
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hxy
    nlinarith
  rw [hk0, Int.cast_zero, mul_zero, sub_eq_zero] at hk
  exact hk

theorem psiS_sub_psiS_of_wall {a : ℝ} {b z : ℂ} (hz : 0 < (1 + a * z).re)
    (hB : 0 < (1 + a * b).re) (hY : 0 < (1 + conj (discA a b) * discA a z).re)
    (hY' : (1 + conj (discA a b) * discA a z).im = 0) :
    psiS b z - psiS a z = arg (1 + a * b) := by
  have hz0 : 1 + (a : ℂ) * z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hb0 : 1 + (a : ℂ) * b ≠ 0 := fun h => by rw [h] at hB; simp at hB
  have hR := one_add_conj_mul_div hz0 hb0
  set Y := 1 + conj (discA a b) * discA a z with hYdef
  have hYr : Y = ((Y.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hY']
  set r := Y.re with hrdef
  have hpos : (0 : ℝ) < r / (1 + a ^ 2) := by positivity
  have h1 : 1 + conj b * z = ((r / (1 + a ^ 2) : ℝ) : ℂ) * (conj (1 + a * b) * (1 + a * z)) := by
    rw [← div_mul_cancel₀ (1 + conj b * z) hz0, hR, hYr]
    push_cast
    ring
  have hcB : conj (1 + (a : ℂ) * b) ≠ 0 := (map_ne_zero _).2 hb0
  have hargB : |arg (1 + (a : ℂ) * b)| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.2 (Or.inl hB)
  have hargz : |arg (1 + (a : ℂ) * z)| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.2 (Or.inl hz)
  have hne : arg (1 + (a : ℂ) * b) ≠ Real.pi := by
    intro h
    rw [h, abs_of_pos Real.pi_pos] at hargB
    linarith [Real.pi_pos]
  have hconj : arg (conj (1 + (a : ℂ) * b)) = -arg (1 + (a : ℂ) * b) := by
    rw [arg_conj]
    simp [hne]
  have hmul : arg (conj (1 + (a : ℂ) * b) * (1 + a * z)) =
      arg (conj (1 + (a : ℂ) * b)) + arg (1 + a * z) := by
    apply arg_mul hcB hz0
    rw [hconj]
    constructor <;> linarith [abs_lt.1 hargB, abs_lt.1 hargz]
  rw [psiS_ofReal, psiS, h1, arg_real_mul _ hpos, hmul, hconj]
  ring

end Sph

end ClosedTriangle

end GC.Seifert
