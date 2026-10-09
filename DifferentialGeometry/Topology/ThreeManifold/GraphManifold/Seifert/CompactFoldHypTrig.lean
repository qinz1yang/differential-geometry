import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypDisc

/-!
# Hyperbolic triangles with prescribed angles in the disc

Lane CF-H, tier 1 (design
`docs/geometrization/handoffs/20261004-design-cf-compact-triangle-fold.md`,
§2, curvature `-1`). For angles `α, β, γ ∈ (0, π/2]` with `α + β + γ < π` the quantity
`hDelta α β γ = cos²α + cos²β + cos²γ + 2 cos α cos β cos γ - 1` is symmetric and positive
(`hDelta_eq`, `hDelta_pos`), and the half-side tangent of the side between the vertices of angles
`α` and `β` (opposite `γ`) is `hTan α β γ = √Δ / (cos γ + cos (α - β)) ∈ (0, 1)`, equal to the
`tanh (ℓ/2)` defined from the law of cosines `cosh ℓ = (cos γ + cos α cos β)/(sin α sin β)`
(`sqrt_sideCos_eq`).

The placement identity `hTan_placement`: with `O = 0` (angle `γ`), `A = hTan α γ β` on the
positive axis (angle `α`) and `B = hTan β γ α · e^{iγ}` (angle `β`), the disc coordinate of `B`
at `A` is `(B - A)/(1 - A B) = -hTan α β γ · e^{-iα}`: the side `AB` has the right length and
leaves `A` at the interior angle `α`. It is a polynomial identity in the cosines and sines once
the square root is cleared. Consequently `hTan α β γ < hTan α γ β ⊕ hTan β γ α`
(`hTan_lt_oplus`, the strict triangle inequality, with `a ⊕ b = (a + b)/(1 + a b)`).
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate

namespace GC.Seifert

namespace HypFold

def hDelta (α β γ : ℝ) : ℝ :=
  Real.cos α ^ 2 + Real.cos β ^ 2 + Real.cos γ ^ 2 + 2 * Real.cos α * Real.cos β * Real.cos γ - 1

def hTan (α β γ : ℝ) : ℝ := Real.sqrt (hDelta α β γ) / (Real.cos γ + Real.cos (α - β))

def oplus (a b : ℝ) : ℝ := (a + b) / (1 + a * b)

theorem hDelta_swap_left (α β γ : ℝ) : hDelta β α γ = hDelta α β γ := by
  unfold hDelta
  ring

theorem hDelta_swap_right (α β γ : ℝ) : hDelta α γ β = hDelta α β γ := by
  unfold hDelta
  ring

theorem hTan_swap (α β γ : ℝ) : hTan β α γ = hTan α β γ := by
  rw [hTan, hTan, hDelta_swap_left, ← Real.cos_neg (β - α), neg_sub]

theorem hDelta_eq (α β γ : ℝ) : hDelta α β γ =
    (Real.cos γ + Real.cos (α + β)) * (Real.cos γ + Real.cos (α - β)) := by
  rw [hDelta, Real.cos_add, Real.cos_sub]
  have ha := Real.sin_sq_add_cos_sq α
  have hb := Real.sin_sq_add_cos_sq β
  linear_combination (Real.sin β ^ 2) * ha + (1 - Real.cos α ^ 2) * hb

section Angles

variable {α β γ : ℝ}

theorem cos_sub_pos (hα : 0 < α) (hα' : α ≤ Real.pi / 2) (hβ : 0 < β) (hβ' : β ≤ Real.pi / 2) :
    0 < Real.cos (α - β) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith

theorem cos_nonneg_of_le (hγ : 0 < γ) (hγ' : γ ≤ Real.pi / 2) : 0 ≤ Real.cos γ :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith, hγ'⟩

theorem sin_pos_of_le (hγ : 0 < γ) (hγ' : γ ≤ Real.pi / 2) : 0 < Real.sin γ :=
  Real.sin_pos_of_pos_of_lt_pi hγ (by linarith [Real.pi_pos])

theorem hTan_den_pos (hα : 0 < α) (hα' : α ≤ Real.pi / 2) (hβ : 0 < β) (hβ' : β ≤ Real.pi / 2)
    (hγ : 0 < γ) (hγ' : γ ≤ Real.pi / 2) : 0 < Real.cos γ + Real.cos (α - β) := by
  have := cos_sub_pos hα hα' hβ hβ'
  have := cos_nonneg_of_le hγ hγ'
  linarith

theorem cos_add_cos_add_pos (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hs : α + β + γ < Real.pi) : 0 < Real.cos γ + Real.cos (α + β) := by
  have h1 : Real.cos (Real.pi - (α + β)) < Real.cos γ := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi hγ.le (by linarith) (by linarith)
  rw [Real.cos_pi_sub] at h1
  linarith

theorem hDelta_pos (hα : 0 < α) (hα' : α ≤ Real.pi / 2) (hβ : 0 < β) (hβ' : β ≤ Real.pi / 2)
    (hγ : 0 < γ) (hγ' : γ ≤ Real.pi / 2) (hs : α + β + γ < Real.pi) : 0 < hDelta α β γ := by
  rw [hDelta_eq]
  exact mul_pos (cos_add_cos_add_pos hα hβ hγ hs) (hTan_den_pos hα hα' hβ hβ' hγ hγ')

theorem hTan_pos (hα : 0 < α) (hα' : α ≤ Real.pi / 2) (hβ : 0 < β) (hβ' : β ≤ Real.pi / 2)
    (hγ : 0 < γ) (hγ' : γ ≤ Real.pi / 2) (hs : α + β + γ < Real.pi) : 0 < hTan α β γ :=
  div_pos (Real.sqrt_pos.2 (hDelta_pos hα hα' hβ hβ' hγ hγ' hs))
    (hTan_den_pos hα hα' hβ hβ' hγ hγ')

theorem hTan_sq (hα : 0 < α) (hα' : α ≤ Real.pi / 2) (hβ : 0 < β) (hβ' : β ≤ Real.pi / 2)
    (hγ : 0 < γ) (hγ' : γ ≤ Real.pi / 2) (hs : α + β + γ < Real.pi) :
    hTan α β γ ^ 2 = (Real.cos γ + Real.cos (α + β)) / (Real.cos γ + Real.cos (α - β)) := by
  have hD := hTan_den_pos hα hα' hβ hβ' hγ hγ'
  rw [hTan, div_pow, Real.sq_sqrt (hDelta_pos hα hα' hβ hβ' hγ hγ' hs).le, hDelta_eq]
  field_simp

theorem hTan_lt_one (hα : 0 < α) (hα' : α ≤ Real.pi / 2) (hβ : 0 < β) (hβ' : β ≤ Real.pi / 2)
    (hγ : 0 < γ) (hγ' : γ ≤ Real.pi / 2) (hs : α + β + γ < Real.pi) : hTan α β γ < 1 := by
  have hD := hTan_den_pos hα hα' hβ hβ' hγ hγ'
  have hp := hTan_pos hα hα' hβ hβ' hγ hγ' hs
  have h2 := hTan_sq hα hα' hβ hβ' hγ hγ' hs
  have hsa := sin_pos_of_le hα hα'
  have hsb := sin_pos_of_le hβ hβ'
  have hlt : Real.cos (α + β) < Real.cos (α - β) := by
    rw [Real.cos_add, Real.cos_sub]
    nlinarith
  have : hTan α β γ ^ 2 < 1 := by
    rw [h2, div_lt_one hD]
    linarith
  nlinarith

theorem sqrt_sideCos_eq (hα : 0 < α) (hα' : α ≤ Real.pi / 2) (hβ : 0 < β)
    (hβ' : β ≤ Real.pi / 2) (hγ : 0 < γ) (hγ' : γ ≤ Real.pi / 2) (hs : α + β + γ < Real.pi) :
    Real.sqrt ((CompactShape.sideCos α β γ - 1) / (CompactShape.sideCos α β γ + 1)) =
      hTan α β γ := by
  have hsa := sin_pos_of_le hα hα'
  have hsb := sin_pos_of_le hβ hβ'
  have hD := hTan_den_pos hα hα' hβ hβ' hγ hγ'
  have e : (CompactShape.sideCos α β γ - 1) / (CompactShape.sideCos α β γ + 1) =
      hTan α β γ ^ 2 := by
    rw [hTan_sq hα hα' hβ hβ' hγ hγ' hs, CompactShape.sideCos]
    have hsab : Real.sin α * Real.sin β ≠ 0 := (mul_pos hsa hsb).ne'
    have e1 : (Real.cos γ + Real.cos α * Real.cos β) / (Real.sin α * Real.sin β) - 1 =
        (Real.cos γ + Real.cos (α + β)) / (Real.sin α * Real.sin β) := by
      rw [Real.cos_add, div_sub_one hsab]
      ring_nf
    have e2 : (Real.cos γ + Real.cos α * Real.cos β) / (Real.sin α * Real.sin β) + 1 =
        (Real.cos γ + Real.cos (α - β)) / (Real.sin α * Real.sin β) := by
      rw [Real.cos_sub, div_add_one hsab]
      ring_nf
    rw [e1, e2, div_div_div_cancel_right₀ hsab]
  rw [e, Real.sqrt_sq (hTan_pos hα hα' hβ hβ' hγ hγ' hs).le]

theorem exp_ofReal_mul_I_eq (x : ℝ) :
    exp ((x : ℂ) * I) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem exp_neg_ofReal_mul_I_eq (x : ℝ) :
    exp (-((x : ℂ) * I)) = (Real.cos x : ℂ) - (Real.sin x : ℂ) * I := by
  rw [show -((x : ℂ) * I) = ((-x : ℝ) : ℂ) * I by push_cast; ring, exp_ofReal_mul_I_eq,
    Real.cos_neg, Real.sin_neg]
  push_cast
  ring

theorem placement_re (α β γ : ℝ) :
    (Real.cos β + Real.cos (α - γ)) * (Real.cos γ + Real.cos (α - β)) * Real.cos γ -
        (Real.cos α + Real.cos (β - γ)) * (Real.cos γ + Real.cos (α - β)) +
        (Real.cos β + Real.cos (α - γ)) * (Real.cos α + Real.cos (β - γ)) * Real.cos α -
        hDelta α β γ * (Real.cos γ * Real.cos α + Real.sin γ * Real.sin α) = 0 := by
  rw [Real.cos_sub, Real.cos_sub, Real.cos_sub, hDelta]
  have ha := Real.sin_sq_add_cos_sq α
  have hb := Real.sin_sq_add_cos_sq β
  have hg := Real.sin_sq_add_cos_sq γ
  linear_combination (Real.cos γ * Real.sin β * Real.sin γ) * ha +
    (-(Real.sin α * Real.sin γ)) * hb + (Real.cos α * Real.sin α * Real.sin β) * hg

theorem placement_im (α β γ : ℝ) :
    (Real.cos β + Real.cos (α - γ)) * (Real.cos γ + Real.cos (α - β)) * Real.sin γ -
        (Real.cos β + Real.cos (α - γ)) * (Real.cos α + Real.cos (β - γ)) * Real.sin α -
        hDelta α β γ * (Real.sin γ * Real.cos α - Real.cos γ * Real.sin α) = 0 := by
  rw [Real.cos_sub, Real.cos_sub, Real.cos_sub, hDelta]
  have ha := Real.sin_sq_add_cos_sq α
  have hb := Real.sin_sq_add_cos_sq β
  have hg := Real.sin_sq_add_cos_sq γ
  linear_combination (-(Real.sin γ * (Real.cos α + Real.cos β * Real.cos γ))) * ha +
    (Real.sin α * (Real.cos α * Real.cos β + Real.cos γ)) * hg

theorem placement_alg {s Da Db Dc ca sa cg sg : ℝ} (hDa : Da ≠ 0) (hDb : Db ≠ 0) (hDc : Dc ≠ 0)
    (hre : Da * Dc * cg - Db * Dc + Da * Db * ca - s * s * (cg * ca + sg * sa) = 0)
    (him : Da * Dc * sg - Da * Db * sa - s * s * (sg * ca - cg * sa) = 0) :
    ((s / Db : ℝ) : ℂ) * ((cg : ℂ) + (sg : ℂ) * I) - ((s / Da : ℝ) : ℂ) =
      -(((s / Dc : ℝ) : ℂ) * ((ca : ℂ) - (sa : ℂ) * I)) *
        (1 - ((s / Da : ℝ) : ℂ) * (((s / Db : ℝ) : ℂ) * ((cg : ℂ) + (sg : ℂ) * I))) := by
  rw [← sub_eq_zero]
  have e : ((s / Db : ℝ) : ℂ) * ((cg : ℂ) + (sg : ℂ) * I) - ((s / Da : ℝ) : ℂ) -
      -(((s / Dc : ℝ) : ℂ) * ((ca : ℂ) - (sa : ℂ) * I)) *
        (1 - ((s / Da : ℝ) : ℂ) * (((s / Db : ℝ) : ℂ) * ((cg : ℂ) + (sg : ℂ) * I))) =
      ((s / (Da * Db * Dc) : ℝ) : ℂ) *
        (((Da * Dc * cg - Db * Dc + Da * Db * ca - s * s * (cg * ca + sg * sa) : ℝ) : ℂ) +
          ((Da * Dc * sg - Da * Db * sa - s * s * (sg * ca - cg * sa) : ℝ) : ℂ) * I) := by
    have hDa' : (Da : ℂ) ≠ 0 := by exact_mod_cast hDa
    have hDb' : (Db : ℂ) ≠ 0 := by exact_mod_cast hDb
    have hDc' : (Dc : ℂ) ≠ 0 := by exact_mod_cast hDc
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [e, hre, him]
  simp

theorem hTan_placement (hα : 0 < α) (hα' : α ≤ Real.pi / 2) (hβ : 0 < β)
    (hβ' : β ≤ Real.pi / 2) (hγ : 0 < γ) (hγ' : γ ≤ Real.pi / 2) (hs : α + β + γ < Real.pi) :
    (hTan β γ α : ℂ) * exp ((γ : ℂ) * I) - (hTan α γ β : ℂ) =
      -((hTan α β γ : ℂ) * exp (-((α : ℂ) * I))) *
        (1 - (hTan α γ β : ℂ) * ((hTan β γ α : ℂ) * exp ((γ : ℂ) * I))) := by
  have hDa := hTan_den_pos hα hα' hγ hγ' hβ hβ'
  have hDb := hTan_den_pos hβ hβ' hγ hγ' hα hα'
  have hDc := hTan_den_pos hα hα' hβ hβ' hγ hγ'
  have hΔ := hDelta_pos hα hα' hβ hβ' hγ hγ' hs
  have hss : Real.sqrt (hDelta α β γ) * Real.sqrt (hDelta α β γ) = hDelta α β γ :=
    Real.mul_self_sqrt hΔ.le
  have hA : hTan α γ β = Real.sqrt (hDelta α β γ) / (Real.cos β + Real.cos (α - γ)) := by
    rw [hTan, hDelta_swap_right]
  have hB : hTan β γ α = Real.sqrt (hDelta α β γ) / (Real.cos α + Real.cos (β - γ)) := by
    rw [hTan, show hDelta β γ α = hDelta α β γ by rw [hDelta_swap_right, hDelta_swap_left]]
  have hre := placement_re α β γ
  have him := placement_im α β γ
  rw [← hss] at hre him
  rw [hA, hB, hTan, exp_ofReal_mul_I_eq, exp_neg_ofReal_mul_I_eq]
  exact placement_alg hDa.ne' hDb.ne' hDc.ne' hre him

theorem key_of_placement {a b c α γ : ℝ}
    (h : (b : ℂ) * exp ((γ : ℂ) * I) - (a : ℂ) =
      -((c : ℂ) * exp (-((α : ℂ) * I))) * (1 - (a : ℂ) * ((b : ℂ) * exp ((γ : ℂ) * I)))) :
    c ^ 2 * (1 + a ^ 2 * b ^ 2 - 2 * a * b * Real.cos γ) =
      a ^ 2 + b ^ 2 - 2 * a * b * Real.cos γ := by
  have hn := congrArg normSq h
  rw [neg_mul, normSq_neg, map_mul, map_mul, normSq_ofReal, exp_ofReal_mul_I_eq,
    exp_neg_ofReal_mul_I_eq] at hn
  simp only [normSq_apply, sub_re, sub_im, mul_re, mul_im, add_re, add_im, ofReal_re,
    ofReal_im, I_re, I_im, one_re, one_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add,
    mul_one, zero_sub] at hn
  have hcs := Real.sin_sq_add_cos_sq α
  have hcs' := Real.sin_sq_add_cos_sq γ
  linear_combination (-1 : ℝ) * hn + b ^ 2 * hcs' -
    c ^ 2 * ((1 - a * b * Real.cos γ) ^ 2 + (a * b * Real.sin γ) ^ 2) * hcs -
    c ^ 2 * a ^ 2 * b ^ 2 * hcs'

theorem lt_oplus_of_key {a b c k : ℝ} (ha : 0 < a) (hb : 0 < b) (ha1 : a < 1) (hb1 : b < 1)
    (hc : 0 ≤ c) (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (key : c ^ 2 * (1 + a ^ 2 * b ^ 2 - 2 * a * b * k) = a ^ 2 + b ^ 2 - 2 * a * b * k) :
    c < oplus a b := by
  have hab0 : 0 < a * b := mul_pos ha hb
  have hab1 : a * b < 1 := by nlinarith
  have h1 : a * b * k ≤ a * b := by nlinarith
  have hpos : 0 < 1 + a ^ 2 * b ^ 2 - 2 * a * b * k := by nlinarith
  have hA : 0 < 1 - a ^ 2 := by nlinarith
  have hB : 0 < 1 - b ^ 2 := by nlinarith
  have e : (a + b) ^ 2 * (1 + a ^ 2 * b ^ 2 - 2 * a * b * k) -
      (a ^ 2 + b ^ 2 - 2 * a * b * k) * (1 + a * b) ^ 2 =
      2 * (a * b) * (1 - a ^ 2) * (1 - b ^ 2) * (1 + k) := by ring
  have hpos2 : 0 < 2 * (a * b) * (1 - a ^ 2) * (1 - b ^ 2) * (1 + k) := by positivity
  have hsq : (c * (1 + a * b)) ^ 2 < (a + b) ^ 2 := by
    have h2 : (c * (1 + a * b)) ^ 2 * (1 + a ^ 2 * b ^ 2 - 2 * a * b * k) <
        (a + b) ^ 2 * (1 + a ^ 2 * b ^ 2 - 2 * a * b * k) := by
      have : (c * (1 + a * b)) ^ 2 * (1 + a ^ 2 * b ^ 2 - 2 * a * b * k) =
          (a ^ 2 + b ^ 2 - 2 * a * b * k) * (1 + a * b) ^ 2 := by
        rw [mul_pow, mul_right_comm, key]
      linarith
    exact lt_of_mul_lt_mul_right h2 hpos.le
  have h3 : 0 ≤ c * (1 + a * b) := by positivity
  have h4 : c * (1 + a * b) < a + b := by nlinarith
  rw [oplus, lt_div_iff₀ (by positivity)]
  exact h4

theorem hTan_lt_oplus (hα : 0 < α) (hα' : α ≤ Real.pi / 2) (hβ : 0 < β)
    (hβ' : β ≤ Real.pi / 2) (hγ : 0 < γ) (hγ' : γ ≤ Real.pi / 2) (hs : α + β + γ < Real.pi) :
    hTan α β γ < oplus (hTan α γ β) (hTan β γ α) :=
  lt_oplus_of_key (hTan_pos hα hα' hγ hγ' hβ hβ' (by linarith))
    (hTan_pos hβ hβ' hγ hγ' hα hα' (by linarith))
    (hTan_lt_one hα hα' hγ hγ' hβ hβ' (by linarith))
    (hTan_lt_one hβ hβ' hγ hγ' hα hα' (by linarith))
    (hTan_pos hα hα' hβ hβ' hγ hγ' hs).le (cos_nonneg_of_le hγ hγ') (Real.cos_le_one γ)
    (key_of_placement (hTan_placement hα hα' hβ hβ' hγ hγ' hs))

end Angles

end HypFold

end GC.Seifert
