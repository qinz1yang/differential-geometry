import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSpec

/-!
# The spherical triangles of the compact fold: angles, sides and vertices

Lane CF-S, tier 1, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §1–2, errata of review 23). For a spherical
`CompactShape` (`Σ 1/pᵢ > 1`) the chart is the stereographic one, `eps = -1`, and the disc
coordinate is `disc v z = (z - v)/(1 + v̄ z)`, a rotation of the sphere defined off the antipode
`-1/v̄` of `v`.

Every spherical shape has an order `2` (`exists_p_eq_two_sph`), and with `θᵢ = π/pᵢ ∈ (0, π/2]`,
`θ₁ + θ₂ + θ₃ > π`. Writing `Eₖ = cos θₖ + cos θᵢ cos θⱼ + sin θᵢ sin θⱼ > 0` and
`Fₖ = sin θᵢ sin θⱼ - cos θᵢ cos θⱼ - cos θₖ > 0` (the second because `θᵢ + θⱼ > π - θₖ`), the
Gram quantity `Δ = 1 - Σ cos² θᵢ - 2 Π cos θᵢ` equals `Fₖ Eₖ` for each `k`, so `Δ > 0`, and the
side tangents of the spec are `tan(ℓᵢⱼ/2) = √Δ / Eₖ` (`tTwoThree_eq_sph`, …) with
`(1 - t²)/(1 + t²) = sideCos` (the spherical law of cosines) and `0 < t ≤ 1`; `t = 1` happens
exactly for the legs of `(2,2,n)`.

The two vertex identities (`rotTwo_vertexOne_sph`, `rotOne_vertexTwo_sph`) say that in the rotated
disc
coordinates the third vertex sits at `t₁₂` on the positive axis (seen from `v₂`) and at
`t₁₂ e^{iθ₁}` (seen from `v₁`): the triangle has the angles `θ₂`, `θ₁` there. They are polynomial
identities in the sines and cosines and `√Δ`, certified by Gröbner reduction.

The cyclic relabelling `sphRot` (orders `(p₂, p₃, p₁)`) has the same sides permuted; `rotOne`
identifies it with `σ` seen from `v₁` (`v₁ ↦ 0`, `v₃ ↦ t₁₃`, `v₂ ↦ t₁₂ e^{iθ₁}`), so facts proved
at the vertex `v₃ = 0` transfer to the other vertices.
-/

set_option autoImplicit false

noncomputable section

open Complex Set
open scoped ComplexConjugate

namespace GC.Seifert

/-! ### Rotations of the sphere in the stereographic chart -/

def sphMoeb (a z : ℂ) : ℂ := (z - a) / (1 + conj a * z)

def sphMoebInv (a w : ℂ) : ℂ := (w + a) / (1 - conj a * w)

theorem one_add_conj_mul_self_ne_sph (a : ℂ) : 1 + conj a * a ≠ 0 := by
  rw [← Complex.normSq_eq_conj_mul_self]
  have := Complex.normSq_nonneg a
  intro h
  have h' := congrArg Complex.re h
  simp only [add_re, one_re, ofReal_re, zero_re] at h'
  linarith

theorem sphMoeb_zero (w : ℂ) : sphMoeb 0 w = w := by
  simp [sphMoeb]

theorem sphMoeb_self (a : ℂ) : sphMoeb a a = 0 := by
  simp [sphMoeb]

theorem sphMoeb_sphMoebInv {a w : ℂ} (h : 1 - conj a * w ≠ 0) : sphMoeb a (sphMoebInv a w) = w := by
  have ha := one_add_conj_mul_self_ne_sph a
  unfold sphMoeb sphMoebInv
  have e : 1 + conj a * ((w + a) / (1 - conj a * w)) = (1 + conj a * a) / (1 - conj a * w) := by
    rw [mul_div_assoc', add_div' _ _ _ h]
    ring_nf
  have n : (w + a) / (1 - conj a * w) - a = w * (1 + conj a * a) / (1 - conj a * w) := by
    rw [div_sub' h]
    ring_nf
  rw [e, n, div_div_div_cancel_right₀ h, mul_div_assoc, div_self ha, mul_one]

theorem sphMoebInv_sphMoeb {a z : ℂ} (h : 1 + conj a * z ≠ 0) : sphMoebInv a (sphMoeb a z) = z := by
  have ha := one_add_conj_mul_self_ne_sph a
  unfold sphMoeb sphMoebInv
  have e : 1 - conj a * ((z - a) / (1 + conj a * z)) = (1 + conj a * a) / (1 + conj a * z) := by
    rw [mul_div_assoc', sub_div' h]
    ring_nf
  have n : (z - a) / (1 + conj a * z) + a = z * (1 + conj a * a) / (1 + conj a * z) := by
    rw [div_add' _ _ _ h]
    ring_nf
  rw [e, n, div_div_div_cancel_right₀ h, mul_div_assoc, div_self ha, mul_one]

theorem one_sub_conj_mul_sphMoeb {a z : ℂ} (h : 1 + conj a * z ≠ 0) :
    1 - conj a * sphMoeb a z = (1 + conj a * a) / (1 + conj a * z) := by
  unfold sphMoeb
  rw [mul_div_assoc', sub_div' h]
  ring_nf

theorem one_add_conj_mul_sphMoebInv {a w : ℂ} (h : 1 - conj a * w ≠ 0) :
    1 + conj a * sphMoebInv a w = (1 + conj a * a) / (1 - conj a * w) := by
  unfold sphMoebInv
  rw [mul_div_assoc', add_div' _ _ _ h]
  ring_nf

theorem one_add_mul_conj_ne_sph {a b : ℂ} (h : 1 + conj a * b ≠ 0) : 1 + a * conj b ≠ 0 := by
  intro h'
  apply h
  have := congrArg conj h'
  simpa [mul_comm] using this

theorem one_add_conj_sphMoeb_mul {a b z : ℂ} (h1 : 1 + conj a * z ≠ 0)
    (h2 : 1 + conj a * b ≠ 0) :
    1 + conj (sphMoeb a b) * sphMoeb a z =
      (1 + conj a * a) * (1 + conj b * z) / ((1 + a * conj b) * (1 + conj a * z)) := by
  have h2' := one_add_mul_conj_ne_sph h2
  unfold sphMoeb
  rw [map_div₀, map_sub, map_add, map_one, map_mul, Complex.conj_conj, div_mul_div_comm,
    add_div' _ _ _ (mul_ne_zero h2' h1)]
  congr 1
  ring

theorem sphMoeb_comp {a b z : ℂ} (h1 : 1 + conj a * z ≠ 0) (h2 : 1 + conj a * b ≠ 0)
    (h3 : 1 + conj b * z ≠ 0) :
    sphMoeb (sphMoeb a b) (sphMoeb a z) = sphMoeb b z * ((1 + a * conj b) / (1 + conj a * b)) := by
  have h2' := one_add_mul_conj_ne_sph h2
  have ha := one_add_conj_mul_self_ne_sph a
  have hd := one_add_conj_sphMoeb_mul h1 h2
  have n : sphMoeb a z - sphMoeb a b =
      (1 + conj a * a) * (z - b) / ((1 + conj a * z) * (1 + conj a * b)) := by
    unfold sphMoeb
    rw [div_sub_div _ _ h1 h2]
    congr 1
    ring
  rw [sphMoeb, hd, n, div_div_div_eq, sphMoeb, div_mul_div_comm]
  rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero h1 h2) (mul_ne_zero ha h3))
    (mul_ne_zero h3 h2)]
  ring

theorem norm_one_add_div_conj_sph {c : ℂ} (h : 1 + conj c ≠ 0) :
    ‖(1 + c) / (1 + conj c)‖ = 1 := by
  have e : 1 + conj c = conj (1 + c) := by simp
  have h' : 1 + c ≠ 0 := by
    intro h0
    apply h
    rw [e, h0, map_zero]
  rw [e, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 h')]

theorem norm_sphMoeb_comp {a b z : ℂ} (h1 : 1 + conj a * z ≠ 0) (h2 : 1 + conj a * b ≠ 0)
    (h3 : 1 + conj b * z ≠ 0) :
    ‖sphMoeb (sphMoeb a b) (sphMoeb a z)‖ = ‖sphMoeb b z‖ := by
  rw [sphMoeb_comp h1 h2 h3, norm_mul]
  have e : conj (a * conj b) = conj a * b := by simp
  rw [← e, norm_one_add_div_conj_sph (by rw [e]; exact h2), mul_one]

theorem sphMoeb_mul_unit {u : ℂ} (hu : conj u * u = 1) (c w : ℂ) :
    sphMoeb (u * c) (u * w) = u * sphMoeb c w := by
  unfold sphMoeb
  rw [map_mul]
  have e : 1 + conj u * conj c * (u * w) = 1 + conj c * w := by
    linear_combination (conj c * w) * hu
  rw [e]
  ring

theorem norm_eq_one_of_conj_mul_sph {u : ℂ} (hu : conj u * u = 1) : ‖u‖ = 1 := by
  have h := congrArg Complex.re hu
  rw [← Complex.normSq_eq_conj_mul_self] at h
  simp only [ofReal_re, one_re] at h
  have h0 : 0 ≤ ‖u‖ := norm_nonneg u
  have : ‖u‖ ^ 2 = 1 := by rw [Complex.sq_norm]; exact h
  nlinarith

theorem norm_sphMoeb_mul_unit {u : ℂ} (hu : conj u * u = 1) (c w : ℂ) :
    ‖sphMoeb (u * c) (u * w)‖ = ‖sphMoeb c w‖ := by
  rw [sphMoeb_mul_unit hu, norm_mul, norm_eq_one_of_conj_mul_sph hu, one_mul]

theorem sphMoeb_conj (c w : ℂ) : sphMoeb (conj c) (conj w) = conj (sphMoeb c w) := by
  simp [sphMoeb, map_div₀]

theorem conj_exp_mul_exp_sph (θ : ℝ) : conj (exp ((θ : ℂ) * I)) * exp ((θ : ℂ) * I) = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring_nf
  exact Complex.exp_zero

theorem conj_neg_exp_mul_sph (θ : ℝ) :
    conj (-exp ((θ : ℂ) * I)) * -exp ((θ : ℂ) * I) = 1 := by
  rw [map_neg, neg_mul_neg]
  exact conj_exp_mul_exp_sph θ

namespace CompactShape

variable (σ : CompactShape)

/-! ### The cyclic relabelling -/

theorem angle_cond_rot_sph :
    (σ.curv = .hyperbolic ∧ (1 / σ.p₂ + 1 / σ.p₃ + 1 / σ.p₁ : ℝ) < 1) ∨
    (σ.curv = .flat ∧ (1 / σ.p₂ + 1 / σ.p₃ + 1 / σ.p₁ : ℝ) = 1) ∨
    (σ.curv = .spherical ∧ 1 < (1 / σ.p₂ + 1 / σ.p₃ + 1 / σ.p₁ : ℝ)) := by
  have e : (1 / σ.p₂ + 1 / σ.p₃ + 1 / σ.p₁ : ℝ) = 1 / σ.p₁ + 1 / σ.p₂ + 1 / σ.p₃ := by ring
  rw [e]
  exact σ.angle_cond

def sphRot : CompactShape where
  curv := σ.curv
  p₁ := σ.p₂
  p₂ := σ.p₃
  p₃ := σ.p₁
  two_le_p₁ := σ.two_le_p₂
  two_le_p₂ := σ.two_le_p₃
  two_le_p₃ := σ.two_le_p₁
  angle_cond := σ.angle_cond_rot_sph

@[simp] theorem rot_curv_sph : σ.sphRot.curv = σ.curv := rfl

@[simp] theorem rot_θ₁_sph : σ.sphRot.θ₁ = σ.θ₂ := rfl

@[simp] theorem rot_θ₂_sph : σ.sphRot.θ₂ = σ.θ₃ := rfl

@[simp] theorem rot_θ₃_sph : σ.sphRot.θ₃ = σ.θ₁ := rfl

@[simp] theorem rot_eps_sph : σ.sphRot.eps = σ.eps := rfl

theorem sideCos_comm_sph (a b c : ℝ) : sideCos a b c = sideCos b a c := by
  unfold sideCos
  ring

theorem sideTan_comm_sph (a b c : ℝ) : σ.sideTan a b c = σ.sideTan b a c := by
  unfold sideTan
  rw [sideCos_comm_sph]

theorem rot_sideTan_sph (a b c : ℝ) : σ.sphRot.sideTan a b c = σ.sideTan a b c := rfl

/-! ### Angles -/

theorem θ₁_pos_sph : 0 < σ.θ₁ := EuclidShape.θ_pos_aux σ.two_le_p₁

theorem θ₂_pos_sph : 0 < σ.θ₂ := EuclidShape.θ_pos_aux σ.two_le_p₂

theorem θ₃_pos_sph : 0 < σ.θ₃ := EuclidShape.θ_pos_aux σ.two_le_p₃

theorem θ₁_le_sph : σ.θ₁ ≤ Real.pi / 2 := EuclidShape.θ_le_aux σ.two_le_p₁

theorem θ₂_le_sph : σ.θ₂ ≤ Real.pi / 2 := EuclidShape.θ_le_aux σ.two_le_p₂

theorem θ₃_le_sph : σ.θ₃ ≤ Real.pi / 2 := EuclidShape.θ_le_aux σ.two_le_p₃

theorem θ₁_mul_sph : σ.θ₁ * σ.p₁ = Real.pi := by
  have := EuclidShape.p_pos_aux σ.two_le_p₁
  unfold θ₁
  field_simp

theorem θ₂_mul_sph : σ.θ₂ * σ.p₂ = Real.pi := by
  have := EuclidShape.p_pos_aux σ.two_le_p₂
  unfold θ₂
  field_simp

theorem θ₃_mul_sph : σ.θ₃ * σ.p₃ = Real.pi := by
  have := EuclidShape.p_pos_aux σ.two_le_p₃
  unfold θ₃
  field_simp

theorem sin_θ₁_pos_sph : 0 < Real.sin σ.θ₁ := EuclidShape.sin_pos_aux σ.θ₁_pos_sph σ.θ₁_le_sph

theorem sin_θ₂_pos_sph : 0 < Real.sin σ.θ₂ := EuclidShape.sin_pos_aux σ.θ₂_pos_sph σ.θ₂_le_sph

theorem sin_θ₃_pos_sph : 0 < Real.sin σ.θ₃ := EuclidShape.sin_pos_aux σ.θ₃_pos_sph σ.θ₃_le_sph

theorem cos_θ₁_nonneg_sph : 0 ≤ Real.cos σ.θ₁ := EuclidShape.cos_nonneg_aux σ.θ₁_pos_sph σ.θ₁_le_sph

theorem cos_θ₂_nonneg_sph : 0 ≤ Real.cos σ.θ₂ := EuclidShape.cos_nonneg_aux σ.θ₂_pos_sph σ.θ₂_le_sph

theorem cos_θ₃_nonneg_sph : 0 ≤ Real.cos σ.θ₃ := EuclidShape.cos_nonneg_aux σ.θ₃_pos_sph σ.θ₃_le_sph

/-! ### Trigonometric quantities of the triangle -/

def sphDelta : ℝ := 1 - Real.cos σ.θ₁ ^ 2 - Real.cos σ.θ₂ ^ 2 - Real.cos σ.θ₃ ^ 2 -
  2 * Real.cos σ.θ₁ * Real.cos σ.θ₂ * Real.cos σ.θ₃

def sphE₁ : ℝ := Real.cos σ.θ₁ + Real.cos σ.θ₂ * Real.cos σ.θ₃ + Real.sin σ.θ₂ * Real.sin σ.θ₃

def sphE₂ : ℝ := Real.cos σ.θ₂ + Real.cos σ.θ₁ * Real.cos σ.θ₃ + Real.sin σ.θ₁ * Real.sin σ.θ₃

def sphE₃ : ℝ := Real.cos σ.θ₃ + Real.cos σ.θ₁ * Real.cos σ.θ₂ + Real.sin σ.θ₁ * Real.sin σ.θ₂

def sphF₁ : ℝ := Real.sin σ.θ₂ * Real.sin σ.θ₃ - Real.cos σ.θ₂ * Real.cos σ.θ₃ - Real.cos σ.θ₁

def sphF₂ : ℝ := Real.sin σ.θ₁ * Real.sin σ.θ₃ - Real.cos σ.θ₁ * Real.cos σ.θ₃ - Real.cos σ.θ₂

def sphF₃ : ℝ := Real.sin σ.θ₁ * Real.sin σ.θ₂ - Real.cos σ.θ₁ * Real.cos σ.θ₂ - Real.cos σ.θ₃

def sphTOneTwo : ℝ := σ.sideTan σ.θ₁ σ.θ₂ σ.θ₃

def sphTOneThree : ℝ := σ.sideTan σ.θ₁ σ.θ₃ σ.θ₂

def sphTTwoThree : ℝ := σ.sideTan σ.θ₂ σ.θ₃ σ.θ₁

theorem vertexOne_eq_sph : σ.vertexOne = (σ.sphTOneThree : ℂ) * exp (σ.θ₃ * I) := rfl

theorem vertexTwo_eq_sph : σ.vertexTwo = (σ.sphTTwoThree : ℂ) := rfl

theorem sphE₁_pos : 0 < σ.sphE₁ := by
  have := σ.cos_θ₁_nonneg_sph
  have := σ.cos_θ₂_nonneg_sph
  have := σ.cos_θ₃_nonneg_sph
  have := σ.sin_θ₂_pos_sph
  have := σ.sin_θ₃_pos_sph
  unfold sphE₁
  positivity

theorem sphE₂_pos : 0 < σ.sphE₂ := by
  have := σ.cos_θ₁_nonneg_sph
  have := σ.cos_θ₂_nonneg_sph
  have := σ.cos_θ₃_nonneg_sph
  have := σ.sin_θ₁_pos_sph
  have := σ.sin_θ₃_pos_sph
  unfold sphE₂
  positivity

theorem sphE₃_pos : 0 < σ.sphE₃ := by
  have := σ.cos_θ₁_nonneg_sph
  have := σ.cos_θ₂_nonneg_sph
  have := σ.cos_θ₃_nonneg_sph
  have := σ.sin_θ₁_pos_sph
  have := σ.sin_θ₂_pos_sph
  unfold sphE₃
  positivity

theorem sphDelta_eq_one : σ.sphDelta = σ.sphF₁ * σ.sphE₁ := by
  unfold sphDelta sphF₁ sphE₁
  linear_combination (-(Real.sin σ.θ₃ ^ 2)) * Real.cos_sq_add_sin_sq σ.θ₂ -
    (1 - Real.cos σ.θ₂ ^ 2) * Real.cos_sq_add_sin_sq σ.θ₃

theorem sphDelta_eq_two : σ.sphDelta = σ.sphF₂ * σ.sphE₂ := by
  unfold sphDelta sphF₂ sphE₂
  linear_combination (-(Real.sin σ.θ₃ ^ 2)) * Real.cos_sq_add_sin_sq σ.θ₁ -
    (1 - Real.cos σ.θ₁ ^ 2) * Real.cos_sq_add_sin_sq σ.θ₃

theorem sphDelta_eq_three : σ.sphDelta = σ.sphF₃ * σ.sphE₃ := by
  unfold sphDelta sphF₃ sphE₃
  linear_combination (-(Real.sin σ.θ₂ ^ 2)) * Real.cos_sq_add_sin_sq σ.θ₁ -
    (1 - Real.cos σ.θ₁ ^ 2) * Real.cos_sq_add_sin_sq σ.θ₂

theorem cos_add_lt_aux_sph {a b c : ℝ} (ha0 : 0 < a) (ha : a ≤ Real.pi / 2) (hb : b ≤ Real.pi / 2)
    (hc : c ≤ Real.pi / 2) (hsum : Real.pi < a + b + c) :
    0 < Real.sin b * Real.sin c - Real.cos b * Real.cos c - Real.cos a := by
  have e : Real.sin b * Real.sin c - Real.cos b * Real.cos c = -Real.cos (b + c) := by
    rw [Real.cos_add]
    ring
  have h : Real.cos (b + c) < Real.cos (Real.pi - a) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  rw [Real.cos_pi_sub] at h
  linarith

theorem t_sq_aux_sph {D E F : ℝ} (hE : 0 < E) (hD : D = F * E) (hF : 0 ≤ F) :
    (Real.sqrt D / E) ^ 2 = F / E := by
  rw [div_pow, Real.sq_sqrt (by rw [hD]; positivity), hD]
  field_simp

theorem t_le_one_aux_sph {t F E : ℝ} (ht : 0 < t) (hE : 0 < E) (h : t ^ 2 = F / E)
    (hFE : F ≤ E) : t ≤ 1 := by
  have : t ^ 2 ≤ 1 := by rw [h, div_le_one hE]; exact hFE
  nlinarith

theorem lawOfCosines_aux_sph {t F E a b c : ℝ} (hE : 0 < E) (hsa : 0 < Real.sin a)
    (hsb : 0 < Real.sin b) (h : t ^ 2 = F / E)
    (hEe : E = Real.cos c + Real.cos a * Real.cos b + Real.sin a * Real.sin b)
    (hFe : F = Real.sin a * Real.sin b - Real.cos a * Real.cos b - Real.cos c) :
    (1 - t ^ 2) / (1 + t ^ 2) = sideCos a b c := by
  have hss : 0 < Real.sin a * Real.sin b := mul_pos hsa hsb
  have hEF : E + F = 2 * (Real.sin a * Real.sin b) := by rw [hEe, hFe]; ring
  have hEF' : E - F = 2 * (Real.cos c + Real.cos a * Real.cos b) := by rw [hEe, hFe]; ring
  have e : (1 - t ^ 2) / (1 + t ^ 2) = (E - F) / (E + F) := by
    rw [h, div_eq_div_iff (by rw [← h]; positivity) (by rw [hEF]; positivity)]
    field_simp
  rw [e, hEF, hEF', sideCos]
  field_simp

/-! ### The vertex identities as polynomial identities -/

section VertexAlgebra

variable {ca sa cb sb cc sc D : ℝ}

theorem vertexA_re_sph (ha : ca ^ 2 + sa ^ 2 = 1) (hb : cb ^ 2 + sb ^ 2 = 1) (hc : cc ^ 2 + sc ^ 2 =
    1)
    (hD : D ^ 2 = 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 - 2 * ca * cb * cc)
    (h1 : ca + cb * cc + sb * sc ≠ 0) (h2 : cb + ca * cc + sa * sc ≠ 0)
    (h3 : cc + ca * cb + sa * sb ≠ 0) :
    D / (cb + ca * cc + sa * sc) * cc - D / (ca + cb * cc + sb * sc) +
      D / (cc + ca * cb + sa * sb) * (cb + D / (ca + cb * cc + sb * sc) *
        (D / (cb + ca * cc + sa * sc)) * (cb * cc + sb * sc)) = 0 := by
  set E1 := ca + cb * cc + sb * sc with hE1
  set E2 := cb + ca * cc + sa * sc with hE2
  set E3 := cc + ca * cb + sa * sb with hE3
  have key : cc * E1 * E3 - E2 * E3 + cb * E1 * E2 +
      (1 - ca ^ 2 - cb ^ 2 - cc ^ 2 - 2 * ca * cb * cc) * (cb * cc + sb * sc) = 0 := by
    rw [hE1, hE2, hE3]
    linear_combination (-sb * sc) * ha + (cc * sa * sc) * hb + (cb * sa * sb) * hc
  have e : D / E2 * cc - D / E1 + D / E3 * (cb + D / E1 * (D / E2) * (cb * cc + sb * sc)) =
      D * (cc * E1 * E3 - E2 * E3 + cb * E1 * E2 + D ^ 2 * (cb * cc + sb * sc)) /
        (E1 * E2 * E3) := by
    field_simp
    ring
  rw [e, hD, key]
  simp

theorem vertexA_im_sph (hb : cb ^ 2 + sb ^ 2 = 1) (hc : cc ^ 2 + sc ^ 2 = 1)
    (hD : D ^ 2 = 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 - 2 * ca * cb * cc)
    (h1 : ca + cb * cc + sb * sc ≠ 0) (h2 : cb + ca * cc + sa * sc ≠ 0)
    (h3 : cc + ca * cb + sa * sb ≠ 0) :
    D / (cb + ca * cc + sa * sc) * sc +
      D / (cc + ca * cb + sa * sb) * (-sb + D / (ca + cb * cc + sb * sc) *
        (D / (cb + ca * cc + sa * sc)) * (sc * cb - cc * sb)) = 0 := by
  set E1 := ca + cb * cc + sb * sc with hE1
  set E2 := cb + ca * cc + sa * sc with hE2
  set E3 := cc + ca * cb + sa * sb with hE3
  have key : sc * E1 * E3 + (-sb) * E1 * E2 +
      (1 - ca ^ 2 - cb ^ 2 - cc ^ 2 - 2 * ca * cb * cc) * (sc * cb - cc * sb) = 0 := by
    rw [hE1, hE2, hE3]
    linear_combination (-sc * (ca * cc + cb)) * hb + (sb * (ca * cb + cc)) * hc
  have e : D / E2 * sc + D / E3 * (-sb + D / E1 * (D / E2) * (sc * cb - cc * sb)) =
      D * (sc * E1 * E3 + (-sb) * E1 * E2 + D ^ 2 * (sc * cb - cc * sb)) / (E1 * E2 * E3) := by
    field_simp
    ring
  rw [e, hD, key]
  simp

theorem vertexB_re_sph (ha : ca ^ 2 + sa ^ 2 = 1) (hb : cb ^ 2 + sb ^ 2 = 1) (hc : cc ^ 2 + sc ^ 2 =
    1)
    (hD : D ^ 2 = 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 - 2 * ca * cb * cc)
    (h1 : ca + cb * cc + sb * sc ≠ 0) (h2 : cb + ca * cc + sa * sc ≠ 0)
    (h3 : cc + ca * cb + sa * sb ≠ 0) :
    D / (cb + ca * cc + sa * sc) * cc - D / (ca + cb * cc + sb * sc) -
      D / (cc + ca * cb + sa * sb) * ((ca * cc - sa * sc) + D / (ca + cb * cc + sb * sc) *
        (D / (cb + ca * cc + sa * sc)) * ca) = 0 := by
  set E1 := ca + cb * cc + sb * sc with hE1
  set E2 := cb + ca * cc + sa * sc with hE2
  set E3 := cc + ca * cb + sa * sb with hE3
  have key : cc * E1 * E3 - E2 * E3 - (ca * cc - sa * sc) * E1 * E2 -
      (1 - ca ^ 2 - cb ^ 2 - cc ^ 2 - 2 * ca * cb * cc) * ca = 0 := by
    rw [hE1, hE2, hE3]
    linear_combination (sc * (ca * sc + cb * cc * sc + sb * sc ^ 2 - sb)) * ha +
      (cc * sa * sc) * hb + (-ca ^ 3 - ca ^ 2 * cb * cc - ca ^ 2 * sb * sc + ca + cb * cc +
        cb * sa * sb + sb * sc) * hc
  have e : D / E2 * cc - D / E1 - D / E3 * ((ca * cc - sa * sc) + D / E1 * (D / E2) * ca) =
      D * (cc * E1 * E3 - E2 * E3 - (ca * cc - sa * sc) * E1 * E2 - D ^ 2 * ca) /
        (E1 * E2 * E3) := by
    field_simp
    ring
  rw [e, hD, key]
  simp

theorem vertexB_im_sph (ha : ca ^ 2 + sa ^ 2 = 1) (hb : cb ^ 2 + sb ^ 2 = 1) (hc : cc ^ 2 + sc ^ 2 =
    1)
    (hD : D ^ 2 = 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 - 2 * ca * cb * cc)
    (h1 : ca + cb * cc + sb * sc ≠ 0) (h2 : cb + ca * cc + sa * sc ≠ 0)
    (h3 : cc + ca * cb + sa * sb ≠ 0) :
    D / (cb + ca * cc + sa * sc) * sc -
      D / (cc + ca * cb + sa * sb) * ((sa * cc + ca * sc) + D / (ca + cb * cc + sb * sc) *
        (D / (cb + ca * cc + sa * sc)) * sa) = 0 := by
  set E1 := ca + cb * cc + sb * sc with hE1
  set E2 := cb + ca * cc + sa * sc with hE2
  set E3 := cc + ca * cb + sa * sb with hE3
  have key : sc * E1 * E3 - (sa * cc + ca * sc) * E1 * E2 -
      (1 - ca ^ 2 - cb ^ 2 - cc ^ 2 - 2 * ca * cb * cc) * sa = 0 := by
    rw [hE1, hE2, hE3]
    linear_combination (-cc * sc * (ca + cb * cc + sb * sc)) * ha + (sa * sc ^ 2) * hb +
      (-sa * (ca ^ 2 + ca * cb * cc + ca * sb * sc + cb ^ 2 - 1)) * hc
  have e : D / E2 * sc - D / E3 * ((sa * cc + ca * sc) + D / E1 * (D / E2) * sa) =
      D * (sc * E1 * E3 - (sa * cc + ca * sc) * E1 * E2 - D ^ 2 * sa) / (E1 * E2 * E3) := by
    field_simp
    ring
  rw [e, hD, key]
  simp

theorem excess_re_sph (ha : ca ^ 2 + sa ^ 2 = 1) (hb : cb ^ 2 + sb ^ 2 = 1) (hc : cc ^ 2 + sc ^ 2 =
    1)
    (hD : D ^ 2 = 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 - 2 * ca * cb * cc)
    (h1 : ca + cb * cc + sb * sc ≠ 0) (h2 : cb + ca * cc + sa * sc ≠ 0) :
    1 + D / (ca + cb * cc + sb * sc) * (D / (cb + ca * cc + sa * sc)) * cc +
      ((ca * cb - sa * sb) * cc - (sa * cb + ca * sb) * sc) +
      D / (ca + cb * cc + sb * sc) * (D / (cb + ca * cc + sa * sc)) * (ca * cb - sa * sb) = 0 := by
  set E1 := ca + cb * cc + sb * sc with hE1
  set E2 := cb + ca * cc + sa * sc with hE2
  have key : E1 * E2 * (1 + ((ca * cb - sa * sb) * cc - (sa * cb + ca * sb) * sc)) +
      (1 - ca ^ 2 - cb ^ 2 - cc ^ 2 - 2 * ca * cb * cc) * (cc + (ca * cb - sa * sb)) = 0 := by
    rw [hE1, hE2]
    linear_combination (-sc * (cb * sc + cc * sb) * (ca + cb * cc + sb * sc)) * ha +
      (-sc * (ca * cb * sc + ca * cc ^ 2 * sa + ca * sa * sc ^ 2 + cb * cc * sa + cc * sc)) * hb +
      (ca ^ 3 * cb + ca ^ 2 * cb ^ 2 * cc + ca ^ 2 * cb * sb * sc - ca ^ 2 * sa * sb + ca * cb ^ 3 +
        ca * cb ^ 2 * sa * sc - ca * cb * cc * sa * sb - 2 * ca * cb - ca * sa * sc -
        cb ^ 2 * sa * sb - cb * sb * sc - cc + sa * sb) * hc
  have e : 1 + D / E1 * (D / E2) * cc + ((ca * cb - sa * sb) * cc - (sa * cb + ca * sb) * sc) +
      D / E1 * (D / E2) * (ca * cb - sa * sb) =
      (E1 * E2 * (1 + ((ca * cb - sa * sb) * cc - (sa * cb + ca * sb) * sc)) +
        D ^ 2 * (cc + (ca * cb - sa * sb))) / (E1 * E2) := by
    field_simp
    ring
  rw [e, hD, key]
  simp

theorem excess_im_sph (ha : ca ^ 2 + sa ^ 2 = 1) (hb : cb ^ 2 + sb ^ 2 = 1) (hc : cc ^ 2 + sc ^ 2 =
    1)
    (hD : D ^ 2 = 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 - 2 * ca * cb * cc)
    (h1 : ca + cb * cc + sb * sc ≠ 0) (h2 : cb + ca * cc + sa * sc ≠ 0) :
    D / (ca + cb * cc + sb * sc) * (D / (cb + ca * cc + sa * sc)) * sc +
      ((sa * cb + ca * sb) * cc + (ca * cb - sa * sb) * sc) +
      D / (ca + cb * cc + sb * sc) * (D / (cb + ca * cc + sa * sc)) * (sa * cb + ca * sb) = 0 := by
  set E1 := ca + cb * cc + sb * sc with hE1
  set E2 := cb + ca * cc + sa * sc with hE2
  have key : E1 * E2 * ((sa * cb + ca * sb) * cc + (ca * cb - sa * sb) * sc) +
      (1 - ca ^ 2 - cb ^ 2 - cc ^ 2 - 2 * ca * cb * cc) * (sc + (sa * cb + ca * sb)) = 0 := by
    rw [hE1, hE2]
    linear_combination (sc * (cb * cc - sb * sc) * (ca + cb * cc + sb * sc)) * ha +
      (sc * (ca ^ 2 * cc ^ 2 + ca ^ 2 * sc ^ 2 + ca * cb * cc - cb * sa * sc - sc ^ 2)) * hb +
      (ca ^ 3 * sb - ca ^ 2 * cb ^ 2 * sc + ca ^ 2 * cb * cc * sb + ca ^ 2 * cb * sa + ca ^ 2 * sc +
        ca * cb ^ 2 * cc * sa + ca * cb ^ 2 * sb + ca * cb * sa * sb * sc - ca * sb + cb ^ 3 * sa +
        cb ^ 2 * sc - cb * sa - sc) * hc
  have e : D / E1 * (D / E2) * sc + ((sa * cb + ca * sb) * cc + (ca * cb - sa * sb) * sc) +
      D / E1 * (D / E2) * (sa * cb + ca * sb) =
      (E1 * E2 * ((sa * cb + ca * sb) * cc + (ca * cb - sa * sb) * sc) +
        D ^ 2 * (sc + (sa * cb + ca * sb))) / (E1 * E2) := by
    field_simp
    ring
  rw [e, hD, key]
  simp

theorem wallTwo_key_x_sph (ha : ca ^ 2 + sa ^ 2 = 1) (hb : cb ^ 2 + sb ^ 2 = 1)
    (hc : cc ^ 2 + sc ^ 2 = 1) :
    -sa*(ca*cc + cb + sa*sc)*(ca^2 + 2*ca*cb*cc + cb^2 + cc^2 + (ca + cb*cc + sb*sc)^2 - 1) +
      (-(-ca*sc + cc*sa)*(-ca^2 - 2*ca*cb*cc - cb^2 - cc^2 + 1) + (ca*sc + cc*sa)*(ca*cc + cb +
      sa*sc)^2)*(ca + cb*cc + sb*sc) = 0 := by
  linear_combination (sc*(2*ca^2*cc^2 + ca^2*sc^2 - 2*ca^2 + 2*ca*cb*cc^3 + ca*cb*cc*sc^2 -
    2*ca*cb*cc + 2*ca*cc^2*sb*sc + ca*cc*sa*sc + ca*sb*sc^3 - 2*ca*sb*sc + cb^2*cc^2 - cb^2 +
    cb*cc^2*sa*sc - cc^2 + cc*sa*sb*sc^2 - sb^2*sc^2 + 1)) * ha +
    (sc^2*(ca^2*sc - ca*cc*sa - cb*sa - sc)) * hb +
    (-ca^4*sc - ca^3*cb*cc*sc + ca^3*cc*sa - ca^3*sb*sc^2 - ca^2*cb^2*sc + ca^2*cb*cc^2*sa +
      2*ca^2*cb*sa + ca^2*cc*sa*sb*sc + 2*ca^2*sc + 3*ca*cb^2*cc*sa + ca*cb*cc*sc + 2*ca*cb*sa*sb*sc
      + ca*sb*sc^2 + cb^3*sa + cb^2*sc + cb*cc^2*sa - cb*sa + cc*sa*sb*sc - sc) * hc

theorem wallTwo_key_y_sph (ha : ca ^ 2 + sa ^ 2 = 1) (hb : cb ^ 2 + sb ^ 2 = 1)
    (hc : cc ^ 2 + sc ^ 2 = 1) :
    cb*sa*(ca*cc + cb + sa*sc)*(-ca^2 - 2*ca*cb*cc - cb^2 - cc^2 + (ca + cb*cc + sb*sc)^2 + 1) +
      sb*((ca*cc - sa*sc)*(ca*cc + cb + sa*sc)^2 + (ca*cc + sa*sc)*(-ca^2 - 2*ca*cb*cc - cb^2 - cc^2
      + 1))*(ca + cb*cc + sb*sc) = 0 := by
  linear_combination (-sc*(ca^2*cc*sb*sc + ca*cb*cc^2*sb*sc + ca*cc*sb^2*sc^2 + ca*sa*sb*sc^2 -
    cb^3*cc^2 + cb^3 + cb*cc^2 + cb*cc*sa*sb*sc^2 + cb*sb^2*sc^2 - cb + sa*sb^2*sc^3)) * ha +
    (sc*(ca^3*cc^3 + ca^3*cc*sc^2 - ca^3*cc + ca^2*cb*sc^2 + ca^2*cc^2*sa*sc + ca^2*sa*sc^3 -
      ca^2*sa*sc - ca*cb*cc*sa*sc - ca*cc^3 - ca*cc*sc^2 + ca*cc - cb^2*sa*sc - cb*sc^2 - cc^2*sa*sc
      - sa*sc^3 + sa*sc)) * hb +
    (ca^4*cc*sb - ca^3*cb^2*cc*sc + ca^3*cb*cc^2*sb + ca^3*cc*sc + ca^3*sa*sb*sc - ca^2*cb^3*sc -
      ca^2*cb^2*sa*sc^2 + ca^2*cb*cc*sa*sb*sc + ca^2*cb*sc - ca^2*cc*sb + ca^2*sa*sc^2 +
      ca*cb^3*cc*sa + ca*cb^2*cc*sc - ca*cb*cc^2*sb - ca*cb*cc*sa - ca*cc*sc - ca*sa*sb*sc + cb^4*sa
      + cb^3*sc + cb^2*sa*sc^2 - cb^2*sa - cb*cc*sa*sb*sc - cb*sc - sa*sc^2) * hc


theorem wallTwo_x_sph (ha : ca ^ 2 + sa ^ 2 = 1) (hb : cb ^ 2 + sb ^ 2 = 1) (hc : cc ^ 2 + sc ^ 2 =
    1)
    (hD : D ^ 2 = 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 - 2 * ca * cb * cc)
    (h1 : ca + cb * cc + sb * sc ≠ 0) (h2 : cb + ca * cc + sa * sc ≠ 0) :
    ((sa * cc + ca * sc) - (D / (cb + ca * cc + sa * sc)) ^ 2 * (sa * cc - ca * sc)) *
      (D / (ca + cb * cc + sb * sc)) =
      D / (cb + ca * cc + sa * sc) * sa * (1 - (D / (ca + cb * cc + sb * sc)) ^ 2) := by
  have key := wallTwo_key_x_sph ha hb hc
  set E1 := ca + cb * cc + sb * sc with hE1
  set E2 := cb + ca * cc + sa * sc with hE2
  rw [← sub_eq_zero]
  have e : ((sa * cc + ca * sc) - (D / E2) ^ 2 * (sa * cc - ca * sc)) * (D / E1) -
      D / E2 * sa * (1 - (D / E1) ^ 2) =
      D * (((sa * cc + ca * sc) * E2 ^ 2 - D ^ 2 * (sa * cc - ca * sc)) * E1 -
        sa * E2 * (E1 ^ 2 - D ^ 2)) / (E1 ^ 2 * E2 ^ 2) := by
    field_simp
  rw [e, hD]
  rw [div_eq_zero_iff]
  left
  rw [mul_eq_zero]
  right
  linear_combination key

theorem wallTwo_y_sph (ha : ca ^ 2 + sa ^ 2 = 1) (hb : cb ^ 2 + sb ^ 2 = 1) (hc : cc ^ 2 + sc ^ 2 =
    1)
    (hD : D ^ 2 = 1 - ca ^ 2 - cb ^ 2 - cc ^ 2 - 2 * ca * cb * cc)
    (h1 : ca + cb * cc + sb * sc ≠ 0) (h2 : cb + ca * cc + sa * sc ≠ 0) :
    ((ca * cc - sa * sc) + (D / (cb + ca * cc + sa * sc)) ^ 2 * (ca * cc + sa * sc)) *
      (D / (ca + cb * cc + sb * sc)) * sb =
      -(D / (cb + ca * cc + sa * sc) * sa * cb * (1 + (D / (ca + cb * cc + sb * sc)) ^ 2)) := by
  have key := wallTwo_key_y_sph ha hb hc
  set E1 := ca + cb * cc + sb * sc with hE1
  set E2 := cb + ca * cc + sa * sc with hE2
  rw [← sub_eq_zero]
  have e : ((ca * cc - sa * sc) + (D / E2) ^ 2 * (ca * cc + sa * sc)) * (D / E1) * sb -
      -(D / E2 * sa * cb * (1 + (D / E1) ^ 2)) =
      D * (((ca * cc - sa * sc) * E2 ^ 2 + D ^ 2 * (ca * cc + sa * sc)) * E1 * sb +
        sa * cb * E2 * (E1 ^ 2 + D ^ 2)) / (E1 ^ 2 * E2 ^ 2) := by
    field_simp
    ring
  rw [e, hD]
  rw [div_eq_zero_iff]
  left
  rw [mul_eq_zero]
  right
  linear_combination key

end VertexAlgebra

theorem exp_neg_ofReal_mul_I_sph (θ : ℝ) : exp (-((θ : ℂ) * I)) = exp (((-θ : ℝ) : ℂ) * I) := by
  push_cast
  ring_nf

theorem exp_mul_exp_neg_sph (θ : ℝ) : exp ((θ : ℂ) * I) * exp (-((θ : ℂ) * I)) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

theorem conj_exp_ofReal_mul_I_sph (θ : ℝ) : conj (exp ((θ : ℂ) * I)) = exp (-((θ : ℂ) * I)) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring_nf

theorem conj_vertexOne_sph : conj σ.vertexOne = (σ.sphTOneThree : ℂ) * exp (-((σ.θ₃ : ℂ) * I)) := by
  rw [vertexOne_eq_sph, map_mul, Complex.conj_ofReal, conj_exp_ofReal_mul_I_sph]

theorem conj_vertexTwo_sph : conj σ.vertexTwo = σ.vertexTwo := by
  rw [vertexTwo_eq_sph, Complex.conj_ofReal]

/-! ### Spherical shapes -/

section Spherical

variable {σ}
variable (hs : σ.curv = .spherical)
include hs

theorem eps_sph : σ.eps = -1 := by
  unfold eps
  rw [hs]
  rfl

theorem rot_spherical : σ.sphRot.curv = .spherical := hs

theorem sum_inv_sph : 1 < (1 / σ.p₁ + 1 / σ.p₂ + 1 / σ.p₃ : ℝ) := by
  rcases σ.angle_cond with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, h⟩
  · rw [hs] at h'
    exact absurd h' (by decide)
  · rw [hs] at h'
    exact absurd h' (by decide)
  · exact h

theorem θ_sum_gt_sph : Real.pi < σ.θ₁ + σ.θ₂ + σ.θ₃ := by
  have h := sum_inv_sph hs
  unfold θ₁ θ₂ θ₃
  have : Real.pi / σ.p₁ + Real.pi / σ.p₂ + Real.pi / σ.p₃ =
      Real.pi * (1 / σ.p₁ + 1 / σ.p₂ + 1 / σ.p₃) := by ring
  rw [this]
  have := Real.pi_pos
  nlinarith

theorem exists_p_eq_two_sph : σ.p₁ = 2 ∨ σ.p₂ = 2 ∨ σ.p₃ = 2 := by
  by_contra h
  simp only [not_or] at h
  have h1 : (3 : ℝ) ≤ σ.p₁ := by exact_mod_cast (show 3 ≤ σ.p₁ by have := σ.two_le_p₁; omega)
  have h2 : (3 : ℝ) ≤ σ.p₂ := by exact_mod_cast (show 3 ≤ σ.p₂ by have := σ.two_le_p₂; omega)
  have h3 : (3 : ℝ) ≤ σ.p₃ := by exact_mod_cast (show 3 ≤ σ.p₃ by have := σ.two_le_p₃; omega)
  have e1 : (1 : ℝ) / σ.p₁ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h1
  have e2 : (1 : ℝ) / σ.p₂ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h2
  have e3 : (1 : ℝ) / σ.p₃ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3
  have := sum_inv_sph hs
  linarith

theorem sphF₁_pos : 0 < σ.sphF₁ :=
  cos_add_lt_aux_sph σ.θ₁_pos_sph σ.θ₁_le_sph σ.θ₂_le_sph σ.θ₃_le_sph (θ_sum_gt_sph hs)

theorem sphF₂_pos : 0 < σ.sphF₂ :=
  cos_add_lt_aux_sph σ.θ₂_pos_sph σ.θ₂_le_sph σ.θ₁_le_sph σ.θ₃_le_sph
    (by linarith [θ_sum_gt_sph hs])

theorem sphF₃_pos : 0 < σ.sphF₃ :=
  cos_add_lt_aux_sph σ.θ₃_pos_sph σ.θ₃_le_sph σ.θ₁_le_sph σ.θ₂_le_sph
    (by linarith [θ_sum_gt_sph hs])

theorem sphDelta_pos : 0 < σ.sphDelta := by
  rw [sphDelta_eq_one]
  exact mul_pos (sphF₁_pos hs) σ.sphE₁_pos

theorem sideTan_sph_aux {a b c F E : ℝ} (hE : 0 < E) (hsa : 0 < Real.sin a)
    (hsb : 0 < Real.sin b)
    (hEe : E = Real.cos c + Real.cos a * Real.cos b + Real.sin a * Real.sin b)
    (hFe : F = Real.sin a * Real.sin b - Real.cos a * Real.cos b - Real.cos c) :
    σ.sideTan a b c = Real.sqrt (F * E) / E := by
  unfold sideTan
  rw [hs]
  have hss : 0 < Real.sin a * Real.sin b := mul_pos hsa hsb
  have h1 : 1 - sideCos a b c = F / (Real.sin a * Real.sin b) := by
    unfold sideCos
    rw [hFe]
    field_simp
    ring
  have h2 : 1 + sideCos a b c = E / (Real.sin a * Real.sin b) := by
    unfold sideCos
    rw [hEe]
    field_simp
    ring
  have e : (1 - sideCos a b c) / (1 + sideCos a b c) = F * E / E ^ 2 := by
    rw [h1, h2]
    field_simp
  dsimp only
  rw [e, Real.sqrt_div' _ (sq_nonneg E), Real.sqrt_sq hE.le]

theorem tTwoThree_eq_sph : σ.sphTTwoThree = Real.sqrt σ.sphDelta / σ.sphE₁ := by
  rw [sphDelta_eq_one]
  exact sideTan_sph_aux hs σ.sphE₁_pos σ.sin_θ₂_pos_sph σ.sin_θ₃_pos_sph rfl rfl

theorem tOneThree_eq_sph : σ.sphTOneThree = Real.sqrt σ.sphDelta / σ.sphE₂ := by
  rw [sphDelta_eq_two]
  exact sideTan_sph_aux hs σ.sphE₂_pos σ.sin_θ₁_pos_sph σ.sin_θ₃_pos_sph rfl rfl

theorem tOneTwo_eq_sph : σ.sphTOneTwo = Real.sqrt σ.sphDelta / σ.sphE₃ := by
  rw [sphDelta_eq_three]
  exact sideTan_sph_aux hs σ.sphE₃_pos σ.sin_θ₁_pos_sph σ.sin_θ₂_pos_sph rfl rfl

theorem tTwoThree_pos_sph : 0 < σ.sphTTwoThree := by
  rw [tTwoThree_eq_sph hs]
  exact div_pos (Real.sqrt_pos.2 (sphDelta_pos hs)) σ.sphE₁_pos

theorem tOneThree_pos_sph : 0 < σ.sphTOneThree := by
  rw [tOneThree_eq_sph hs]
  exact div_pos (Real.sqrt_pos.2 (sphDelta_pos hs)) σ.sphE₂_pos

theorem tOneTwo_pos_sph : 0 < σ.sphTOneTwo := by
  rw [tOneTwo_eq_sph hs]
  exact div_pos (Real.sqrt_pos.2 (sphDelta_pos hs)) σ.sphE₃_pos

theorem tTwoThree_sq_sph : σ.sphTTwoThree ^ 2 = σ.sphF₁ / σ.sphE₁ := by
  rw [tTwoThree_eq_sph hs]
  exact t_sq_aux_sph σ.sphE₁_pos σ.sphDelta_eq_one (sphF₁_pos hs).le

theorem tOneThree_sq_sph : σ.sphTOneThree ^ 2 = σ.sphF₂ / σ.sphE₂ := by
  rw [tOneThree_eq_sph hs]
  exact t_sq_aux_sph σ.sphE₂_pos σ.sphDelta_eq_two (sphF₂_pos hs).le

theorem tOneTwo_sq_sph : σ.sphTOneTwo ^ 2 = σ.sphF₃ / σ.sphE₃ := by
  rw [tOneTwo_eq_sph hs]
  exact t_sq_aux_sph σ.sphE₃_pos σ.sphDelta_eq_three (sphF₃_pos hs).le

theorem tTwoThree_le_one_sph : σ.sphTTwoThree ≤ 1 := by
  refine t_le_one_aux_sph (tTwoThree_pos_sph hs) σ.sphE₁_pos (tTwoThree_sq_sph hs) ?_
  have := σ.cos_θ₁_nonneg_sph
  have := mul_nonneg σ.cos_θ₂_nonneg_sph σ.cos_θ₃_nonneg_sph
  unfold sphF₁ sphE₁
  linarith

theorem tOneThree_le_one_sph : σ.sphTOneThree ≤ 1 := by
  refine t_le_one_aux_sph (tOneThree_pos_sph hs) σ.sphE₂_pos (tOneThree_sq_sph hs) ?_
  have := σ.cos_θ₂_nonneg_sph
  have := mul_nonneg σ.cos_θ₁_nonneg_sph σ.cos_θ₃_nonneg_sph
  unfold sphF₂ sphE₂
  linarith

theorem tOneTwo_le_one_sph : σ.sphTOneTwo ≤ 1 := by
  refine t_le_one_aux_sph (tOneTwo_pos_sph hs) σ.sphE₃_pos (tOneTwo_sq_sph hs) ?_
  have := σ.cos_θ₃_nonneg_sph
  have := mul_nonneg σ.cos_θ₁_nonneg_sph σ.cos_θ₂_nonneg_sph
  unfold sphF₃ sphE₃
  linarith

theorem lawOfCosines_twoThree_sph :
    (1 - σ.sphTTwoThree ^ 2) / (1 + σ.sphTTwoThree ^ 2) = sideCos σ.θ₂ σ.θ₃ σ.θ₁ :=
  lawOfCosines_aux_sph σ.sphE₁_pos σ.sin_θ₂_pos_sph σ.sin_θ₃_pos_sph (tTwoThree_sq_sph hs) rfl rfl

theorem lawOfCosines_oneThree_sph :
    (1 - σ.sphTOneThree ^ 2) / (1 + σ.sphTOneThree ^ 2) = sideCos σ.θ₁ σ.θ₃ σ.θ₂ :=
  lawOfCosines_aux_sph σ.sphE₂_pos σ.sin_θ₁_pos_sph σ.sin_θ₃_pos_sph (tOneThree_sq_sph hs) rfl rfl

theorem lawOfCosines_oneTwo_sph :
    (1 - σ.sphTOneTwo ^ 2) / (1 + σ.sphTOneTwo ^ 2) = sideCos σ.θ₁ σ.θ₂ σ.θ₃ :=
  lawOfCosines_aux_sph σ.sphE₃_pos σ.sin_θ₁_pos_sph σ.sin_θ₂_pos_sph (tOneTwo_sq_sph hs) rfl rfl

/-! ### Disc coordinates and the vertex identities -/

theorem disc_sph (v z : ℂ) : σ.disc v z = sphMoeb v z := by
  rw [disc, eps_sph hs, sphMoeb]
  push_cast
  ring

theorem discInv_sph (v w : ℂ) : σ.discInv v w = sphMoebInv v w := by
  rw [discInv, eps_sph hs, sphMoebInv]
  push_cast
  ring

theorem trig_hyps_sph :
    Real.cos σ.θ₁ ^ 2 + Real.sin σ.θ₁ ^ 2 = 1 ∧ Real.cos σ.θ₂ ^ 2 + Real.sin σ.θ₂ ^ 2 = 1 ∧
      Real.cos σ.θ₃ ^ 2 + Real.sin σ.θ₃ ^ 2 = 1 ∧
      Real.sqrt σ.sphDelta ^ 2 = 1 - Real.cos σ.θ₁ ^ 2 - Real.cos σ.θ₂ ^ 2 -
        Real.cos σ.θ₃ ^ 2 - 2 * Real.cos σ.θ₁ * Real.cos σ.θ₂ * Real.cos σ.θ₃ :=
  ⟨Real.cos_sq_add_sin_sq _, Real.cos_sq_add_sin_sq _, Real.cos_sq_add_sin_sq _,
    Real.sq_sqrt (sphDelta_pos hs).le⟩

theorem vertexOne_sub_vertexTwo_sph : σ.vertexOne - σ.vertexTwo =
    -(exp (-((σ.θ₂ : ℂ) * I)) * σ.sphTOneTwo * (1 + σ.vertexTwo * σ.vertexOne)) := by
  obtain ⟨ha, hb, hc, hD⟩ := trig_hyps_sph hs
  have h1 := σ.sphE₁_pos.ne'
  have h2 := σ.sphE₂_pos.ne'
  have h3 := σ.sphE₃_pos.ne'
  rw [vertexOne_eq_sph, vertexTwo_eq_sph, tOneThree_eq_sph hs, tTwoThree_eq_sph hs, tOneTwo_eq_sph
      hs,
    exp_neg_ofReal_mul_I_sph]
  unfold sphE₁ sphE₂ sphE₃ at *
  apply Complex.ext
  · simp only [sub_re, neg_re, mul_re, add_re, mul_im, add_im, ofReal_re, ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, one_re, one_im, Real.cos_neg,
      Real.sin_neg]
    linear_combination vertexA_re_sph ha hb hc hD h1 h2 h3
  · simp only [sub_im, neg_im, mul_re, add_re, mul_im, add_im, ofReal_re, ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, one_re, one_im, Real.cos_neg,
      Real.sin_neg]
    linear_combination vertexA_im_sph hb hc hD h1 h2 h3

theorem vertexOne_sub_vertexTwo_sph' : σ.vertexOne - σ.vertexTwo =
    σ.sphTOneTwo * (exp (((σ.θ₁ + σ.θ₃ : ℝ) : ℂ) * I) +
      (σ.sphTTwoThree * σ.sphTOneThree : ℝ) * exp ((σ.θ₁ : ℂ) * I)) := by
  obtain ⟨ha, hb, hc, hD⟩ := trig_hyps_sph hs
  have h1 := σ.sphE₁_pos.ne'
  have h2 := σ.sphE₂_pos.ne'
  have h3 := σ.sphE₃_pos.ne'
  rw [vertexOne_eq_sph, vertexTwo_eq_sph, tOneThree_eq_sph hs, tTwoThree_eq_sph hs, tOneTwo_eq_sph
      hs]
  unfold sphE₁ sphE₂ sphE₃ at *
  apply Complex.ext
  · simp only [sub_re, mul_re, add_re, mul_im, add_im, ofReal_re, ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_add]
    linear_combination vertexB_re_sph ha hb hc hD h1 h2 h3
  · simp only [sub_im, mul_re, add_re, mul_im, add_im, ofReal_re, ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.sin_add]
    linear_combination vertexB_im_sph ha hb hc hD h1 h2 h3

/-! ### The rotated disc coordinates at the vertices -/

theorem rotOne_apply_sph (z : ℂ) : σ.rotOne z = -(exp (-((σ.θ₃ : ℂ) * I)) * (z - σ.vertexOne) /
    (1 + conj σ.vertexOne * z)) := by
  rw [rotOne, disc_sph hs, sphMoeb]
  ring

theorem rotTwo_apply_sph (z : ℂ) : σ.rotTwo z = -(exp ((σ.θ₂ : ℂ) * I) * (z - σ.vertexTwo) /
    (1 + σ.vertexTwo * z)) := by
  rw [rotTwo, disc_sph hs, sphMoeb, conj_vertexTwo_sph]
  ring

theorem rotOne_vertexOne_sph : σ.rotOne σ.vertexOne = 0 := by
  rw [rotOne_apply_sph hs]
  simp

theorem rotTwo_vertexTwo_sph : σ.rotTwo σ.vertexTwo = 0 := by
  rw [rotTwo_apply_sph hs]
  simp

theorem rotOne_zero_sph : σ.rotOne 0 = σ.sphTOneThree := by
  rw [rotOne_apply_sph hs, vertexOne_eq_sph]
  simp only [mul_zero, add_zero, div_one, zero_sub]
  rw [mul_neg, neg_neg, mul_left_comm, mul_comm (exp _), exp_mul_exp_neg_sph, mul_one]

theorem rotTwo_zero_sph : σ.rotTwo 0 = (σ.sphTTwoThree : ℂ) * exp ((σ.θ₂ : ℂ) * I) := by
  rw [rotTwo_apply_sph hs, vertexTwo_eq_sph]
  simp only [mul_zero, add_zero, div_one, zero_sub]
  ring

theorem one_add_vertexTwo_mul_vertexOne_ne_sph : 1 + σ.vertexTwo * σ.vertexOne ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  rw [vertexOne_eq_sph, vertexTwo_eq_sph] at h'
  simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, zero_re, zero_mul, sub_zero] at h'
  have := mul_nonneg (mul_nonneg (tTwoThree_pos_sph hs).le (tOneThree_pos_sph hs).le)
      σ.cos_θ₃_nonneg_sph
  nlinarith

theorem one_add_conj_vertexOne_mul_vertexTwo_ne_sph : 1 + conj σ.vertexOne * σ.vertexTwo ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  rw [conj_vertexOne_sph, vertexTwo_eq_sph, exp_neg_ofReal_mul_I_sph] at h'
  simp only [add_re, one_re, mul_re, ofReal_re, ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, zero_re, zero_mul, sub_zero, mul_zero, Real.cos_neg] at h'
  have := mul_nonneg (mul_nonneg (tOneThree_pos_sph hs).le σ.cos_θ₃_nonneg_sph) (tTwoThree_pos_sph
      hs).le
  nlinarith

theorem rotTwo_vertexOne_sph : σ.rotTwo σ.vertexOne = σ.sphTOneTwo := by
  have hne := one_add_vertexTwo_mul_vertexOne_ne_sph hs
  rw [rotTwo_apply_sph hs, vertexOne_sub_vertexTwo_sph hs]
  field_simp
  have := exp_mul_exp_neg_sph σ.θ₂
  linear_combination (σ.sphTOneTwo : ℂ) * this

theorem rotOne_vertexTwo_sph : σ.rotOne σ.vertexTwo = σ.sphTOneTwo * exp ((σ.θ₁ : ℂ) * I) := by
  have hne := one_add_conj_vertexOne_mul_vertexTwo_ne_sph hs
  have e : σ.vertexTwo - σ.vertexOne = -(σ.sphTOneTwo * exp ((σ.θ₁ : ℂ) * I) *
      exp ((σ.θ₃ : ℂ) * I) * (1 + conj σ.vertexOne * σ.vertexTwo)) := by
    rw [← neg_sub, vertexOne_sub_vertexTwo_sph' hs, conj_vertexOne_sph, vertexTwo_eq_sph]
    push_cast
    rw [add_mul, Complex.exp_add]
    have := exp_mul_exp_neg_sph σ.θ₃
    linear_combination (σ.sphTOneTwo : ℂ) * exp ((σ.θ₁ : ℂ) * I) * (σ.sphTTwoThree : ℂ) *
      (σ.sphTOneThree : ℂ) * this
  rw [rotOne_apply_sph hs, e]
  field_simp
  have := exp_mul_exp_neg_sph σ.θ₃
  linear_combination (σ.sphTOneTwo : ℂ) * this

theorem excess_identity_sph : 1 + σ.vertexTwo * σ.vertexOne =
    -(exp (((σ.θ₁ + σ.θ₂ + σ.θ₃ : ℝ) : ℂ) * I) * (1 + σ.vertexTwo * conj σ.vertexOne)) := by
  obtain ⟨ha, hb, hc, hD⟩ := trig_hyps_sph hs
  have h1 := σ.sphE₁_pos.ne'
  have h2 := σ.sphE₂_pos.ne'
  rw [conj_vertexOne_sph, vertexOne_eq_sph, vertexTwo_eq_sph, tOneThree_eq_sph hs, tTwoThree_eq_sph
      hs,
    exp_neg_ofReal_mul_I_sph]
  unfold sphE₁ sphE₂ at *
  apply Complex.ext
  · simp only [add_re, neg_re, mul_re, add_im, mul_im, ofReal_re, ofReal_im, one_re, one_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg,
      Real.cos_add, Real.sin_add]
    linear_combination excess_re_sph ha hb hc hD h1 h2 +
      ((Real.sqrt σ.sphDelta / (Real.cos σ.θ₁ + Real.cos σ.θ₂ * Real.cos σ.θ₃ + Real.sin σ.θ₂ *
        Real.sin σ.θ₃) * (Real.sqrt σ.sphDelta / (Real.cos σ.θ₂ + Real.cos σ.θ₁ * Real.cos σ.θ₃ +
        Real.sin σ.θ₁ * Real.sin σ.θ₃))) * (Real.cos σ.θ₁ * Real.cos σ.θ₂ - Real.sin σ.θ₁ * Real.sin
        σ.θ₂)) * hc
  · simp only [add_re, neg_im, mul_re, add_im, mul_im, ofReal_re, ofReal_im, one_re, one_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg,
      Real.cos_add, Real.sin_add]
    linear_combination excess_im_sph ha hb hc hD h1 h2 +
      ((Real.sqrt σ.sphDelta / (Real.cos σ.θ₁ + Real.cos σ.θ₂ * Real.cos σ.θ₃ + Real.sin σ.θ₂ *
        Real.sin σ.θ₃) * (Real.sqrt σ.sphDelta / (Real.cos σ.θ₂ + Real.cos σ.θ₁ * Real.cos σ.θ₃ +
        Real.sin σ.θ₁ * Real.sin σ.θ₃))) * (Real.sin σ.θ₁ * Real.cos σ.θ₂ + Real.cos σ.θ₁ * Real.sin
        σ.θ₂)) * hc

theorem rotTwo_eq_mul_sph (z : ℂ) : σ.rotTwo z = -exp ((σ.θ₂ : ℂ) * I) * sphMoeb σ.vertexTwo z := by
  rw [rotTwo, disc_sph hs]
  ring

theorem rotOne_eq_mul_sph (z : ℂ) :
    σ.rotOne z = -exp (-((σ.θ₃ : ℂ) * I)) * sphMoeb σ.vertexOne z := by
  rw [rotOne, disc_sph hs]
  ring

theorem rotOne_eq_rotTwo_sph {z : ℂ} (h1 : 1 + conj σ.vertexOne * z ≠ 0)
    (h2 : 1 + conj σ.vertexTwo * z ≠ 0) :
    σ.rotOne z = -(exp ((σ.θ₁ : ℂ) * I) * sphMoeb σ.sphTOneTwo (σ.rotTwo z)) := by
  have hv : 1 + conj σ.vertexTwo * σ.vertexOne ≠ 0 := by
    rw [conj_vertexTwo_sph]
    exact one_add_vertexTwo_mul_vertexOne_ne_sph hs
  have hu : conj (-exp ((σ.θ₂ : ℂ) * I)) * -exp ((σ.θ₂ : ℂ) * I) = 1 := conj_neg_exp_mul_sph σ.θ₂
  have e1 : sphMoeb σ.sphTOneTwo (σ.rotTwo z) = -exp ((σ.θ₂ : ℂ) * I) *
      (sphMoeb σ.vertexOne z * ((1 + σ.vertexTwo * conj σ.vertexOne) /
        (1 + σ.vertexTwo * σ.vertexOne))) := by
    rw [← rotTwo_vertexOne_sph hs, rotTwo_eq_mul_sph hs, rotTwo_eq_mul_sph hs, sphMoeb_mul_unit hu,
      sphMoeb_comp h2 hv h1, conj_vertexTwo_sph]
  have hex := excess_identity_sph hs
  have hne := one_add_vertexTwo_mul_vertexOne_ne_sph hs
  rw [e1, rotOne_eq_mul_sph hs]
  have e2 : (1 + σ.vertexTwo * conj σ.vertexOne) / (1 + σ.vertexTwo * σ.vertexOne) =
      -exp (-(((σ.θ₁ + σ.θ₂ + σ.θ₃ : ℝ) : ℂ) * I)) := by
    rw [div_eq_iff hne, hex]
    have := exp_mul_exp_neg_sph (σ.θ₁ + σ.θ₂ + σ.θ₃)
    linear_combination (-(1 + σ.vertexTwo * conj σ.vertexOne)) * this
  rw [e2]
  have e3 : exp ((σ.θ₁ : ℂ) * I) * exp ((σ.θ₂ : ℂ) * I) *
      exp (-(((σ.θ₁ + σ.θ₂ + σ.θ₃ : ℝ) : ℂ) * I)) = exp (-((σ.θ₃ : ℂ) * I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (sphMoeb σ.vertexOne z) * e3

end Spherical

end CompactShape

end GC.Seifert
