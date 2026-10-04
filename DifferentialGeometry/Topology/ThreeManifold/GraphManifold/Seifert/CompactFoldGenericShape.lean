import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSpec

/-!
# Generic shape facts of the compact triangles

Lane CF, tier 4 (design `docs/geometrization/handoffs/20261004-design-cf-compact-triangle-fold.md`,
§2; the generic part of the `CompactFoldSpec` deliverables). For every `σ : CompactShape`, in all
three curvatures at once:
* the side tangents `sideTanOne = ‖v₁‖`, `sideTanTwo = v₂` are positive and the vertices lie in the
  chart `plane` (`sideTanOne_pos`, `eps_sideTanOne_sq_lt`, …): for `ε = ±1` the side cosines
  `sideCos` lie strictly above resp. below `1` because the angle sum is below resp. above `π`;
* the vertex `v₁` lies on wall `2` (`wallSide_two_vertexOne`): in the explicit formula
  `wallSide_two_eq` of the side function the claim reduces, for `ε = ±1`, to the ε-law of sines
  `t₁ (C₁ + 1) sin θ₁ = t₂ (C₂ + 1) sin θ₂` (both equal `√(εK)/sin θ₃`, `K` the symmetric
  cosine expression `sideCos_sq_sub_one`) and the projection identity `C₁ sin θ₁ =
  sin θ₂ cos θ₃ C₂ + cos θ₂ sin θ₃`; for `ε = 0` it is the flat statement;
* along the ray of wall `1` the side function of wall `2` factors as
  `(t₂ sin θ₂ / t₁)(t₁ - t)(1 - ε t t₁)` (`wallSide_two_ray_mul`), along the real axis as
  `sin θ₂ (t₂ - x)(1 - ε t₂ x)`, so the walls `0`, `1` of the triangle are the segments `[0, v₂]`,
  `[0, v₁]` (`eq_ray_of_wallOne`, `eq_real_of_wallZero`, `ray_mem_triangle`,
  `real_mem_triangle`), wall `2` meets them only at `v₂`, `v₁`, and the three vertices lie in the
  triangle (`vertexOne_mem_triangle`, `vertexTwo_mem_triangle`);
* the reflection `refl i` fixes the points of wall `i` (in the chart domain for `i = 2`;
  `refl_eq_self`), and the open triangle `{z ∈ plane, wᵢ(z) > 0}` is open and misses the
  vertices.
-/

set_option autoImplicit false

noncomputable section

open Complex Set
open scoped ComplexConjugate

namespace GC.Seifert

namespace CompactShape

variable (σ : CompactShape)

def sideTanOne : ℝ := σ.sideTan σ.θ₁ σ.θ₃ σ.θ₂

def sideTanTwo : ℝ := σ.sideTan σ.θ₂ σ.θ₃ σ.θ₁

def openTriangle : Set ℂ := {z | z ∈ σ.plane ∧ ∀ i, 0 < σ.wallSide i z}

theorem θ₁_pos : 0 < σ.θ₁ := EuclidShape.θ_pos_aux σ.two_le_p₁

theorem θ₂_pos : 0 < σ.θ₂ := EuclidShape.θ_pos_aux σ.two_le_p₂

theorem θ₃_pos : 0 < σ.θ₃ := EuclidShape.θ_pos_aux σ.two_le_p₃

theorem θ₁_le : σ.θ₁ ≤ Real.pi / 2 := EuclidShape.θ_le_aux σ.two_le_p₁

theorem θ₂_le : σ.θ₂ ≤ Real.pi / 2 := EuclidShape.θ_le_aux σ.two_le_p₂

theorem θ₃_le : σ.θ₃ ≤ Real.pi / 2 := EuclidShape.θ_le_aux σ.two_le_p₃

theorem sin_θ₁_pos : 0 < Real.sin σ.θ₁ := EuclidShape.sin_pos_aux σ.θ₁_pos σ.θ₁_le

theorem sin_θ₂_pos : 0 < Real.sin σ.θ₂ := EuclidShape.sin_pos_aux σ.θ₂_pos σ.θ₂_le

theorem sin_θ₃_pos : 0 < Real.sin σ.θ₃ := EuclidShape.sin_pos_aux σ.θ₃_pos σ.θ₃_le

theorem cos_θ₁_nonneg : 0 ≤ Real.cos σ.θ₁ := EuclidShape.cos_nonneg_aux σ.θ₁_pos σ.θ₁_le

theorem cos_θ₂_nonneg : 0 ≤ Real.cos σ.θ₂ := EuclidShape.cos_nonneg_aux σ.θ₂_pos σ.θ₂_le

theorem cos_θ₃_nonneg : 0 ≤ Real.cos σ.θ₃ := EuclidShape.cos_nonneg_aux σ.θ₃_pos σ.θ₃_le

theorem θ₃_mul : σ.θ₃ * σ.p₃ = Real.pi := by
  have := EuclidShape.p_pos_aux σ.two_le_p₃
  unfold θ₃
  field_simp

theorem θ_sum_eq : σ.θ₁ + σ.θ₂ + σ.θ₃ = Real.pi * (1 / σ.p₁ + 1 / σ.p₂ + 1 / σ.p₃) := by
  unfold θ₁ θ₂ θ₃
  ring

theorem θ_sum_of_hyp (h : σ.curv = .hyperbolic) : σ.θ₁ + σ.θ₂ + σ.θ₃ < Real.pi := by
  rcases σ.angle_cond with ⟨-, hs⟩ | ⟨h', -⟩ | ⟨h', -⟩
  · rw [θ_sum_eq]
    nlinarith [Real.pi_pos]
  · rw [h] at h'; exact absurd h' (by decide)
  · rw [h] at h'; exact absurd h' (by decide)

theorem θ_sum_of_sph (h : σ.curv = .spherical) : Real.pi < σ.θ₁ + σ.θ₂ + σ.θ₃ := by
  rcases σ.angle_cond with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, hs⟩
  · rw [h] at h'; exact absurd h' (by decide)
  · rw [h] at h'; exact absurd h' (by decide)
  · rw [θ_sum_eq]
    nlinarith [Real.pi_pos]

theorem eps_of_hyp (h : σ.curv = .hyperbolic) : σ.eps = 1 := by
  unfold eps; rw [h]; rfl

theorem eps_of_sph (h : σ.curv = .spherical) : σ.eps = -1 := by
  unfold eps; rw [h]; rfl

theorem sideTan_of_hyp (h : σ.curv = .hyperbolic) (a b c : ℝ) :
    σ.sideTan a b c = Real.sqrt ((sideCos a b c - 1) / (sideCos a b c + 1)) := by
  unfold sideTan; rw [h]

theorem sideTan_of_sph (h : σ.curv = .spherical) (a b c : ℝ) :
    σ.sideTan a b c = Real.sqrt ((1 - sideCos a b c) / (1 + sideCos a b c)) := by
  unfold sideTan; rw [h]

theorem sideCos_nonneg {a b c : ℝ} (ha : 0 < Real.sin a) (hb : 0 < Real.sin b)
    (hca : 0 ≤ Real.cos a) (hcb : 0 ≤ Real.cos b) (hcc : 0 ≤ Real.cos c) : 0 ≤ sideCos a b c := by
  unfold sideCos
  positivity

theorem sideCos_sub_one (a b c : ℝ) (hab : Real.sin a * Real.sin b ≠ 0) :
    sideCos a b c - 1 = (Real.cos c - Real.cos (Real.pi - (a + b))) /
      (Real.sin a * Real.sin b) := by
  have h1 := left_ne_zero_of_mul hab
  have h2 := right_ne_zero_of_mul hab
  unfold sideCos
  rw [Real.cos_pi_sub, Real.cos_add]
  field_simp
  ring

theorem one_lt_sideCos {a b c : ℝ} (ha0 : 0 < a) (ha : a ≤ Real.pi / 2) (hb0 : 0 < b)
    (hb : b ≤ Real.pi / 2) (hc0 : 0 < c) (hs : a + b + c < Real.pi) : 1 < sideCos a b c := by
  have hsa := EuclidShape.sin_pos_aux ha0 ha
  have hsb := EuclidShape.sin_pos_aux hb0 hb
  have e := sideCos_sub_one a b c (mul_pos hsa hsb).ne'
  have hcos : Real.cos (Real.pi - (a + b)) < Real.cos c :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hc0.le (by linarith) (by linarith)
  have : 0 < sideCos a b c - 1 := by
    rw [e]
    exact div_pos (by linarith) (mul_pos hsa hsb)
  linarith

theorem sideCos_lt_one {a b c : ℝ} (ha0 : 0 < a) (ha : a ≤ Real.pi / 2) (hb0 : 0 < b)
    (hb : b ≤ Real.pi / 2) (hc : c ≤ Real.pi / 2) (hs : Real.pi < a + b + c) :
    sideCos a b c < 1 := by
  have hsa := EuclidShape.sin_pos_aux ha0 ha
  have hsb := EuclidShape.sin_pos_aux hb0 hb
  have e := sideCos_sub_one a b c (mul_pos hsa hsb).ne'
  have hcos : Real.cos c < Real.cos (Real.pi - (a + b)) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]) (by linarith)
  have : sideCos a b c - 1 < 0 := by
    rw [e]
    exact div_neg_of_neg_of_pos (by linarith) (mul_pos hsa hsb)
  linarith

theorem sideCos_sq_sub_one (a b c : ℝ) (hab : Real.sin a * Real.sin b ≠ 0) :
    (sideCos a b c ^ 2 - 1) * (Real.sin a * Real.sin b) ^ 2 =
      Real.cos a ^ 2 + Real.cos b ^ 2 + Real.cos c ^ 2 +
        2 * Real.cos a * Real.cos b * Real.cos c - 1 := by
  have h1 := left_ne_zero_of_mul hab
  have h2 := right_ne_zero_of_mul hab
  have ha := Real.sin_sq_add_cos_sq a
  have hb := Real.sin_sq_add_cos_sq b
  unfold sideCos
  field_simp
  linear_combination (-(Real.sin b ^ 2)) * ha + (Real.cos a ^ 2 - 1) * hb

theorem sqrt_ratio_mul {C S : ℝ} (hC : 0 < C + 1) (hS : 0 ≤ S) :
    Real.sqrt ((C - 1) / (C + 1)) * ((C + 1) * S) = Real.sqrt ((C ^ 2 - 1) * S ^ 2) := by
  have hT : 0 ≤ (C + 1) * S := mul_nonneg hC.le hS
  rw [← Real.sqrt_sq hT, ← Real.sqrt_mul' _ (sq_nonneg _)]
  congr 1
  field_simp
  ring

theorem sqrt_ratio_mul' {C S : ℝ} (hC : 0 < C + 1) (hS : 0 ≤ S) :
    Real.sqrt ((1 - C) / (1 + C)) * ((C + 1) * S) = Real.sqrt ((1 - C ^ 2) * S ^ 2) := by
  have hT : 0 ≤ (C + 1) * S := mul_nonneg hC.le hS
  rw [← Real.sqrt_sq hT, ← Real.sqrt_mul' _ (sq_nonneg _)]
  congr 1
  rw [add_comm 1 C]
  field_simp
  ring

theorem wallSide_two_eq_poly (z : ℂ) : σ.wallSide 2 z =
    Real.sin σ.θ₂ * (σ.sideTanTwo * (1 + σ.eps * (z.re ^ 2 + z.im ^ 2)) -
      z.re * (1 + σ.eps * σ.sideTanTwo ^ 2)) -
      Real.cos σ.θ₂ * z.im * (1 - σ.eps * σ.sideTanTwo ^ 2) := by
  change (-(exp ((σ.θ₂ : ℂ) * I) * ((z - σ.vertexTwo) *
    conj (1 - σ.eps * conj σ.vertexTwo * z)))).im = _
  rw [vertexTwo, ← sideTanTwo]
  simp only [neg_im, mul_im, mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    sub_re, sub_im, map_sub, map_one, map_mul, Complex.conj_ofReal, one_re,
    one_im, ofReal_re, ofReal_im, conj_re, conj_im]
  ring

theorem wallSide_zero_eq (z : ℂ) : σ.wallSide 0 z = z.im := rfl

theorem wallSide_one_eq (z : ℂ) :
    σ.wallSide 1 z = Real.sin σ.θ₃ * z.re - Real.cos σ.θ₃ * z.im := by
  change (exp ((σ.θ₃ : ℂ) * I) * conj z).im = _
  simp only [mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, conj_re, conj_im]
  ring

theorem ray_re (t : ℝ) : ((t : ℂ) * exp ((σ.θ₃ : ℂ) * I)).re = t * Real.cos σ.θ₃ := by
  simp [mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem ray_im (t : ℝ) : ((t : ℂ) * exp ((σ.θ₃ : ℂ) * I)).im = t * Real.sin σ.θ₃ := by
  simp [mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

theorem wallSide_two_ray (t : ℝ) : σ.wallSide 2 ((t : ℂ) * exp ((σ.θ₃ : ℂ) * I)) =
    Real.sin σ.θ₂ * (σ.sideTanTwo * (1 + σ.eps * t ^ 2) -
      t * Real.cos σ.θ₃ * (1 + σ.eps * σ.sideTanTwo ^ 2)) -
      Real.cos σ.θ₂ * (t * Real.sin σ.θ₃) * (1 - σ.eps * σ.sideTanTwo ^ 2) := by
  rw [wallSide_two_eq_poly, ray_re, ray_im]
  have := Real.sin_sq_add_cos_sq σ.θ₃
  have e : (t * Real.cos σ.θ₃) ^ 2 + (t * Real.sin σ.θ₃) ^ 2 = t ^ 2 := by
    linear_combination t ^ 2 * this
  rw [e]

theorem wallSide_two_real (x : ℝ) : σ.wallSide 2 (x : ℂ) =
    Real.sin σ.θ₂ * ((σ.sideTanTwo - x) * (1 - σ.eps * σ.sideTanTwo * x)) := by
  rw [wallSide_two_eq_poly, ofReal_re, ofReal_im]
  ring

theorem sideCos_one_gt (h : σ.curv = .hyperbolic) : 1 < sideCos σ.θ₁ σ.θ₃ σ.θ₂ :=
  one_lt_sideCos σ.θ₁_pos σ.θ₁_le σ.θ₃_pos σ.θ₃_le σ.θ₂_pos (by linarith [σ.θ_sum_of_hyp h])

theorem sideCos_two_gt (h : σ.curv = .hyperbolic) : 1 < sideCos σ.θ₂ σ.θ₃ σ.θ₁ :=
  one_lt_sideCos σ.θ₂_pos σ.θ₂_le σ.θ₃_pos σ.θ₃_le σ.θ₁_pos (by linarith [σ.θ_sum_of_hyp h])

theorem sideCos_one_lt (h : σ.curv = .spherical) : sideCos σ.θ₁ σ.θ₃ σ.θ₂ < 1 :=
  sideCos_lt_one σ.θ₁_pos σ.θ₁_le σ.θ₃_pos σ.θ₃_le σ.θ₂_le (by linarith [σ.θ_sum_of_sph h])

theorem sideCos_two_lt (h : σ.curv = .spherical) : sideCos σ.θ₂ σ.θ₃ σ.θ₁ < 1 :=
  sideCos_lt_one σ.θ₂_pos σ.θ₂_le σ.θ₃_pos σ.θ₃_le σ.θ₁_le (by linarith [σ.θ_sum_of_sph h])

theorem sideCos_one_nonneg : 0 ≤ sideCos σ.θ₁ σ.θ₃ σ.θ₂ :=
  sideCos_nonneg σ.sin_θ₁_pos σ.sin_θ₃_pos σ.cos_θ₁_nonneg σ.cos_θ₃_nonneg σ.cos_θ₂_nonneg

theorem sideCos_two_nonneg : 0 ≤ sideCos σ.θ₂ σ.θ₃ σ.θ₁ :=
  sideCos_nonneg σ.sin_θ₂_pos σ.sin_θ₃_pos σ.cos_θ₂_nonneg σ.cos_θ₃_nonneg σ.cos_θ₁_nonneg

theorem sideTan_facts {C t : ℝ} (hC : 0 ≤ C)
    (ht : (σ.curv = .hyperbolic ∧ 1 < C ∧ t = Real.sqrt ((C - 1) / (C + 1))) ∨
      (σ.curv = .spherical ∧ C < 1 ∧ t = Real.sqrt ((1 - C) / (1 + C)))) :
    0 < t ∧ σ.eps * t ^ 2 < 1 ∧ σ.eps * t ^ 2 * (C + 1) = C - 1 ∧ σ.eps ^ 2 = 1 := by
  rcases ht with ⟨h, hC1, rfl⟩ | ⟨h, hC1, rfl⟩
  · rw [σ.eps_of_hyp h]
    have hq : 0 < (C - 1) / (C + 1) := div_pos (by linarith) (by linarith)
    have hq1 : (C - 1) / (C + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    rw [Real.sq_sqrt hq.le]
    refine ⟨Real.sqrt_pos.2 hq, by linarith, ?_, by norm_num⟩
    field_simp
  · rw [σ.eps_of_sph h]
    have hq : 0 < (1 - C) / (1 + C) := div_pos (by linarith) (by linarith)
    rw [Real.sq_sqrt hq.le]
    refine ⟨Real.sqrt_pos.2 hq, by nlinarith, ?_, by norm_num⟩
    rw [add_comm C 1]
    field_simp
    ring

theorem sideTanOne_flat (h : σ.curv = .flat) : σ.sideTanOne = Real.sin σ.θ₂ := by
  unfold sideTanOne; exact sideTan_flat h _ _ _

theorem sideTanTwo_flat (h : σ.curv = .flat) : σ.sideTanTwo = Real.sin σ.θ₁ := by
  unfold sideTanTwo; exact sideTan_flat h _ _ _

theorem sideTanOne_pos : 0 < σ.sideTanOne := by
  rcases hc : σ.curv
  · exact (σ.sideTan_facts σ.sideCos_one_nonneg (Or.inl ⟨hc, σ.sideCos_one_gt hc,
      σ.sideTan_of_hyp hc _ _ _⟩)).1
  · rw [σ.sideTanOne_flat hc]; exact σ.sin_θ₂_pos
  · exact (σ.sideTan_facts σ.sideCos_one_nonneg (Or.inr ⟨hc, σ.sideCos_one_lt hc,
      σ.sideTan_of_sph hc _ _ _⟩)).1

theorem sideTanTwo_pos : 0 < σ.sideTanTwo := by
  rcases hc : σ.curv
  · exact (σ.sideTan_facts σ.sideCos_two_nonneg (Or.inl ⟨hc, σ.sideCos_two_gt hc,
      σ.sideTan_of_hyp hc _ _ _⟩)).1
  · rw [σ.sideTanTwo_flat hc]; exact σ.sin_θ₁_pos
  · exact (σ.sideTan_facts σ.sideCos_two_nonneg (Or.inr ⟨hc, σ.sideCos_two_lt hc,
      σ.sideTan_of_sph hc _ _ _⟩)).1

theorem eps_sideTanOne_sq_lt : σ.eps * σ.sideTanOne ^ 2 < 1 := by
  rcases hc : σ.curv
  · exact (σ.sideTan_facts σ.sideCos_one_nonneg (Or.inl ⟨hc, σ.sideCos_one_gt hc,
      σ.sideTan_of_hyp hc _ _ _⟩)).2.1
  · rw [eps_flat hc]; norm_num
  · exact (σ.sideTan_facts σ.sideCos_one_nonneg (Or.inr ⟨hc, σ.sideCos_one_lt hc,
      σ.sideTan_of_sph hc _ _ _⟩)).2.1

theorem eps_sideTanTwo_sq_lt : σ.eps * σ.sideTanTwo ^ 2 < 1 := by
  rcases hc : σ.curv
  · exact (σ.sideTan_facts σ.sideCos_two_nonneg (Or.inl ⟨hc, σ.sideCos_two_gt hc,
      σ.sideTan_of_hyp hc _ _ _⟩)).2.1
  · rw [eps_flat hc]; norm_num
  · exact (σ.sideTan_facts σ.sideCos_two_nonneg (Or.inr ⟨hc, σ.sideCos_two_lt hc,
      σ.sideTan_of_sph hc _ _ _⟩)).2.1

theorem cos_identity :
    sideCos σ.θ₁ σ.θ₃ σ.θ₂ * Real.sin σ.θ₁ = Real.sin σ.θ₂ * Real.cos σ.θ₃ *
      sideCos σ.θ₂ σ.θ₃ σ.θ₁ + Real.cos σ.θ₂ * Real.sin σ.θ₃ := by
  have h1 := σ.sin_θ₁_pos.ne'
  have h2 := σ.sin_θ₂_pos.ne'
  have h3 := σ.sin_θ₃_pos.ne'
  have hc := Real.sin_sq_add_cos_sq σ.θ₃
  unfold sideCos
  field_simp
  linear_combination (-Real.cos σ.θ₂) * hc

theorem sine_law_hyp (h : σ.curv = .hyperbolic) :
    σ.sideTanOne * (sideCos σ.θ₁ σ.θ₃ σ.θ₂ + 1) * Real.sin σ.θ₁ =
      σ.sideTanTwo * (sideCos σ.θ₂ σ.θ₃ σ.θ₁ + 1) * Real.sin σ.θ₂ := by
  have h1 := σ.sin_θ₁_pos
  have h2 := σ.sin_θ₂_pos
  have h3 := σ.sin_θ₃_pos
  have e1 := sqrt_ratio_mul (C := sideCos σ.θ₁ σ.θ₃ σ.θ₂) (by linarith [σ.sideCos_one_nonneg])
    (mul_pos h1 h3).le
  have e2 := sqrt_ratio_mul (C := sideCos σ.θ₂ σ.θ₃ σ.θ₁) (by linarith [σ.sideCos_two_nonneg])
    (mul_pos h2 h3).le
  rw [sideCos_sq_sub_one _ _ _ (mul_pos h1 h3).ne'] at e1
  rw [sideCos_sq_sub_one _ _ _ (mul_pos h2 h3).ne'] at e2
  rw [← σ.sideTan_of_hyp h, ← sideTanOne] at e1
  rw [← σ.sideTan_of_hyp h, ← sideTanTwo] at e2
  have key : σ.sideTanOne * (sideCos σ.θ₁ σ.θ₃ σ.θ₂ + 1) * Real.sin σ.θ₁ * Real.sin σ.θ₃ =
      σ.sideTanTwo * (sideCos σ.θ₂ σ.θ₃ σ.θ₁ + 1) * Real.sin σ.θ₂ * Real.sin σ.θ₃ := by
    have := e1.trans (e2.trans (congrArg Real.sqrt (by ring))).symm
    linear_combination this
  exact mul_right_cancel₀ h3.ne' key

theorem sine_law_sph (h : σ.curv = .spherical) :
    σ.sideTanOne * (sideCos σ.θ₁ σ.θ₃ σ.θ₂ + 1) * Real.sin σ.θ₁ =
      σ.sideTanTwo * (sideCos σ.θ₂ σ.θ₃ σ.θ₁ + 1) * Real.sin σ.θ₂ := by
  have h1 := σ.sin_θ₁_pos
  have h2 := σ.sin_θ₂_pos
  have h3 := σ.sin_θ₃_pos
  have e1 := sqrt_ratio_mul' (C := sideCos σ.θ₁ σ.θ₃ σ.θ₂) (by linarith [σ.sideCos_one_nonneg])
    (mul_pos h1 h3).le
  have e2 := sqrt_ratio_mul' (C := sideCos σ.θ₂ σ.θ₃ σ.θ₁) (by linarith [σ.sideCos_two_nonneg])
    (mul_pos h2 h3).le
  have k1 := sideCos_sq_sub_one σ.θ₁ σ.θ₃ σ.θ₂ (mul_pos h1 h3).ne'
  have k2 := sideCos_sq_sub_one σ.θ₂ σ.θ₃ σ.θ₁ (mul_pos h2 h3).ne'
  rw [show (1 - sideCos σ.θ₁ σ.θ₃ σ.θ₂ ^ 2) * (Real.sin σ.θ₁ * Real.sin σ.θ₃) ^ 2 =
    -((sideCos σ.θ₁ σ.θ₃ σ.θ₂ ^ 2 - 1) * (Real.sin σ.θ₁ * Real.sin σ.θ₃) ^ 2) by ring, k1] at e1
  rw [show (1 - sideCos σ.θ₂ σ.θ₃ σ.θ₁ ^ 2) * (Real.sin σ.θ₂ * Real.sin σ.θ₃) ^ 2 =
    -((sideCos σ.θ₂ σ.θ₃ σ.θ₁ ^ 2 - 1) * (Real.sin σ.θ₂ * Real.sin σ.θ₃) ^ 2) by ring, k2] at e2
  rw [← σ.sideTan_of_sph h, ← sideTanOne] at e1
  rw [← σ.sideTan_of_sph h, ← sideTanTwo] at e2
  have key : σ.sideTanOne * (sideCos σ.θ₁ σ.θ₃ σ.θ₂ + 1) * Real.sin σ.θ₁ * Real.sin σ.θ₃ =
      σ.sideTanTwo * (sideCos σ.θ₂ σ.θ₃ σ.θ₁ + 1) * Real.sin σ.θ₂ * Real.sin σ.θ₃ := by
    have := e1.trans (e2.trans (congrArg Real.sqrt (by ring))).symm
    linear_combination this
  exact mul_right_cancel₀ h3.ne' key

theorem wall_identity {ε t₁ t₂ A B s₁ s₂ s₃ c₂ c₃ : ℝ} (h1 : ε * t₁ ^ 2 * (A + 1) = A - 1)
    (h2 : ε * t₂ ^ 2 * (B + 1) = B - 1) (hsine : t₁ * (A + 1) * s₁ = t₂ * (B + 1) * s₂)
    (hcos : A * s₁ = s₂ * c₃ * B + c₂ * s₃) (hA : A + 1 ≠ 0) (hB : B + 1 ≠ 0) :
    s₂ * (t₂ * (1 + ε * t₁ ^ 2) - t₁ * c₃ * (1 + ε * t₂ ^ 2)) - c₂ * (t₁ * s₃) *
      (1 - ε * t₂ ^ 2) = 0 := by
  have key : (s₂ * (t₂ * (1 + ε * t₁ ^ 2) - t₁ * c₃ * (1 + ε * t₂ ^ 2)) - c₂ * (t₁ * s₃) *
      (1 - ε * t₂ ^ 2)) * ((A + 1) * (B + 1)) = 0 := by
    linear_combination s₂ * t₂ * (B + 1) * h1 + t₁ * (A + 1) * (c₂ * s₃ - s₂ * c₃) * h2 -
      2 * A * hsine + 2 * t₁ * (A + 1) * hcos
  exact (mul_eq_zero.1 key).resolve_right (mul_ne_zero hA hB)

theorem wallSide_two_vertexOne : σ.wallSide 2 σ.vertexOne = 0 := by
  rcases hc : σ.curv
  · have f1 := σ.sideTan_facts σ.sideCos_one_nonneg (Or.inl ⟨hc, σ.sideCos_one_gt hc,
      σ.sideTan_of_hyp hc _ _ _⟩)
    have f2 := σ.sideTan_facts σ.sideCos_two_nonneg (Or.inl ⟨hc, σ.sideCos_two_gt hc,
      σ.sideTan_of_hyp hc _ _ _⟩)
    rw [vertexOne, ← sideTanOne, wallSide_two_ray]
    exact wall_identity f1.2.2.1 f2.2.2.1 (σ.sine_law_hyp hc) σ.cos_identity
      (by linarith [σ.sideCos_one_nonneg]) (by linarith [σ.sideCos_two_nonneg])
  · rw [wallSide_flat hc, vertexOne_flat hc]
    exact (σ.toEuclidShape hc).wallSide_two_vertexOne
  · have f1 := σ.sideTan_facts σ.sideCos_one_nonneg (Or.inr ⟨hc, σ.sideCos_one_lt hc,
      σ.sideTan_of_sph hc _ _ _⟩)
    have f2 := σ.sideTan_facts σ.sideCos_two_nonneg (Or.inr ⟨hc, σ.sideCos_two_lt hc,
      σ.sideTan_of_sph hc _ _ _⟩)
    rw [vertexOne, ← sideTanOne, wallSide_two_ray]
    exact wall_identity f1.2.2.1 f2.2.2.1 (σ.sine_law_sph hc) σ.cos_identity
      (by linarith [σ.sideCos_one_nonneg]) (by linarith [σ.sideCos_two_nonneg])

theorem wallSide_two_ray_mul (t : ℝ) :
    σ.sideTanOne * σ.wallSide 2 ((t : ℂ) * exp ((σ.θ₃ : ℂ) * I)) = σ.sideTanTwo *
      Real.sin σ.θ₂ * ((σ.sideTanOne - t) * (1 - σ.eps * t * σ.sideTanOne)) := by
  have h0 := σ.wallSide_two_vertexOne
  rw [vertexOne, ← sideTanOne, wallSide_two_ray] at h0
  rw [wallSide_two_ray]
  linear_combination t * h0

theorem eps_mul_lt_one {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hx' : σ.eps * x ^ 2 < 1)
    (hy' : σ.eps * y ^ 2 < 1) : σ.eps * (x * y) < 1 := by
  rcases hc : σ.curv
  · rw [σ.eps_of_hyp hc] at *
    nlinarith [sq_nonneg (x - y)]
  · rw [eps_flat hc]; norm_num
  · rw [σ.eps_of_sph hc]
    nlinarith [mul_nonneg hx hy]

theorem eps_sq_lt_of_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : σ.eps * y ^ 2 < 1) :
    σ.eps * x ^ 2 < 1 := by
  rcases hc : σ.curv
  · rw [σ.eps_of_hyp hc] at *
    nlinarith
  · rw [eps_flat hc]; norm_num
  · rw [σ.eps_of_sph hc]
    nlinarith [sq_nonneg x]

theorem mem_plane_iff (z : ℂ) : z ∈ σ.plane ↔ σ.eps * ‖z‖ ^ 2 < 1 := Iff.rfl

theorem norm_ray {t : ℝ} (ht : 0 ≤ t) : ‖(t : ℂ) * exp ((σ.θ₃ : ℂ) * I)‖ = t := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht,
    Complex.norm_exp_ofReal_mul_I, mul_one]

theorem vertexOne_eq_ray : σ.vertexOne = (σ.sideTanOne : ℂ) * exp ((σ.θ₃ : ℂ) * I) := rfl

theorem vertexTwo_eq_real : σ.vertexTwo = (σ.sideTanTwo : ℂ) := rfl

theorem ray_mem_triangle {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ σ.sideTanOne) :
    (t : ℂ) * exp ((σ.θ₃ : ℂ) * I) ∈ σ.triangle := by
  have h1 := σ.sideTanOne_pos
  have hpl : σ.eps * t ^ 2 < 1 := σ.eps_sq_lt_of_le ht0 ht σ.eps_sideTanOne_sq_lt
  refine ⟨by rw [mem_plane_iff, σ.norm_ray ht0]; exact hpl, fun i => ?_⟩
  fin_cases i
  · change 0 ≤ σ.wallSide 0 _
    rw [wallSide_zero_eq, ray_im]
    exact mul_nonneg ht0 σ.sin_θ₃_pos.le
  · change 0 ≤ σ.wallSide 1 _
    rw [wallSide_one_eq, ray_re, ray_im]
    nlinarith
  · change 0 ≤ σ.wallSide 2 _
    have hm := σ.wallSide_two_ray_mul t
    have hl := σ.eps_mul_lt_one ht0 h1.le hpl σ.eps_sideTanOne_sq_lt
    have hp : 0 ≤ σ.sideTanTwo * Real.sin σ.θ₂ * ((σ.sideTanOne - t) *
        (1 - σ.eps * t * σ.sideTanOne)) :=
      mul_nonneg (mul_pos σ.sideTanTwo_pos σ.sin_θ₂_pos).le
        (mul_nonneg (by linarith) (by rw [mul_assoc]; linarith))
    rw [← hm] at hp
    exact nonneg_of_mul_nonneg_right (by linarith) h1

theorem real_mem_triangle {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ σ.sideTanTwo) :
    (x : ℂ) ∈ σ.triangle := by
  have h2 := σ.sideTanTwo_pos
  have hpl : σ.eps * x ^ 2 < 1 := σ.eps_sq_lt_of_le hx0 hx σ.eps_sideTanTwo_sq_lt
  refine ⟨by rw [mem_plane_iff, Complex.norm_real, Real.norm_eq_abs, sq_abs]; exact hpl,
    fun i => ?_⟩
  fin_cases i
  · change 0 ≤ σ.wallSide 0 _
    rw [wallSide_zero_eq, ofReal_im]
  · change 0 ≤ σ.wallSide 1 _
    rw [wallSide_one_eq, ofReal_re, ofReal_im]
    nlinarith [σ.sin_θ₃_pos]
  · change 0 ≤ σ.wallSide 2 _
    rw [wallSide_two_real]
    have hl := σ.eps_mul_lt_one h2.le hx0 σ.eps_sideTanTwo_sq_lt hpl
    exact mul_nonneg σ.sin_θ₂_pos.le (mul_nonneg (by linarith) (by rw [mul_assoc]; linarith))

theorem zero_mem_triangle : (0 : ℂ) ∈ σ.triangle := by
  have := σ.real_mem_triangle le_rfl σ.sideTanTwo_pos.le
  rwa [ofReal_zero] at this

theorem vertexOne_mem_triangle : σ.vertexOne ∈ σ.triangle :=
  σ.ray_mem_triangle σ.sideTanOne_pos.le le_rfl

theorem vertexTwo_mem_triangle : σ.vertexTwo ∈ σ.triangle :=
  σ.real_mem_triangle σ.sideTanTwo_pos.le le_rfl

theorem norm_vertexOne : ‖σ.vertexOne‖ = σ.sideTanOne := σ.norm_ray σ.sideTanOne_pos.le

theorem vertexOne_ne_zero : σ.vertexOne ≠ 0 := by
  intro h
  have := σ.norm_vertexOne
  rw [h, norm_zero] at this
  linarith [σ.sideTanOne_pos]

theorem vertexTwo_ne_zero : σ.vertexTwo ≠ 0 := by
  rw [vertexTwo_eq_real, Ne, ofReal_eq_zero]
  exact σ.sideTanTwo_pos.ne'

theorem eq_ray_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 1 z = 0) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ σ.sideTanOne ∧ z = (t : ℂ) * exp ((σ.θ₃ : ℂ) * I) := by
  set t := z.re * Real.cos σ.θ₃ + z.im * Real.sin σ.θ₃ with ht
  have hs := σ.sin_θ₃_pos
  have hcs := Real.sin_sq_add_cos_sq σ.θ₃
  rw [wallSide_one_eq] at hw
  have hz' : z = (t : ℂ) * exp ((σ.θ₃ : ℂ) * I) := by
    apply Complex.ext
    · rw [ray_re, ht]
      linear_combination Real.sin σ.θ₃ * hw - z.re * hcs
    · rw [ray_im, ht]
      linear_combination (-Real.cos σ.θ₃) * hw - z.im * hcs
  have ht0 : 0 ≤ t := by
    have h0 := hz.2 0
    change 0 ≤ z.im at h0
    rw [hz', ray_im] at h0
    exact nonneg_of_mul_nonneg_left h0 hs
  refine ⟨t, ht0, ?_, hz'⟩
  have hpl : σ.eps * t ^ 2 < 1 := by
    have := hz.1
    rw [mem_plane_iff, hz', σ.norm_ray ht0] at this
    exact this
  have hl := σ.eps_mul_lt_one ht0 σ.sideTanOne_pos.le hpl σ.eps_sideTanOne_sq_lt
  have hm := σ.wallSide_two_ray_mul t
  rw [← hz'] at hm
  have h2 := mul_nonneg σ.sideTanOne_pos.le (hz.2 2)
  rw [hm] at h2
  have hq : 0 < σ.sideTanTwo * Real.sin σ.θ₂ := mul_pos σ.sideTanTwo_pos σ.sin_θ₂_pos
  have h3 := nonneg_of_mul_nonneg_right h2 hq
  have h4 : 0 < 1 - σ.eps * t * σ.sideTanOne := by rw [mul_assoc]; linarith
  have := nonneg_of_mul_nonneg_left h3 h4
  linarith

theorem eq_real_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 0 z = 0) :
    ∃ x : ℝ, 0 ≤ x ∧ x ≤ σ.sideTanTwo ∧ z = (x : ℂ) := by
  have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by rw [ofReal_im]; exact hw)
  have hx0 : 0 ≤ z.re := by
    have h1 := hz.2 1
    change 0 ≤ σ.wallSide 1 z at h1
    rw [wallSide_one_eq, show z.im = 0 from hw, mul_zero, sub_zero] at h1
    exact nonneg_of_mul_nonneg_right h1 σ.sin_θ₃_pos
  refine ⟨z.re, hx0, ?_, hz'⟩
  have hpl : σ.eps * z.re ^ 2 < 1 := by
    have := hz.1
    rw [mem_plane_iff, hz', Complex.norm_real, Real.norm_eq_abs, sq_abs] at this
    exact this
  have hl := σ.eps_mul_lt_one σ.sideTanTwo_pos.le hx0 σ.eps_sideTanTwo_sq_lt hpl
  have h2 := hz.2 2
  change 0 ≤ σ.wallSide 2 z at h2
  rw [hz', wallSide_two_real] at h2
  have h3 := nonneg_of_mul_nonneg_right h2 σ.sin_θ₂_pos
  have h4 : 0 < 1 - σ.eps * σ.sideTanTwo * z.re := by rw [mul_assoc]; linarith
  have := nonneg_of_mul_nonneg_left h3 h4
  linarith

theorem eq_vertexOne_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (h1 : σ.wallSide 1 z = 0)
    (h2 : σ.wallSide 2 z = 0) : z = σ.vertexOne := by
  obtain ⟨t, ht0, -, rfl⟩ := σ.eq_ray_of_wallOne hz h1
  have hpl : σ.eps * t ^ 2 < 1 := by
    have := hz.1
    rw [mem_plane_iff, σ.norm_ray ht0] at this
    exact this
  have hl := σ.eps_mul_lt_one ht0 σ.sideTanOne_pos.le hpl σ.eps_sideTanOne_sq_lt
  have hm := σ.wallSide_two_ray_mul t
  rw [h2, mul_zero] at hm
  have hq : σ.sideTanTwo * Real.sin σ.θ₂ ≠ 0 := (mul_pos σ.sideTanTwo_pos σ.sin_θ₂_pos).ne'
  have h4 : 1 - σ.eps * t * σ.sideTanOne ≠ 0 := by rw [mul_assoc]; linarith
  have := (mul_eq_zero.1 ((mul_eq_zero.1 hm.symm).resolve_left hq)).resolve_right h4
  rw [vertexOne_eq_ray, show t = σ.sideTanOne by linarith]

theorem eq_vertexTwo_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (h0 : σ.wallSide 0 z = 0)
    (h2 : σ.wallSide 2 z = 0) : z = σ.vertexTwo := by
  obtain ⟨x, hx0, -, rfl⟩ := σ.eq_real_of_wallZero hz h0
  have hpl : σ.eps * x ^ 2 < 1 := by
    have := hz.1
    rw [mem_plane_iff, Complex.norm_real, Real.norm_eq_abs, sq_abs] at this
    exact this
  have hl := σ.eps_mul_lt_one σ.sideTanTwo_pos.le hx0 σ.eps_sideTanTwo_sq_lt hpl
  rw [wallSide_two_real] at h2
  have h4 : 1 - σ.eps * σ.sideTanTwo * x ≠ 0 := by rw [mul_assoc]; linarith
  have := (mul_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left σ.sin_θ₂_pos.ne')).resolve_right h4
  rw [vertexTwo_eq_real, show x = σ.sideTanTwo by linarith]

theorem refl_eq_self {i : Fin 3} {z : ℂ} (hc : z ∈ σ.reflChart i) (hw : σ.wallSide i z = 0) :
    σ.refl i z = z := by
  fin_cases i
  · change conj z = z
    exact Complex.conj_eq_iff_im.2 hw
  · change exp (2 * (σ.θ₃ : ℂ) * I) * conj z = z
    change (exp ((σ.θ₃ : ℂ) * I) * conj z).im = 0 at hw
    have hr := Complex.conj_eq_iff_im.2 hw
    rw [map_mul, Complex.conj_conj, ← Complex.exp_conj] at hr
    have e : exp (2 * (σ.θ₃ : ℂ) * I) = exp ((σ.θ₃ : ℂ) * I) * exp ((σ.θ₃ : ℂ) * I) := by
      rw [← Complex.exp_add]
      ring_nf
    rw [e, mul_assoc, ← hr, ← mul_assoc, ← Complex.exp_add,
      show (σ.θ₃ : ℂ) * I + conj ((σ.θ₃ : ℂ) * I) = 0 by
        simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring,
      Complex.exp_zero, one_mul]
  · obtain ⟨hD, hE⟩ := hc
    change σ.discInv σ.vertexTwo (σ.reflTwoAux z) = z
    have hn : Complex.normSq (1 - σ.eps * conj σ.vertexTwo * z) ≠ 0 :=
      (Complex.normSq_pos.2 hD).ne'
    have him : (σ.rotTwo z).im = 0 := by
      have h := σ.wallSide_two_eq z
      change σ.wallSide 2 z = 0 at hw
      rw [hw] at h
      exact (mul_eq_zero.1 h.symm).resolve_right hn
    have hr := Complex.conj_eq_iff_im.2 him
    set w := σ.disc σ.vertexTwo z with hwdef
    have hc' : conj (exp ((σ.θ₂ : ℂ) * I)) = exp (-((σ.θ₂ : ℂ) * I)) := by
      rw [← Complex.exp_conj]
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
    have hr' : exp (-((σ.θ₂ : ℂ) * I)) * conj w = exp ((σ.θ₂ : ℂ) * I) * w := by
      have := hr
      simp only [rotTwo, map_neg, map_mul, hc', ← hwdef] at this
      exact neg_injective this
    have haux : σ.reflTwoAux z = w := by
      change exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj w = w
      rw [show -(2 * (σ.θ₂ : ℂ) * I) = -((σ.θ₂ : ℂ) * I) + -((σ.θ₂ : ℂ) * I) by ring,
        Complex.exp_add, mul_assoc, hr', ← mul_assoc, ← Complex.exp_add, neg_add_cancel,
        Complex.exp_zero, one_mul]
    rw [haux] at hE ⊢
    have hD' : 1 - z * (σ.eps : ℂ) * conj σ.vertexTwo ≠ 0 := by
      convert hD using 1
      ring
    rw [discInv, div_eq_iff hE, hwdef, disc]
    field_simp
    ring

theorem continuous_wallSide (i : Fin 3) : Continuous (σ.wallSide i) := by
  fin_cases i
  · exact Complex.continuous_im
  · have e : σ.wallSide 1 = fun z => Real.sin σ.θ₃ * z.re - Real.cos σ.θ₃ * z.im :=
      funext σ.wallSide_one_eq
    change Continuous (σ.wallSide 1)
    rw [e]
    fun_prop
  · have e : σ.wallSide 2 = fun z => Real.sin σ.θ₂ * (σ.sideTanTwo * (1 + σ.eps *
        (z.re ^ 2 + z.im ^ 2)) - z.re * (1 + σ.eps * σ.sideTanTwo ^ 2)) -
        Real.cos σ.θ₂ * z.im * (1 - σ.eps * σ.sideTanTwo ^ 2) := funext σ.wallSide_two_eq_poly
    change Continuous (σ.wallSide 2)
    rw [e]
    fun_prop

theorem isOpen_plane : IsOpen σ.plane :=
  isOpen_lt (continuous_const.mul (continuous_norm.pow 2)) continuous_const

theorem isOpen_openTriangle : IsOpen σ.openTriangle := by
  have e : σ.openTriangle = σ.plane ∩ ⋂ i, {z | 0 < σ.wallSide i z} := by
    ext z
    simp [openTriangle]
  rw [e]
  exact σ.isOpen_plane.inter (isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (σ.continuous_wallSide i))

theorem openTriangle_subset : σ.openTriangle ⊆ σ.triangle := fun _ hz =>
  ⟨hz.1, fun i => (hz.2 i).le⟩

theorem ne_of_mem_openTriangle {z : ℂ} (hz : z ∈ σ.openTriangle) :
    z ≠ 0 ∧ z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · have := hz.2 0
    rw [wallSide_zero_eq, zero_im] at this
    exact lt_irrefl 0 this
  · have := hz.2 2
    rw [σ.wallSide_two_vertexOne] at this
    exact lt_irrefl 0 this
  · have := hz.2 0
    rw [wallSide_zero_eq, vertexTwo_eq_real, ofReal_im] at this
    exact lt_irrefl 0 this

end CompactShape

end GC.Seifert
