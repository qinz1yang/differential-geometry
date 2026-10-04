import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryGenerators

/-!
# Reduction of the fold domain to the doubled triangle

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §3.3,
with review 21 §4.3). Every point `y` of the fold domain is related by `FoldRel` to a point over the
doubled triangle `σ.domain = T ∪ σ₀T` (`exists_foldRel_domain`): points of the wall patches by one
side pairing `γᵢ^{±1}`, points of the cone disc about `v₁` (or its mirror) by a power of the screw
`S₁` (rounding the angle of the disc coordinate to the sectors of `T` and `σ₁T`) followed by `γ₁`,
points of the cone disc about `v₂` by a power of `S₂` (rounding to the sectors of `T ∪ σ₀T`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace TwoConeFold

namespace Fold

open ConeShape

section Sector

variable {σ : ConeShape}

theorem mem_triangle_of_sector_one {z : ℂ} (hz : 0 < z.im) (hx : 0 ≤ z.re) {β : ℝ}
    (hω : coneDisc σ.vertexOne z = ‖coneDisc σ.vertexOne z‖ * exp ((β : ℂ) * I))
    (h0 : 0 ≤ β) (h1 : β ≤ σ.θ₁) : z ∈ σ.triangle := by
  have hnsq : 0 < normSq (z - conj σ.vertexOne) := normSq_sub_conj_pos σ.vertexOne_im_pos hz
  have hθ := σ.θ₁_le
  have hs := σ.sin_θ₁_pos
  have him : 0 ≤ (coneDisc σ.vertexOne z).im := by
    rw [hω]
    simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, exp_ofReal_mul_I_im]
    exact mul_nonneg (norm_nonneg _) (Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith))
  have hrot : (exp (-(σ.θ₁ * I)) * coneDisc σ.vertexOne z).im ≤ 0 := by
    rw [hω, show exp (-(σ.θ₁ * I)) * (‖coneDisc σ.vertexOne z‖ * exp ((β : ℂ) * I)) =
      ‖coneDisc σ.vertexOne z‖ * exp (((β - σ.θ₁ : ℝ) : ℂ) * I) by
        rw [mul_left_comm, ← exp_add]; push_cast; ring_nf]
    simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, exp_ofReal_mul_I_im]
    exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _)
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [σ.θ₁_pos]))
  refine ⟨hz, fun i => ?_⟩
  fin_cases i
  · exact hx
  · have := σ.im_coneDisc_vertexOne_mul z
    have hv := σ.vertexOne_im_pos
    change 0 ≤ σ.wallSide 1 z
    by_contra hneg
    push Not at hneg
    have : (coneDisc σ.vertexOne z).im * normSq (z - conj σ.vertexOne) < 0 := by
      rw [this]; nlinarith
    nlinarith
  · have := σ.im_rot_coneDisc_vertexOne_mul z
    change 0 ≤ σ.wallSide 2 z
    by_contra hneg
    push Not at hneg
    have : 0 < (exp (-(σ.θ₁ * I)) * coneDisc σ.vertexOne z).im *
        normSq (z - conj σ.vertexOne) := by
      rw [this]; nlinarith
    nlinarith

theorem mem_triangle_of_sector_two {z : ℂ} (hz : 0 < z.im) (hx : z.re ≤ σ.width)
    (hθ : 0 < σ.θ₂) {β : ℝ}
    (hξ : exp (σ.θ₂ * I) * coneDisc σ.vertexTwo z =
      ‖exp (σ.θ₂ * I) * coneDisc σ.vertexTwo z‖ * exp ((β : ℂ) * I))
    (h0 : 0 ≤ β) (h1 : β ≤ σ.θ₂) : z ∈ σ.triangle := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [σ.θ₂_le, Real.pi_pos])
  have hv : 0 < σ.vertexTwo.im := by rw [vertexTwo_im]; positivity
  have hnsq : 0 < normSq (z - conj σ.vertexTwo) := normSq_sub_conj_pos hv hz
  set r := ‖exp (σ.θ₂ * I) * coneDisc σ.vertexTwo z‖ with hr
  have hω : coneDisc σ.vertexTwo z = r * exp (((β - σ.θ₂ : ℝ) : ℂ) * I) := by
    have : coneDisc σ.vertexTwo z =
        exp (-(σ.θ₂ * I)) * (exp (σ.θ₂ * I) * coneDisc σ.vertexTwo z) := by
      rw [← mul_assoc, ← exp_add]; simp
    rw [this, hξ, mul_left_comm, ← exp_add]
    push_cast
    ring_nf
  have him : (coneDisc σ.vertexTwo z).im ≤ 0 := by
    rw [hω]
    simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, exp_ofReal_mul_I_im]
    exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _)
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [σ.θ₂_le, Real.pi_pos]))
  have hrot : (exp (-(((Real.pi - σ.θ₂ : ℝ) : ℂ) * I)) * coneDisc σ.vertexTwo z).im ≤ 0 := by
    rw [hω, show exp (-(((Real.pi - σ.θ₂ : ℝ) : ℂ) * I)) * (r * exp (((β - σ.θ₂ : ℝ) : ℂ) * I)) =
      r * exp (((β - Real.pi : ℝ) : ℂ) * I) by
        rw [mul_left_comm, ← exp_add]; push_cast; ring_nf]
    simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, exp_ofReal_mul_I_im]
    exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _)
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [σ.θ₂_le, Real.pi_pos])
        (by linarith))
  refine ⟨hz, fun i => ?_⟩
  fin_cases i
  · have := σ.im_coneDisc_vertexTwo_mul z
    change 0 ≤ σ.wallSide 0 z
    by_contra hneg
    push Not at hneg
    have : 0 < (coneDisc σ.vertexTwo z).im * normSq (z - conj σ.vertexTwo) := by
      rw [this]; nlinarith
    nlinarith
  · change 0 ≤ σ.width - z.re
    linarith
  · have := σ.im_rot_coneDisc_vertexTwo_mul z
    change 0 ≤ σ.wallSide 2 z
    by_contra hneg
    push Not at hneg
    have : 0 < (exp (-(((Real.pi - σ.θ₂ : ℝ) : ℂ) * I)) * coneDisc σ.vertexTwo z).im *
        normSq (z - conj σ.vertexTwo) := by
      rw [this]; nlinarith
    nlinarith

theorem exp_round {θ : ℝ} {P : ℕ} (hθP : θ * P = Real.pi) (hP : P ≠ 0) (α : ℝ) (c : ℝ) :
    ∃ j : ℕ, ∃ j₀ : ℤ, j₀ = ⌊(α + c) / (2 * θ)⌋ ∧
      exp (((-2 * (j : ℝ) * θ : ℝ) : ℂ) * I) = exp (((-2 * (j₀ : ℝ) * θ : ℝ) : ℂ) * I) := by
  set j₀ : ℤ := ⌊(α + c) / (2 * θ)⌋
  have hPz : (0 : ℤ) < P := by exact_mod_cast Nat.pos_of_ne_zero hP
  refine ⟨(j₀ % P).toNat, j₀, rfl, ?_⟩
  have hj : (((j₀ % P).toNat : ℕ) : ℤ) = j₀ - P * (j₀ / P) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hPz.ne'), Int.emod_def]
  have hjr : (((j₀ % P).toNat : ℕ) : ℝ) = (j₀ : ℝ) - P * ((j₀ / P : ℤ) : ℝ) := by
    exact_mod_cast hj
  rw [hjr]
  have : ((-2 * ((j₀ : ℝ) - P * ((j₀ / P : ℤ) : ℝ)) * θ : ℝ) : ℂ) * I =
      ((-2 * (j₀ : ℝ) * θ : ℝ) : ℂ) * I + ((j₀ / P : ℤ) : ℂ) * (2 * Real.pi * I) := by
    rw [← hθP]; push_cast; ring
  rw [this, exp_add, exp_int_mul_two_pi_mul_I, mul_one]

theorem polar_rot (η : ℂ) (t : ℝ) :
    exp ((t : ℂ) * I) * η = ‖exp ((t : ℂ) * I) * η‖ * exp (((arg η + t : ℝ) : ℂ) * I) := by
  rw [norm_mul, norm_exp_ofReal_mul_I, one_mul]
  conv_lhs => rw [← norm_mul_exp_arg_mul_I η]
  push_cast
  rw [add_mul, exp_add]
  ring

theorem polar_conj {w : ℂ} {β : ℝ} (hw : w = ‖w‖ * exp ((β : ℂ) * I)) :
    conj w = ‖conj w‖ * exp (((-β : ℝ) : ℂ) * I) := by
  rw [norm_conj]
  conv_lhs => rw [hw]
  rw [map_mul, conj_ofReal, ← exp_conj, map_mul, conj_ofReal, conj_I]
  push_cast
  ring_nf

theorem polar_conj_rot {w : ℂ} {β : ℝ} (hw : w = ‖w‖ * exp ((β : ℂ) * I)) (t : ℝ) :
    exp ((t : ℂ) * I) * conj w =
      ‖exp ((t : ℂ) * I) * conj w‖ * exp (((t - β : ℝ) : ℂ) * I) := by
  have hc := polar_conj hw
  rw [norm_conj] at hc
  rw [norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_conj]
  conv_lhs => rw [hc]
  rw [mul_left_comm, ← exp_add]
  push_cast
  ring_nf

theorem xi_refl_zero (z : ℂ) :
    exp (σ.θ₂ * I) * coneDisc σ.vertexTwo (σ.refl 0 z) =
      exp (((2 * σ.θ₂ : ℝ) : ℂ) * I) * conj (exp (σ.θ₂ * I) * coneDisc σ.vertexTwo z) := by
  rw [σ.coneDisc_vertexTwo_refl_zero, map_mul, ← exp_conj, map_mul, conj_ofReal, conj_I,
    ← mul_assoc, ← exp_add]
  congr 2
  push_cast
  ring

theorem refl_zero_mem_domain_iff {z : ℂ} : σ.refl 0 z ∈ σ.domain ↔ z ∈ σ.domain := by
  rw [σ.mem_domain_iff, σ.mem_domain_iff, σ.refl_zero_refl_zero]
  exact or_comm

end Sector

theorem zOf_im_pos (p : ModelCoordinates) : 0 < (zOf p).im := (logPoint p).2

section Reduce

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (m₁ m₂ : Fin d.fillingCount) (hk : d.k = 3)
  (hj : ∀ m : Fin d.fillingCount, (C.port (.inr m)).val ≠ 0)
  (hp : ∀ m : Fin d.fillingCount, 0 < (d.fillingSlope m).1)
  {σ : ConeShape} (D : σ.FoldData)
  (hθ₁ : σ.θ₁ * (chartNumbers C m₁ m₂).p₁ = Real.pi)
  (hθ₂ : σ.θ₂ * (chartNumbers C m₁ m₂).p₂ = Real.pi)
  (hc₁ : C.tubeCentre m₁ = ((3 / 2 : ℝ) : ℂ)) (hc₂ : C.tubeCentre m₂ = ((-(3 / 2) : ℝ) : ℂ))

theorem rhoZero_rhoZero (c : ℝ) (p : ModelCoordinates) : rhoZero c (rhoZero c p) = p :=
  flipMap_flipMap c p

theorem rhoOne_rhoOne (p : ModelCoordinates) : rhoOne σ (rhoOne σ p) = p :=
  point_ext (by rw [zOf_rhoOne, zOf_rhoOne, σ.refl_refl (zOf_im_pos p) 1])
    (by rw [rhoOne_two, rhoOne_two, neg_neg])

theorem rhoTwo_rhoTwo (c : ℝ) (p : ModelCoordinates) : rhoTwo σ c (rhoTwo σ c p) = p :=
  point_ext (by rw [zOf_rhoTwo σ c _ (zOf_im_pos _), zOf_rhoTwo σ c _ (zOf_im_pos _),
      σ.refl_refl (zOf_im_pos p) 2])
    (by rw [rhoTwo_two, rhoTwo_two]; ring)

theorem gammaOne_inv (y : ModelCoordinates) :
    gammaOne C m₁ m₂ (σ := σ) (rhoOne σ (rhoZero (chartNumbers C m₁ m₂).c₀ y)) = y := by
  change rhoZero (chartNumbers C m₁ m₂).c₀
    (rhoOne σ (rhoOne σ (rhoZero (chartNumbers C m₁ m₂).c₀ y))) = y
  rw [rhoOne_rhoOne, rhoZero_rhoZero]

theorem gammaTwo_inv (y : ModelCoordinates) :
    gammaTwo C m₁ m₂ (σ := σ)
      (rhoTwo σ (chartNumbers C m₁ m₂).k₁ (rhoZero (chartNumbers C m₁ m₂).c₀ y)) = y := by
  change rhoZero (chartNumbers C m₁ m₂).c₀ (rhoTwo σ (chartNumbers C m₁ m₂).k₁
    (rhoTwo σ (chartNumbers C m₁ m₂).k₁ (rhoZero (chartNumbers C m₁ m₂).c₀ y))) = y
  rw [rhoTwo_rhoTwo, rhoZero_rhoZero]

theorem zOf_screwOne (p : ModelCoordinates) :
    zOf (screwOne C m₁ m₂ (σ := σ) p) = σ.refl 1 (σ.refl 2 (zOf p)) := by
  change zOf (rhoOne σ (rhoTwo σ (chartNumbers C m₁ m₂).k₁ p)) = _
  rw [zOf_rhoOne, zOf_rhoTwo σ _ p (zOf_im_pos p)]

theorem screwOne_two (p : ModelCoordinates) :
    screwOne C m₁ m₂ (σ := σ) p 2 = p 2 - (chartNumbers C m₁ m₂).k₁ := by
  change rhoOne σ (rhoTwo σ (chartNumbers C m₁ m₂).k₁ p) 2 = _
  rw [rhoOne_two, rhoTwo_two]
  ring

theorem zOf_screwTwo (p : ModelCoordinates) :
    zOf (screwTwo C m₁ m₂ (σ := σ) p) = σ.refl 2 (σ.refl 0 (zOf p)) := by
  change zOf (rhoTwo σ (chartNumbers C m₁ m₂).k₁ (rhoZero (chartNumbers C m₁ m₂).c₀ p)) = _
  rw [zOf_rhoTwo σ _ _ (zOf_im_pos _), zOf_rhoZero]

theorem screwTwo_two (p : ModelCoordinates) :
    screwTwo C m₁ m₂ (σ := σ) p 2 = p 2 - (chartNumbers C m₁ m₂).k₂ := by
  change rhoTwo σ (chartNumbers C m₁ m₂).k₁ (rhoZero (chartNumbers C m₁ m₂).c₀ p) 2 = _
  rw [rhoTwo_two, rhoZero_two, Numbers.c₀]
  ring

theorem screwOne_iter {y : ModelCoordinates} (hy : zOf y ∈ discOne D hθ₁) (j : ℕ) :
    zOf ((screwOne C m₁ m₂ (σ := σ))^[j] y) ∈ discOne D hθ₁ ∧
      coneDisc σ.vertexOne (zOf ((screwOne C m₁ m₂ (σ := σ))^[j] y)) =
        exp (((-2 * (j : ℝ) * σ.θ₁ : ℝ) : ℂ) * I) * coneDisc σ.vertexOne (zOf y) := by
  induction j with
  | zero => simpa using hy
  | succ j ih =>
    rw [Function.iterate_succ_apply', zOf_screwOne]
    refine ⟨rot_mem_discOne D hθ₁ ih.1, ?_⟩
    rw [coneDisc_rot_one (zOf_im_pos _), ih.2, ← mul_assoc, ← exp_add]
    congr 2
    push_cast
    ring

theorem screwTwo_iter {y : ModelCoordinates} (hy : zOf y ∈ discTwo D hθ₂) (j : ℕ) :
    zOf ((screwTwo C m₁ m₂ (σ := σ))^[j] y) ∈ discTwo D hθ₂ ∧
      coneDisc σ.vertexTwo (zOf ((screwTwo C m₁ m₂ (σ := σ))^[j] y)) =
        exp (((-2 * (j : ℝ) * σ.θ₂ : ℝ) : ℂ) * I) * coneDisc σ.vertexTwo (zOf y) := by
  induction j with
  | zero => simpa using hy
  | succ j ih =>
    rw [Function.iterate_succ_apply', zOf_screwTwo]
    refine ⟨rot_mem_discTwo D hθ₂ ih.1, ?_⟩
    rw [coneDisc_rot_two (zOf_im_pos _), ih.2, ← mul_assoc, ← exp_add]
    congr 2
    push_cast
    ring

include hp in
theorem foldRel_screwOne_iter {y : ModelCoordinates} (hy : zOf y ∈ discOne D hθ₁) (j : ℕ) :
    FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
      (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y ((screwOne C m₁ m₂ (σ := σ))^[j] y) := by
  induction j with
  | zero => exact FoldRel.refl' (foldDomain C m₁ m₂ D hθ₁ hθ₂).isOpen (Or.inl (Or.inl (Or.inr hy)))
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (foldRel_screwOne C m₁ m₂ hk hp D hθ₁ hθ₂ (screwOne_iter C m₁ m₂ D hθ₁ hy j).1)

include hp in
theorem foldRel_screwTwo_iter {y : ModelCoordinates} (hy : zOf y ∈ discTwo D hθ₂) (j : ℕ) :
    FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
      (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y ((screwTwo C m₁ m₂ (σ := σ))^[j] y) := by
  induction j with
  | zero => exact FoldRel.refl' (foldDomain C m₁ m₂ D hθ₁ hθ₂).isOpen (Or.inr hy)
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (foldRel_screwTwo C m₁ m₂ hk hp D hθ₁ hθ₂ (screwTwo_iter C m₁ m₂ D hθ₂ hy j).1)

include hp in
theorem exists_foldRel_of_discOne {y : ModelCoordinates} (hy : zOf y ∈ discOne D hθ₁) :
    ∃ y₀, zOf y₀ ∈ σ.domain ∧
      FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
        (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y y₀ := by
  have hθpos : 0 < σ.θ₁ := σ.θ₁_pos
  obtain ⟨j, j₀, hj₀, hexp⟩ := exp_round hθ₁ (p₁_ne_zero hθ₁)
    (arg (coneDisc σ.vertexOne (zOf y))) σ.θ₁
  obtain ⟨hd₁, hη₁⟩ := screwOne_iter C m₁ m₂ D hθ₁ hy j
  have hrel := foldRel_screwOne_iter C m₁ m₂ hk hp D hθ₁ hθ₂ hy j
  set y₁ := (screwOne C m₁ m₂ (σ := σ))^[j] y with hy₁
  set β := arg (coneDisc σ.vertexOne (zOf y)) + (-2 * (j₀ : ℝ) * σ.θ₁) with hβ
  have hpol : coneDisc σ.vertexOne (zOf y₁) =
      ‖coneDisc σ.vertexOne (zOf y₁)‖ * exp ((β : ℂ) * I) := by
    rw [hη₁, hexp]
    exact polar_rot _ _
  have hfl := Int.floor_le ((arg (coneDisc σ.vertexOne (zOf y)) + σ.θ₁) / (2 * σ.θ₁))
  have hlt := Int.lt_floor_add_one ((arg (coneDisc σ.vertexOne (zOf y)) + σ.θ₁) / (2 * σ.θ₁))
  rw [← hj₀] at hfl hlt
  have h2θ : 0 < 2 * σ.θ₁ := by positivity
  rw [le_div_iff₀ h2θ] at hfl
  rw [div_lt_iff₀ h2θ] at hlt
  have hβlo : -σ.θ₁ ≤ β := by rw [hβ]; nlinarith
  have hβhi : β < σ.θ₁ := by rw [hβ]; nlinarith
  rcases le_or_gt 0 β with h0 | h0
  · refine ⟨y₁, Or.inl (mem_triangle_of_sector_one (zOf_im_pos _) ?_ hpol h0 hβhi.le), hrel⟩
    linarith [re_of_mem_discOne D hθ₁ hd₁, σ.width_pos]
  · refine ⟨gammaOne C m₁ m₂ (σ := σ) y₁, ?_,
      hrel.trans (foldRel_gammaOne_disc C m₁ m₂ hk D hθ₁ hθ₂ hd₁)⟩
    rw [zOf_gammaOne, refl_zero_mem_domain_iff]
    refine Or.inl (mem_triangle_of_sector_one (β := -β) (σ.refl_im_pos (zOf_im_pos _) 1) ?_ ?_
      (by linarith) (by linarith))
    · linarith [re_of_mem_discOne D hθ₁ (refl_one_mem_discOne D hθ₁ hd₁), σ.width_pos]
    · rw [σ.coneDisc_vertexOne_refl_one]
      exact polar_conj hpol

include hp in
theorem exists_foldRel_of_discTwo {y : ModelCoordinates} (hy : zOf y ∈ discTwo D hθ₂) :
    ∃ y₀, zOf y₀ ∈ σ.domain ∧
      FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
        (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y y₀ := by
  have hθpos : 0 < σ.θ₂ := θ₂_pos hθ₂
  obtain ⟨j, j₀, hj₀, hexp⟩ := exp_round hθ₂ (p₂_ne_zero hθ₂)
    (arg (exp (σ.θ₂ * I) * coneDisc σ.vertexTwo (zOf y))) 0
  obtain ⟨hd₁, hη₁⟩ := screwTwo_iter C m₁ m₂ D hθ₂ hy j
  have hrel := foldRel_screwTwo_iter C m₁ m₂ hk hp D hθ₁ hθ₂ hy j
  set y₁ := (screwTwo C m₁ m₂ (σ := σ))^[j] y with hy₁
  set β := arg (exp (σ.θ₂ * I) * coneDisc σ.vertexTwo (zOf y)) + (-2 * (j₀ : ℝ) * σ.θ₂)
    with hβ
  have hpol : exp (σ.θ₂ * I) * coneDisc σ.vertexTwo (zOf y₁) =
      ‖exp (σ.θ₂ * I) * coneDisc σ.vertexTwo (zOf y₁)‖ * exp ((β : ℂ) * I) := by
    rw [hη₁, hexp, mul_left_comm]
    exact polar_rot _ _
  have hfl := Int.floor_le ((arg (exp (σ.θ₂ * I) * coneDisc σ.vertexTwo (zOf y)) + 0) /
    (2 * σ.θ₂))
  have hlt := Int.lt_floor_add_one ((arg (exp (σ.θ₂ * I) * coneDisc σ.vertexTwo (zOf y)) + 0) /
    (2 * σ.θ₂))
  rw [← hj₀] at hfl hlt
  have h2θ : 0 < 2 * σ.θ₂ := by positivity
  rw [le_div_iff₀ h2θ] at hfl
  rw [div_lt_iff₀ h2θ] at hlt
  have hβlo : 0 ≤ β := by rw [hβ]; nlinarith
  have hβhi : β < 2 * σ.θ₂ := by rw [hβ]; nlinarith
  have hx := abs_lt.1 (re_of_mem_discTwo D hθ₂ hd₁)
  have hW := σ.width_pos
  refine ⟨y₁, ?_, hrel⟩
  rcases le_or_gt β σ.θ₂ with h1 | h1
  · exact Or.inl (mem_triangle_of_sector_two (zOf_im_pos _) (by linarith) hθpos hpol hβlo h1)
  · rw [← refl_zero_mem_domain_iff]
    refine Or.inl (mem_triangle_of_sector_two (β := 2 * σ.θ₂ - β) (σ.refl_im_pos (zOf_im_pos _) 0)
      (by rw [refl_zero_re]; linarith) hθpos ?_ (by linarith) (by linarith))
    rw [xi_refl_zero]
    exact polar_conj_rot hpol _

theorem mem_cases_of_main {w : ℂ} (hw : w ∈ mainSet D hθ₁ hθ₂) :
    w ∈ σ.domain ∨ (w ∈ patchOne D hθ₁ ∧ σ.refl 1 w ∈ σ.triangle) ∨
      (w ∈ patchTwo D hθ₁ hθ₂ ∧ σ.refl 2 w ∈ σ.triangle) := by
  have hW := σ.width_pos
  rcases hw with ((h | h) | h) | h
  · exact Or.inl (Or.inl ⟨h.1, fun i => (h.2 i).le⟩)
  · obtain ⟨h0, -, hx, hw2, hw2', -, -⟩ := h
    have hx' := abs_lt.1 hx
    rcases le_or_gt 0 w.re with hre | hre
    · refine Or.inl (Or.inl ⟨h0, fun i => ?_⟩)
      fin_cases i
      · exact hre
      · change 0 ≤ σ.width - w.re
        linarith
      · exact hw2.le
    · refine Or.inl (σ.mem_domain_iff.2 (Or.inr ⟨σ.refl_im_pos h0 0, fun i => ?_⟩))
      fin_cases i
      · change 0 ≤ (σ.refl 0 w).re
        rw [refl_zero_re]
        linarith
      · change 0 ≤ σ.width - (σ.refl 0 w).re
        rw [refl_zero_re]
        linarith
      · exact hw2'.le
  · have h' := h
    obtain ⟨h0, -, hx1, hx2, hw2, hw2', -, -⟩ := h
    have hr1 : (σ.refl 1 w).re = 2 * σ.width - w.re := by simp [ConeShape.refl]
    rcases le_or_gt w.re σ.width with hre | hre
    · refine Or.inl (Or.inl ⟨h0, fun i => ?_⟩)
      fin_cases i
      · change 0 ≤ w.re
        linarith
      · change 0 ≤ σ.width - w.re
        linarith
      · exact hw2.le
    · refine Or.inr (Or.inl ⟨h', σ.refl_im_pos h0 1, fun i => ?_⟩)
      fin_cases i
      · change 0 ≤ (σ.refl 1 w).re
        linarith
      · change 0 ≤ σ.width - (σ.refl 1 w).re
        linarith
      · exact hw2'.le
  · have h' := h
    obtain ⟨h0, -, hx1, hx2, hy1, hy2, -, -, -, -⟩ := h
    rcases le_or_gt 0 (σ.wallSide 2 w) with hs | hs
    · refine Or.inl (Or.inl ⟨h0, fun i => ?_⟩)
      fin_cases i
      · exact hx1.le
      · change 0 ≤ σ.width - w.re
        linarith
      · exact hs
    · refine Or.inr (Or.inr ⟨h', σ.refl_im_pos h0 2, fun i => ?_⟩)
      fin_cases i
      · exact hy1.le
      · change 0 ≤ σ.width - (σ.refl 2 w).re
        linarith
      · change 0 ≤ σ.wallSide 2 (σ.refl 2 w)
        rw [σ.wallSide_refl_two h0]
        have hn : 0 < normSq (w - σ.centre) := normSq_pos.2 (σ.centre_ne h0)
        exact (div_pos (by linarith) (by positivity)).le

include hj hp hc₁ hc₂ in
theorem exists_foldRel_of_main {y : ModelCoordinates} (hy : zOf y ∈ mainSet D hθ₁ hθ₂) :
    ∃ y₀, zOf y₀ ∈ σ.domain ∧
      FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
        (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y y₀ := by
  rcases mem_cases_of_main C m₁ m₂ D hθ₁ hθ₂ hy with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨y, h, FoldRel.refl' (foldDomain C m₁ m₂ D hθ₁ hθ₂).isOpen
      (Or.inl (Or.inl (Or.inl (Or.inl hy))))⟩
  · refine ⟨gammaOne C m₁ m₂ (σ := σ) y, ?_,
      foldRel_gammaOne_patch C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ h1⟩
    rw [zOf_gammaOne, refl_zero_mem_domain_iff]
    exact Or.inl h2
  · refine ⟨gammaTwo C m₁ m₂ (σ := σ) y, ?_,
      foldRel_gammaTwo C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ h1⟩
    rw [zOf_gammaTwo C m₁ m₂ y (zOf_im_pos y), refl_zero_mem_domain_iff]
    exact Or.inl h2

include hj hp hc₁ hc₂ in
theorem exists_foldRel_of_mirrorMain {y : ModelCoordinates}
    (hy : zOf y ∈ mirrorSet σ (mainSet D hθ₁ hθ₂)) :
    ∃ y₀, zOf y₀ ∈ σ.domain ∧
      FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
        (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y y₀ := by
  rcases mem_cases_of_main C m₁ m₂ D hθ₁ hθ₂ hy.2 with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨y, refl_zero_mem_domain_iff.1 h, FoldRel.refl' (foldDomain C m₁ m₂ D hθ₁ hθ₂).isOpen
      (Or.inl (Or.inl (Or.inl (Or.inr hy))))⟩
  · have hzx : zOf (rhoOne σ (rhoZero (chartNumbers C m₁ m₂).c₀ y)) =
        σ.refl 1 (σ.refl 0 (zOf y)) := by
      rw [zOf_rhoOne, zOf_rhoZero]
    have hrel := foldRel_gammaOne_patch C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂
      (y := rhoOne σ (rhoZero (chartNumbers C m₁ m₂).c₀ y))
      (by rw [hzx]; exact refl_one_mem_patchOne D hθ₁ h1)
    rw [gammaOne_inv] at hrel
    exact ⟨_, by rw [hzx]; exact Or.inl h2, hrel.symm⟩
  · have hzx : zOf (rhoTwo σ (chartNumbers C m₁ m₂).k₁ (rhoZero (chartNumbers C m₁ m₂).c₀ y)) =
        σ.refl 2 (σ.refl 0 (zOf y)) := by
      rw [zOf_rhoTwo σ _ _ (zOf_im_pos _), zOf_rhoZero]
    have hrel := foldRel_gammaTwo C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂
      (y := rhoTwo σ (chartNumbers C m₁ m₂).k₁ (rhoZero (chartNumbers C m₁ m₂).c₀ y))
      (by rw [hzx]; exact refl_two_mem_patchTwo D hθ₁ hθ₂ h1)
    rw [gammaTwo_inv] at hrel
    exact ⟨_, by rw [hzx]; exact Or.inl h2, hrel.symm⟩

include hp in
theorem exists_foldRel_of_mirrorDiscOne {y : ModelCoordinates}
    (hy : zOf y ∈ mirrorSet σ (discOne D hθ₁)) :
    ∃ y₀, zOf y₀ ∈ σ.domain ∧
      FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
        (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y y₀ := by
  have hzx : zOf (rhoOne σ (rhoZero (chartNumbers C m₁ m₂).c₀ y)) ∈ discOne D hθ₁ := by
    rw [zOf_rhoOne, zOf_rhoZero]
    exact refl_one_mem_discOne D hθ₁ hy.2
  have hrel := foldRel_gammaOne_disc C m₁ m₂ hk D hθ₁ hθ₂ hzx
  rw [gammaOne_inv] at hrel
  obtain ⟨y₀, hy₀, hrel₀⟩ := exists_foldRel_of_discOne C m₁ m₂ hk hp D hθ₁ hθ₂ hzx
  exact ⟨y₀, hy₀, hrel.symm.trans hrel₀⟩

include hj hp hc₁ hc₂ in
theorem exists_foldRel_domain {y : ModelCoordinates} (hy : y ∈ foldDomain C m₁ m₂ D hθ₁ hθ₂) :
    ∃ y₀, zOf y₀ ∈ σ.domain ∧
      FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
        (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y y₀ := by
  rcases hy with (((h | h) | h) | h) | h
  · exact exists_foldRel_of_main C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ h
  · exact exists_foldRel_of_mirrorMain C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ h
  · exact exists_foldRel_of_discOne C m₁ m₂ hk hp D hθ₁ hθ₂ h
  · exact exists_foldRel_of_mirrorDiscOne C m₁ m₂ hk hp D hθ₁ hθ₂ h
  · exact exists_foldRel_of_discTwo C m₁ m₂ hk hp D hθ₁ hθ₂ h

end Reduce

end Fold

end TwoConeFold

end GC.Seifert
