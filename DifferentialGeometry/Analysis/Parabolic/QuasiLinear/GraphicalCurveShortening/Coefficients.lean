import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening

open scoped ContDiff

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E]

theorem graphDiffusionCoefficient_lower_bound {p : E} {R : ℝ} (hp : ‖p‖ ≤ R) :
    (1 + R ^ 2)⁻¹ ≤ graphDiffusionCoefficient p := by
  unfold graphDiffusionCoefficient
  apply (inv_le_inv₀ (by positivity) (by positivity)).2
  have hR : 0 ≤ R := (norm_nonneg p).trans hp
  nlinarith only [hp, norm_nonneg p, hR]

private theorem inv_one_add_sq_sub_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |(1 + a ^ 2)⁻¹ - (1 + b ^ 2)⁻¹| ≤ |a - b| := by
  have hden : 0 < (1 + a ^ 2) * (1 + b ^ 2) := by positivity
  have hsum : a + b ≤ (1 + a ^ 2) * (1 + b ^ 2) := by
    nlinarith only [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2),
      mul_nonneg (sq_nonneg a) (sq_nonneg b)]
  rw [inv_sub_inv (by positivity) (by positivity), abs_div, abs_of_pos hden]
  have hnum : |1 + b ^ 2 - (1 + a ^ 2)| = (a + b) * |a - b| := by
    rw [show 1 + b ^ 2 - (1 + a ^ 2) = (a + b) * (b - a) by ring,
      abs_mul, abs_of_nonneg (add_nonneg ha hb), abs_sub_comm]
  rw [hnum, div_le_iff₀ hden]
  nlinarith only [mul_le_mul_of_nonneg_right hsum (abs_nonneg (a - b))]

theorem graphDiffusionCoefficient_lipschitz :
    LipschitzWith 1 (graphDiffusionCoefficient (E := E)) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs, graphDiffusionCoefficient] using
    (inv_one_add_sq_sub_bound (norm_nonneg p) (norm_nonneg q)).trans
      (abs_norm_sub_norm_le p q)

theorem graphDiffusionCoefficient_smul_sub_bound {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (p q : E) (r s : F) :
    ‖graphDiffusionCoefficient p • r - graphDiffusionCoefficient q • s‖ ≤
      ‖r - s‖ + ‖p - q‖ * ‖s‖ := by
  have heq : graphDiffusionCoefficient p • r - graphDiffusionCoefficient q • s =
      graphDiffusionCoefficient p • (r - s) +
        (graphDiffusionCoefficient p - graphDiffusionCoefficient q) • s := by
    simp only [smul_sub, sub_smul]
    abel
  rw [heq]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (graphDiffusionCoefficient_pos p)]
  apply add_le_add
  · exact (mul_le_mul_of_nonneg_right (graphDiffusionCoefficient_le_one p)
      (norm_nonneg (r - s))).trans_eq (one_mul _)
  · apply mul_le_mul_of_nonneg_right _ (norm_nonneg s)
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs, graphDiffusionCoefficient] using
      (graphDiffusionCoefficient_lipschitz (E := E)).dist_le_mul p q

theorem graphDiffusionCoefficient_sub_one_bound (p : E) :
    |graphDiffusionCoefficient p - 1| ≤ ‖p‖ ^ 2 := by
  have hpos : 0 < 1 + ‖p‖ ^ 2 := by positivity
  have heq : graphDiffusionCoefficient p - 1 = -(‖p‖ ^ 2 / (1 + ‖p‖ ^ 2)) := by
    dsimp [graphDiffusionCoefficient]
    field_simp
    ring
  rw [heq, abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ hpos]
  nlinarith only [sq_nonneg (‖p‖ ^ 2)]

theorem graphDiffusionCoefficient_remainder_sub_bound {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (p q : E) (r s : F) :
    ‖(graphDiffusionCoefficient p - 1) • r - (graphDiffusionCoefficient q - 1) • s‖ ≤
      ‖p‖ ^ 2 * ‖r - s‖ + ‖p - q‖ * ‖s‖ := by
  have heq : (graphDiffusionCoefficient p - 1) • r -
      (graphDiffusionCoefficient q - 1) • s =
      (graphDiffusionCoefficient p - 1) • (r - s) +
        (graphDiffusionCoefficient p - graphDiffusionCoefficient q) • s := by
    simp only [smul_sub, sub_smul, one_smul]
    abel
  rw [heq]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (graphDiffusionCoefficient_sub_one_bound p)
      (norm_nonneg (r - s))
  · apply mul_le_mul_of_nonneg_right _ (norm_nonneg s)
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs, graphDiffusionCoefficient] using
      (graphDiffusionCoefficient_lipschitz (E := E)).dist_le_mul p q

theorem contDiff_graphDiffusionCoefficient [InnerProductSpace ℝ E] :
    ContDiff ℝ ∞ (graphDiffusionCoefficient (E := E)) := by
  exact (contDiff_const.add (contDiff_id.norm_sq ℝ)).inv (fun p => by positivity)

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E]

private theorem inv_one_add_sq_sub_local {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |(1 + a ^ 2)⁻¹ - (1 + b ^ 2)⁻¹| ≤ (a + b) * |a - b| := by
  have hden : 0 < (1 + a ^ 2) * (1 + b ^ 2) := by positivity
  rw [inv_sub_inv (by positivity) (by positivity), abs_div, abs_of_pos hden]
  have hnum : |1 + b ^ 2 - (1 + a ^ 2)| = (a + b) * |a - b| := by
    rw [show 1 + b ^ 2 - (1 + a ^ 2) = (a + b) * (b - a) by ring,
      abs_mul, abs_of_nonneg (add_nonneg ha hb), abs_sub_comm]
  rw [hnum]
  exact (div_le_self (mul_nonneg (add_nonneg ha hb) (abs_nonneg (a - b)))
    (by nlinarith only [sq_nonneg a, sq_nonneg b,
      mul_nonneg (sq_nonneg a) (sq_nonneg b)]))

theorem graphDiffusionCoefficient_local_lipschitz {p q : E} :
    |graphDiffusionCoefficient p - graphDiffusionCoefficient q| ≤
      (‖p‖ + ‖q‖) * ‖p - q‖ := by
  have h := inv_one_add_sq_sub_local (norm_nonneg p) (norm_nonneg q)
  rw [show graphDiffusionCoefficient p = (1 + ‖p‖ ^ 2)⁻¹ by rfl,
    show graphDiffusionCoefficient q = (1 + ‖q‖ ^ 2)⁻¹ by rfl]
  exact h.trans (mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le p q)
    (add_nonneg (norm_nonneg p) (norm_nonneg q)))

theorem graphDiffusionCoefficient_remainder_small_slope_bound {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {p q : E} {R : ℝ}
    (hp : ‖p‖ ≤ R) (hq : ‖q‖ ≤ R) (r s : F) :
    ‖(graphDiffusionCoefficient p - 1) • r - (graphDiffusionCoefficient q - 1) • s‖ ≤
      R ^ 2 * ‖r - s‖ + (2 * R) * ‖p - q‖ * ‖s‖ := by
  have hR : 0 ≤ R := (norm_nonneg p).trans hp
  have heq : (graphDiffusionCoefficient p - 1) • r -
      (graphDiffusionCoefficient q - 1) • s =
      (graphDiffusionCoefficient p - 1) • (r - s) +
        (graphDiffusionCoefficient p - graphDiffusionCoefficient q) • s := by
    simp only [smul_sub, sub_smul, one_smul]
    abel
  rw [heq]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (norm_nonneg (r - s))
    apply (graphDiffusionCoefficient_sub_one_bound p).trans
    nlinarith only [hp, norm_nonneg p, hR]
  · apply mul_le_mul_of_nonneg_right _ (norm_nonneg s)
    apply graphDiffusionCoefficient_local_lipschitz.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg (p - q))
    linarith

end DifferentialGeometry.Analysis.Parabolic

open scoped InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem graphDiffusionCoefficient_deriv_sub_bound (p q v w : E) :
    |(-2 * graphDiffusionCoefficient p ^ 2 * ⟪p, v⟫_ℝ) -
      (-2 * graphDiffusionCoefficient q ^ 2 * ⟪q, w⟫_ℝ)| ≤
      2 * ‖p‖ * ‖v - w‖ +
        (2 + 4 * (‖p‖ + ‖q‖) * ‖q‖) * ‖p - q‖ * ‖w‖ := by
  let a := graphDiffusionCoefficient p
  let b := graphDiffusionCoefficient q
  have ha : 0 ≤ a := (graphDiffusionCoefficient_pos p).le
  have hb : 0 ≤ b := (graphDiffusionCoefficient_pos q).le
  have ha1 : a ≤ 1 := graphDiffusionCoefficient_le_one p
  have hb1 : b ≤ 1 := graphDiffusionCoefficient_le_one q
  have hinner_vw : |⟪p, v - w⟫_ℝ| ≤ ‖p‖ * ‖v - w‖ := by
    simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) p (v - w))
  have hinner_pq : |⟪p - q, w⟫_ℝ| ≤ ‖p - q‖ * ‖w‖ := by
    simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) (p - q) w)
  have hinner_qw : |⟪q, w⟫_ℝ| ≤ ‖q‖ * ‖w‖ := by
    simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) q w)
  have hab : |a - b| ≤ (‖p‖ + ‖q‖) * ‖p - q‖ := by
    simpa only [a, b] using graphDiffusionCoefficient_local_lipschitz (p := p) (q := q)
  have habsq : |a ^ 2 - b ^ 2| ≤
      2 * (‖p‖ + ‖q‖) * ‖p - q‖ := by
    rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul,
      abs_of_nonneg (add_nonneg ha hb)]
    calc
      |a - b| * (a + b) ≤
          ((‖p‖ + ‖q‖) * ‖p - q‖) * 2 := by
            exact mul_le_mul hab (by linarith) (add_nonneg ha hb) (by positivity)
      _ = 2 * (‖p‖ + ‖q‖) * ‖p - q‖ := by ring
  have hsplit :
      (-2 * a ^ 2 * ⟪p, v⟫_ℝ) - (-2 * b ^ 2 * ⟪q, w⟫_ℝ) =
        (-2 * a ^ 2 * ⟪p, v - w⟫_ℝ) +
          (-2 * a ^ 2 * ⟪p - q, w⟫_ℝ) +
          (-2 * (a ^ 2 - b ^ 2) * ⟪q, w⟫_ℝ) := by
    rw [inner_sub_right, inner_sub_left]
    ring
  have hAsq : a ^ 2 ≤ 1 := by nlinarith
  have hA : 2 * a ^ 2 * |⟪p, v - w⟫_ℝ| ≤ 2 * ‖p‖ * ‖v - w‖ := by
    calc
      _ ≤ 2 * a ^ 2 * (‖p‖ * ‖v - w‖) :=
        mul_le_mul_of_nonneg_left hinner_vw (by positivity)
      _ ≤ 2 * 1 * (‖p‖ * ‖v - w‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAsq (by norm_num))
          (by positivity)
      _ = _ := by ring
  have hB : 2 * a ^ 2 * |⟪p - q, w⟫_ℝ| ≤ 2 * ‖p - q‖ * ‖w‖ := by
    calc
      _ ≤ 2 * a ^ 2 * (‖p - q‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left hinner_pq (by positivity)
      _ ≤ 2 * 1 * (‖p - q‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAsq (by norm_num))
          (by positivity)
      _ = _ := by ring
  have hC : 2 * |a ^ 2 - b ^ 2| * |⟪q, w⟫_ℝ| ≤
      4 * (‖p‖ + ‖q‖) * ‖q‖ * ‖p - q‖ * ‖w‖ := by
    calc
      _ ≤ 2 * |a ^ 2 - b ^ 2| * (‖q‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left hinner_qw (by positivity)
      _ ≤ 2 * (2 * (‖p‖ + ‖q‖) * ‖p - q‖) * (‖q‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habsq (by norm_num))
          (by positivity)
      _ = _ := by ring
  rw [show graphDiffusionCoefficient p = a by rfl,
      show graphDiffusionCoefficient q = b by rfl, hsplit]
  calc
    _ ≤ |(-2 * a ^ 2 * ⟪p, v - w⟫_ℝ)| +
        |(-2 * a ^ 2 * ⟪p - q, w⟫_ℝ)| +
        |(-2 * (a ^ 2 - b ^ 2) * ⟪q, w⟫_ℝ)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = 2 * a ^ 2 * |⟪p, v - w⟫_ℝ| +
        2 * a ^ 2 * |⟪p - q, w⟫_ℝ| +
        2 * |a ^ 2 - b ^ 2| * |⟪q, w⟫_ℝ| := by
          simp only [abs_mul, abs_of_nonneg (sq_nonneg a)]
          norm_num
    _ ≤ _ := by nlinarith only [hA, hB, hC]

theorem graphDiffusionCoefficient_deriv_sub_bound_of_norm_le {p q : E} {R : ℝ}
    (hp : ‖p‖ ≤ R) (hq : ‖q‖ ≤ R) (v w : E) :
    |(-2 * graphDiffusionCoefficient p ^ 2 * ⟪p, v⟫_ℝ) -
      (-2 * graphDiffusionCoefficient q ^ 2 * ⟪q, w⟫_ℝ)| ≤
      2 * ‖p‖ * ‖v - w‖ + (2 + 8 * R ^ 2) * ‖p - q‖ * ‖w‖ := by
  have hR : 0 ≤ R := (norm_nonneg p).trans hp
  refine (graphDiffusionCoefficient_deriv_sub_bound p q v w).trans ?_
  have h : (‖p‖ + ‖q‖) * ‖q‖ ≤ 2 * R ^ 2 := by
    have hsum : ‖p‖ + ‖q‖ ≤ 2 * R := by linarith
    have hmul := mul_le_mul hsum hq (norm_nonneg q) (by positivity : 0 ≤ 2 * R)
    nlinarith only [hmul]
  have hcoef : 2 + 4 * (‖p‖ + ‖q‖) * ‖q‖ ≤ 2 + 8 * R ^ 2 := by nlinarith only [h]
  have hnonneg : 0 ≤ ‖p - q‖ * ‖w‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith only [mul_le_mul_of_nonneg_right hcoef hnonneg]

end DifferentialGeometry.Analysis.Parabolic


namespace DifferentialGeometry.Analysis.Parabolic

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivAt_graphDiffusionCoefficient_remainder
    {p : ℝ → E} {q : ℝ → F} {x : ℝ} {p' : E} {q' : F}
    (hp : HasDerivAt p p' x) (hq : HasDerivAt q q' x) :
    HasDerivAt (fun y => (graphDiffusionCoefficient (p y) - 1) • q y)
      ((graphDiffusionCoefficient (p x) - 1) • q' +
        (-2 * graphDiffusionCoefficient (p x) ^ 2 * ⟪p x, p'⟫_ℝ) • q x) x :=
  ((hasDerivAt_graphDiffusionCoefficient hp).sub_const 1).smul hq

theorem graphDiffusionCoefficient_derivative_bound (p p' : E) :
    |(-2 * graphDiffusionCoefficient p ^ 2 * ⟪p, p'⟫_ℝ)| ≤
      2 * ‖p‖ * ‖p'‖ := by
  have ha0 : 0 ≤ graphDiffusionCoefficient p := (graphDiffusionCoefficient_pos p).le
  have ha1 : graphDiffusionCoefficient p ≤ 1 := graphDiffusionCoefficient_le_one p
  have hasq : graphDiffusionCoefficient p ^ 2 ≤ 1 := by nlinarith
  calc
    |(-2 * graphDiffusionCoefficient p ^ 2 * ⟪p, p'⟫_ℝ)| =
        2 * graphDiffusionCoefficient p ^ 2 * |⟪p, p'⟫_ℝ| := by
      simp only [abs_mul, abs_pow, sq_abs]
      norm_num
    _ ≤ 2 * 1 * (‖p‖ * ‖p'‖) := by
      gcongr
      exact abs_real_inner_le_norm p p'
    _ = 2 * ‖p‖ * ‖p'‖ := by ring

theorem graphDiffusionCoefficient_remainder_derivative_bound (p p' : E) (q q' : F) :
    ‖(graphDiffusionCoefficient p - 1) • q' +
        (-2 * graphDiffusionCoefficient p ^ 2 * ⟪p, p'⟫_ℝ) • q‖ ≤
      ‖p‖ ^ 2 * ‖q'‖ + 2 * ‖p‖ * ‖p'‖ * ‖q‖ := by
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact add_le_add
    (mul_le_mul_of_nonneg_right (graphDiffusionCoefficient_sub_one_bound p) (norm_nonneg q'))
    (mul_le_mul_of_nonneg_right (graphDiffusionCoefficient_derivative_bound p p') (norm_nonneg q))

theorem norm_deriv_graphDiffusionCoefficient_remainder_le
    {p : ℝ → E} {q : ℝ → F} {x : ℝ}
    (hp : DifferentiableAt ℝ p x) (hq : DifferentiableAt ℝ q x) :
    ‖deriv (fun y => (graphDiffusionCoefficient (p y) - 1) • q y) x‖ ≤
      ‖p x‖ ^ 2 * ‖deriv q x‖ + 2 * ‖p x‖ * ‖deriv p x‖ * ‖q x‖ := by
  rw [(hasDerivAt_graphDiffusionCoefficient_remainder hp.hasDerivAt hq.hasDerivAt).deriv]
  exact graphDiffusionCoefficient_remainder_derivative_bound _ _ _ _

end DifferentialGeometry.Analysis.Parabolic


namespace DifferentialGeometry.Analysis.Parabolic

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem graphDiffusionCoefficient_derivative_smul_sub_bound (p q u v : E) (r s : F) :
    ‖(-2 * graphDiffusionCoefficient p ^ 2 * ⟪p, u⟫_ℝ) • r -
        (-2 * graphDiffusionCoefficient q ^ 2 * ⟪q, v⟫_ℝ) • s‖ ≤
      2 * ‖p‖ * ‖u‖ * ‖r - s‖ +
        (2 * ‖p‖ * ‖u - v‖ +
          (2 + 4 * (‖p‖ + ‖q‖) * ‖q‖) * ‖p - q‖ * ‖v‖) * ‖s‖ := by
  let bp := -2 * graphDiffusionCoefficient p ^ 2 * ⟪p, u⟫_ℝ
  let bq := -2 * graphDiffusionCoefficient q ^ 2 * ⟪q, v⟫_ℝ
  change ‖bp • r - bq • s‖ ≤ _
  have heq : bp • r - bq • s = bp • (r - s) + (bp - bq) • s := by
    simp only [smul_sub, sub_smul]
    abel
  rw [heq]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact add_le_add
    (mul_le_mul_of_nonneg_right (graphDiffusionCoefficient_derivative_bound p u)
      (norm_nonneg (r - s)))
    (mul_le_mul_of_nonneg_right (graphDiffusionCoefficient_deriv_sub_bound p q u v)
      (norm_nonneg s))

theorem graphDiffusionCoefficient_remainder_derivative_sub_bound
    {p q : E} {R : ℝ} (hp : ‖p‖ ≤ R) (hq : ‖q‖ ≤ R)
    (u v : E) (r s r' s' : F) :
    ‖((graphDiffusionCoefficient p - 1) • r' +
        (-2 * graphDiffusionCoefficient p ^ 2 * ⟪p, u⟫_ℝ) • r) -
      ((graphDiffusionCoefficient q - 1) • s' +
        (-2 * graphDiffusionCoefficient q ^ 2 * ⟪q, v⟫_ℝ) • s)‖ ≤
      R ^ 2 * ‖r' - s'‖ + (2 * R) * ‖p - q‖ * ‖s'‖ +
        2 * ‖p‖ * ‖u‖ * ‖r - s‖ +
        (2 * ‖p‖ * ‖u - v‖ +
          (2 + 4 * (‖p‖ + ‖q‖) * ‖q‖) * ‖p - q‖ * ‖v‖) * ‖s‖ := by
  rw [show ((graphDiffusionCoefficient p - 1) • r' +
      (-2 * graphDiffusionCoefficient p ^ 2 * ⟪p, u⟫_ℝ) • r) -
      ((graphDiffusionCoefficient q - 1) • s' +
        (-2 * graphDiffusionCoefficient q ^ 2 * ⟪q, v⟫_ℝ) • s) =
      ((graphDiffusionCoefficient p - 1) • r' -
        (graphDiffusionCoefficient q - 1) • s') +
      ((-2 * graphDiffusionCoefficient p ^ 2 * ⟪p, u⟫_ℝ) • r -
        (-2 * graphDiffusionCoefficient q ^ 2 * ⟪q, v⟫_ℝ) • s) by abel]
  have h := add_le_add
    (graphDiffusionCoefficient_remainder_small_slope_bound hp hq r' s')
    (graphDiffusionCoefficient_derivative_smul_sub_bound p q u v r s)
  exact (norm_add_le _ _).trans (by simpa only [add_assoc] using h)

theorem norm_deriv_graphDiffusionCoefficient_remainder_sub_le
    {p q : ℝ → E} {r s : ℝ → F} {x R : ℝ}
    (hp : DifferentiableAt ℝ p x) (hq : DifferentiableAt ℝ q x)
    (hr : DifferentiableAt ℝ r x) (hs : DifferentiableAt ℝ s x)
    (hpR : ‖p x‖ ≤ R) (hqR : ‖q x‖ ≤ R) :
    ‖deriv (fun y => (graphDiffusionCoefficient (p y) - 1) • r y) x -
        deriv (fun y => (graphDiffusionCoefficient (q y) - 1) • s y) x‖ ≤
      R ^ 2 * ‖deriv r x - deriv s x‖ + (2 * R) * ‖p x - q x‖ * ‖deriv s x‖ +
        2 * ‖p x‖ * ‖deriv p x‖ * ‖r x - s x‖ +
        (2 * ‖p x‖ * ‖deriv p x - deriv q x‖ +
          (2 + 4 * (‖p x‖ + ‖q x‖) * ‖q x‖) * ‖p x - q x‖ * ‖deriv q x‖) * ‖s x‖ := by
  rw [(hasDerivAt_graphDiffusionCoefficient_remainder hp.hasDerivAt hr.hasDerivAt).deriv,
    (hasDerivAt_graphDiffusionCoefficient_remainder hq.hasDerivAt hs.hasDerivAt).deriv]
  exact graphDiffusionCoefficient_remainder_derivative_sub_bound hpR hqR _ _ _ _ _ _

end DifferentialGeometry.Analysis.Parabolic


namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem deriv_graphDiffusionCoefficient_sub_bound {p q : ℝ → E} {R x : ℝ}
    (hp : DifferentiableAt ℝ p x) (hq : DifferentiableAt ℝ q x)
    (hpR : ‖p x‖ ≤ R) (hqR : ‖q x‖ ≤ R) :
    |deriv (fun y => graphDiffusionCoefficient (p y) - graphDiffusionCoefficient (q y)) x| ≤
      (2 * R) * ‖deriv p x - deriv q x‖ +
        (2 + 8 * R ^ 2) * ‖p x - q x‖ * ‖deriv q x‖ := by
  have hd := ((hasDerivAt_graphDiffusionCoefficient hp.hasDerivAt).sub
    (hasDerivAt_graphDiffusionCoefficient hq.hasDerivAt)).deriv
  change deriv (fun y => graphDiffusionCoefficient (p y) - graphDiffusionCoefficient (q y)) x = _ at hd
  rw [hd]
  refine (graphDiffusionCoefficient_deriv_sub_bound_of_norm_le hpR hqR _ _).trans ?_
  exact add_le_add (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpR (by norm_num)) (norm_nonneg _)) le_rfl

end DifferentialGeometry.Analysis.Parabolic

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem graphDiffusionCoefficient_remainder_second_deriv_bound
    {f : ℝ → E} {x : ℝ}
    (hdf : DifferentiableAt ℝ (deriv f) x)
    (hddf : DifferentiableAt ℝ (deriv (deriv f)) x) :
    ‖deriv (fun y => (graphDiffusionCoefficient (deriv f y) - 1) •
      deriv (deriv f) y) x‖ ≤
      2 * ‖deriv f x‖ * ‖deriv (deriv f) x‖ ^ 2 +
        ‖deriv f x‖ ^ 2 * ‖deriv (deriv (deriv f)) x‖ := by
  simpa only [pow_two, mul_assoc, add_comm] using
    norm_deriv_graphDiffusionCoefficient_remainder_le hdf hddf

end DifferentialGeometry.Analysis.Parabolic
