import DifferentialGeometry.Analysis.Calculus.Cutoff.BoundaryBlockProfile

/-!
# The augmented boundary reference model and its derivative and error bounds (lane BCG-8b, G12)

Blueprint 207B, BCG03 (`B:8960–9010`, (BCG03.a)–(BCG03.b)); external draft 61 §2.5 and
disposition D61-5 (BM). For a reference `a` with reference coordinate `η_a` (values in a normed
space `E`, e.g. `ℝ²` for a circle, `ℝ` for an edge or slim reference) and a boundary component `b`
in its whole support list, the augmented model block is

  `h_{a,b}(z) = η_b(p_a) + R_a A_{a,b}(z − η_a(p_a))`,   `Φ^∂_{a,b}(z) = R_a⁻¹ 𝓑(h_{a,b}(z))`,

`𝓑(t) = (tχ_∂(t), χ_∂(t))` (`boundaryBlock`), `A_{a,b}` the ONE row of (BA) (`‖A‖ ≤ 1`). With an
early constant `P_*` bounding `‖𝓑'‖∞` and `‖𝓑''‖∞` (`exists_boundaryBlock_derivative_bounds`):

* `fderiv_boundaryModel_BCG8b`: `DΦ(z) = 𝓑'(h(z)) ∘ A` — the prefactor `R_a⁻¹` cancels;
* `norm_fderiv_boundaryModel_le_BCG8b`: `‖DΦ‖ ≤ P_*`;
* `fderiv_fderiv_boundaryModel_BCG8b`, `norm_fderiv_fderiv_boundaryModel_le_BCG8b`:
  `‖D²Φ‖ ≤ R_a P_*` (one factor `R_a` survives the second differentiation);
* `norm_smul_boundaryBlock_sub_model_le_BCG8b`, `boundaryModel_value_error_BCG8b`: the normalized
  value error `‖R_a⁻¹𝓑(η_b(p)) − Φ(η_a(p))‖ ≤ P_*·|U_b(p) − A(η_a(p) − η_a(p_a))| ≤ P_*ϑ`;
* consumer `exists_boundaryModel_derivative_bounds_BCG8b`: (BCG03.b) with BCG.0's `P_*`.
* `norm_fderiv_boundaryBlock_sub_le_BCG8b`, `boundaryModel_differential_error_BCG8b`: the normalized
  differential error `‖𝓑'(η_b(p))(DU_b(u)) − DΦ(η_a(p))(Dη_a(u))‖ ≤ 3P_*ϑ|u|` from
  `|DU_b(u) − A Dη_a(u)| ≤ θ'|u|`, `θ' ≤ ϑ`, `‖Dη_a(u)‖ ≤ 2|u|`, `R_a ≤ 1` (here
  `D(R_a⁻¹𝓑 ∘ η_b) = 𝓑'(η_b)·DU_b`, `U_b = (η_b − η_b(p_a))/R_a`).

The possibly large constant `R_a⁻¹` (the marker value of the model) never enters these derivative
bounds, and no absolute bound on `Φ` is asserted (D61-5).
-/

set_option autoImplicit false

noncomputable section

open Set Function

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine height of the augmented model, `h(z) = c + R·A(z − z₀)` (`c = η_b(p_a)`, `R = R_a`,
`z₀ = η_a(p_a)`). -/
def boundaryModelHeight_BCG8b (c R : ℝ) (A : E →L[ℝ] ℝ) (z₀ z : E) : ℝ :=
  c + R * A (z - z₀)

/-- **The augmented boundary model block** (BM): `Φ(z) = R⁻¹ 𝓑(h(z))`. -/
def boundaryModel_BCG8b (c R : ℝ) (A : E →L[ℝ] ℝ) (z₀ z : E) : ℝ × ℝ :=
  R⁻¹ • boundaryBlock (boundaryModelHeight_BCG8b c R A z₀ z)

/-- The affine height has derivative `R • A`. -/
theorem hasFDerivAt_boundaryModelHeight_BCG8b (c R : ℝ) (A : E →L[ℝ] ℝ) (z₀ z : E) :
    HasFDerivAt (boundaryModelHeight_BCG8b c R A z₀) (R • A) z := by
  have he : boundaryModelHeight_BCG8b c R A z₀ = fun z => (R • A) z + (c - (R • A) z₀) := by
    funext z
    simp only [boundaryModelHeight_BCG8b, map_sub, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul]
    ring
  rw [he]
  exact (R • A).hasFDerivAt.add_const _

theorem differentiable_boundaryBlock_BCG8b : Differentiable ℝ boundaryBlock :=
  contDiff_boundaryBlock.differentiable (by simp)

theorem differentiable_fderiv_boundaryBlock_BCG8b : Differentiable ℝ (fderiv ℝ boundaryBlock) :=
  (contDiff_boundaryBlock.fderiv_right (m := 1) (by simp)).differentiable (by simp)

/-- **`DΦ(z) = 𝓑'(h(z)) ∘ A`**: the prefactor `R⁻¹` cancels against the slope `R` of `h`. -/
theorem hasFDerivAt_boundaryModel_BCG8b (c : ℝ) {R : ℝ} (hR : R ≠ 0) (A : E →L[ℝ] ℝ) (z₀ z : E) :
    HasFDerivAt (boundaryModel_BCG8b c R A z₀)
      ((fderiv ℝ boundaryBlock (boundaryModelHeight_BCG8b c R A z₀ z)).comp A) z := by
  have hB : HasFDerivAt boundaryBlock
      (fderiv ℝ boundaryBlock (boundaryModelHeight_BCG8b c R A z₀ z))
      (boundaryModelHeight_BCG8b c R A z₀ z) :=
    (differentiable_boundaryBlock_BCG8b _).hasFDerivAt
  have h := (hB.comp z (hasFDerivAt_boundaryModelHeight_BCG8b c R A z₀ z)).const_smul R⁻¹
  have hEq : (fderiv ℝ boundaryBlock (boundaryModelHeight_BCG8b c R A z₀ z)).comp A =
      R⁻¹ • (fderiv ℝ boundaryBlock (boundaryModelHeight_BCG8b c R A z₀ z)).comp (R • A) := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp [smul_smul, inv_mul_cancel₀ hR]
  rw [hEq]
  exact h

theorem fderiv_boundaryModel_BCG8b (c : ℝ) {R : ℝ} (hR : R ≠ 0) (A : E →L[ℝ] ℝ) (z₀ z : E) :
    fderiv ℝ (boundaryModel_BCG8b c R A z₀) z =
      (fderiv ℝ boundaryBlock (boundaryModelHeight_BCG8b c R A z₀ z)).comp A :=
  (hasFDerivAt_boundaryModel_BCG8b c hR A z₀ z).fderiv

/-- `P_*` is nonnegative. -/
theorem nonneg_of_boundaryBlock_bound_BCG8b {P : ℝ}
    (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ P) : 0 ≤ P :=
  (norm_nonneg _).trans (hP 0)

/-- **`‖DΦ‖ ≤ P_*`** (BCG03.b, first half) for a row with `‖A‖ ≤ 1`. -/
theorem norm_fderiv_boundaryModel_le_BCG8b {P : ℝ} (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ P)
    (c : ℝ) {R : ℝ} (hR : R ≠ 0) {A : E →L[ℝ] ℝ} (hA : ‖A‖ ≤ 1) (z₀ z : E) :
    ‖fderiv ℝ (boundaryModel_BCG8b c R A z₀) z‖ ≤ P := by
  rw [fderiv_boundaryModel_BCG8b c hR A z₀ z]
  calc ‖(fderiv ℝ boundaryBlock (boundaryModelHeight_BCG8b c R A z₀ z)).comp A‖
      ≤ ‖fderiv ℝ boundaryBlock (boundaryModelHeight_BCG8b c R A z₀ z)‖ * ‖A‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ P * 1 := mul_le_mul (hP _) hA (norm_nonneg _) (nonneg_of_boundaryBlock_bound_BCG8b hP)
    _ = P := mul_one P

/-- Precomposition with the row: `L ↦ L ∘ A`. -/
theorem norm_precompRow_le_BCG8b (A : E →L[ℝ] ℝ) :
    ‖(ContinuousLinearMap.compL ℝ E ℝ (ℝ × ℝ)).flip A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun L => ?_
  calc ‖(ContinuousLinearMap.compL ℝ E ℝ (ℝ × ℝ)).flip A L‖ = ‖L.comp A‖ := rfl
    _ ≤ ‖L‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖A‖ * ‖L‖ := mul_comm _ _

/-- **`D²Φ(z) = (L ↦ L ∘ A) ∘ 𝓑''(h(z)) ∘ (R • A)`.** -/
theorem fderiv_fderiv_boundaryModel_BCG8b (c : ℝ) {R : ℝ} (hR : R ≠ 0) (A : E →L[ℝ] ℝ)
    (z₀ z : E) :
    fderiv ℝ (fderiv ℝ (boundaryModel_BCG8b c R A z₀)) z =
      ((ContinuousLinearMap.compL ℝ E ℝ (ℝ × ℝ)).flip A).comp
        ((fderiv ℝ (fderiv ℝ boundaryBlock) (boundaryModelHeight_BCG8b c R A z₀ z)).comp
          (R • A)) := by
  have he : fderiv ℝ (boundaryModel_BCG8b c R A z₀) = fun z =>
      (ContinuousLinearMap.compL ℝ E ℝ (ℝ × ℝ)).flip A
        (fderiv ℝ boundaryBlock (boundaryModelHeight_BCG8b c R A z₀ z)) := by
    funext z
    rw [fderiv_boundaryModel_BCG8b c hR A z₀ z]
    rfl
  rw [he]
  have hB2 : HasFDerivAt (fderiv ℝ boundaryBlock)
      (fderiv ℝ (fderiv ℝ boundaryBlock) (boundaryModelHeight_BCG8b c R A z₀ z))
      (boundaryModelHeight_BCG8b c R A z₀ z) :=
    (differentiable_fderiv_boundaryBlock_BCG8b _).hasFDerivAt
  exact (((ContinuousLinearMap.compL ℝ E ℝ (ℝ × ℝ)).flip A).hasFDerivAt.comp z
    (hB2.comp z (hasFDerivAt_boundaryModelHeight_BCG8b c R A z₀ z))).fderiv

/-- **`‖D²Φ‖ ≤ R P_*`** (BCG03.b, second half) for `R > 0` and a row with `‖A‖ ≤ 1`. -/
theorem norm_fderiv_fderiv_boundaryModel_le_BCG8b {P : ℝ}
    (hP2 : ∀ t, ‖fderiv ℝ (fderiv ℝ boundaryBlock) t‖ ≤ P) (c : ℝ) {R : ℝ} (hR : 0 < R)
    {A : E →L[ℝ] ℝ} (hA : ‖A‖ ≤ 1) (z₀ z : E) :
    ‖fderiv ℝ (fderiv ℝ (boundaryModel_BCG8b c R A z₀)) z‖ ≤ R * P := by
  rw [fderiv_fderiv_boundaryModel_BCG8b c hR.ne' A z₀ z]
  have hP0 : 0 ≤ P := (norm_nonneg _).trans (hP2 0)
  have hRA : ‖R • A‖ ≤ R := by
    rw [norm_smul, Real.norm_of_nonneg hR.le]
    calc R * ‖A‖ ≤ R * 1 := mul_le_mul_of_nonneg_left hA hR.le
      _ = R := mul_one R
  calc ‖((ContinuousLinearMap.compL ℝ E ℝ (ℝ × ℝ)).flip A).comp
        ((fderiv ℝ (fderiv ℝ boundaryBlock) (boundaryModelHeight_BCG8b c R A z₀ z)).comp
          (R • A))‖
      ≤ ‖(ContinuousLinearMap.compL ℝ E ℝ (ℝ × ℝ)).flip A‖ *
        ‖(fderiv ℝ (fderiv ℝ boundaryBlock) (boundaryModelHeight_BCG8b c R A z₀ z)).comp
          (R • A)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (P * R) := by
        refine mul_le_mul ((norm_precompRow_le_BCG8b A).trans hA) ?_ (norm_nonneg _) zero_le_one
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (hP2 _) hRA (norm_nonneg _) hP0)
    _ = R * P := by ring

/-- **The normalized value error** of the model:
`‖R⁻¹𝓑(t) − Φ(z)‖ ≤ P_*·|(t − c)/R − A(z − z₀)|`. -/
theorem norm_smul_boundaryBlock_sub_model_le_BCG8b {P : ℝ}
    (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ P) (c : ℝ) {R : ℝ} (hR : 0 < R) (A : E →L[ℝ] ℝ)
    (z₀ z : E) (t : ℝ) :
    ‖R⁻¹ • boundaryBlock t - boundaryModel_BCG8b c R A z₀ z‖ ≤
      P * |(t - c) / R - A (z - z₀)| := by
  rw [boundaryModel_BCG8b, ← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
  have h := norm_boundaryBlock_sub_le hP t (boundaryModelHeight_BCG8b c R A z₀ z)
  have he : t - boundaryModelHeight_BCG8b c R A z₀ z = R * ((t - c) / R - A (z - z₀)) := by
    rw [boundaryModelHeight_BCG8b]
    field_simp
    ring
  rw [he, abs_mul, abs_of_pos hR] at h
  calc R⁻¹ * ‖boundaryBlock t - boundaryBlock (boundaryModelHeight_BCG8b c R A z₀ z)‖
      ≤ R⁻¹ * (P * (R * |(t - c) / R - A (z - z₀)|)) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hR.le)
    _ = P * |(t - c) / R - A (z - z₀)| := by field_simp

/-- **Normalized value error `≤ P_*ϑ`** from the value clause of (BA). -/
theorem boundaryModel_value_error_BCG8b {P : ℝ} (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ P)
    (c : ℝ) {R : ℝ} (hR : 0 < R) (A : E →L[ℝ] ℝ) (z₀ z : E) {t ϑ : ℝ}
    (hval : |(t - c) / R - A (z - z₀)| < ϑ) :
    ‖R⁻¹ • boundaryBlock t - boundaryModel_BCG8b c R A z₀ z‖ ≤ P * ϑ :=
  (norm_smul_boundaryBlock_sub_model_le_BCG8b hP c hR A z₀ z t).trans
    (mul_le_mul_of_nonneg_left hval.le (nonneg_of_boundaryBlock_bound_BCG8b hP))

/-- `𝓑'` is `P_*`-Lipschitz when `‖𝓑''‖ ≤ P_*`. -/
theorem norm_fderiv_boundaryBlock_sub_le_BCG8b {P : ℝ}
    (hP2 : ∀ t, ‖fderiv ℝ (fderiv ℝ boundaryBlock) t‖ ≤ P) (s t : ℝ) :
    ‖fderiv ℝ boundaryBlock s - fderiv ℝ boundaryBlock t‖ ≤ P * |s - t| := by
  have h := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => differentiable_fderiv_boundaryBlock_BCG8b x) (fun x _ => hP2 x) (mem_univ t)
    (mem_univ s)
  rwa [Real.norm_eq_abs] at h

/-- **Normalized differential error `≤ 3P_*ϑ|u|`.** For the actual covector value `f = DU_b(u)`
at a point with `|(t − c)/R − A(z − z₀)| < ϑ` (`t = η_b(p)`, `z = η_a(p)`), the reference value
`v = Dη_a(u)` with `‖v‖ ≤ 2N` (`N = |u|_{R⁻²g}`) and the differential clause
`|f − A v| ≤ θ'N`, `θ' ≤ ϑ`, `0 < R ≤ 1`: `‖𝓑'(t) f − DΦ(z) v‖ ≤ 3P_*ϑN`. -/
theorem boundaryModel_differential_error_BCG8b {P : ℝ}
    (hP : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ P)
    (hP2 : ∀ t, ‖fderiv ℝ (fderiv ℝ boundaryBlock) t‖ ≤ P) (c : ℝ) {R : ℝ} (hR : 0 < R)
    (hR1 : R ≤ 1) {A : E →L[ℝ] ℝ} (hA : ‖A‖ ≤ 1) (z₀ : E) {z v : E} {t f N ϑ θ' : ℝ}
    (hval : |(t - c) / R - A (z - z₀)| < ϑ) (hdiff : |f - A v| ≤ θ' * N) (hθ' : θ' ≤ ϑ)
    (hv : ‖v‖ ≤ 2 * N) :
    ‖fderiv ℝ boundaryBlock t f - fderiv ℝ (boundaryModel_BCG8b c R A z₀) z v‖ ≤
      3 * P * ϑ * N := by
  have hP0 := nonneg_of_boundaryBlock_bound_BCG8b hP
  have hN : 0 ≤ N := by linarith only [norm_nonneg v, hv]
  have hϑ : 0 ≤ ϑ := (abs_nonneg _).trans hval.le
  set s := boundaryModelHeight_BCG8b c R A z₀ z with hs
  rw [fderiv_boundaryModel_BCG8b c hR.ne' A z₀ z, ContinuousLinearMap.comp_apply, ← hs]
  have hsplit : fderiv ℝ boundaryBlock t f - fderiv ℝ boundaryBlock s (A v) =
      fderiv ℝ boundaryBlock t (f - A v) + (fderiv ℝ boundaryBlock t - fderiv ℝ boundaryBlock s)
        (A v) := by
    simp only [map_sub, FunLike.coe_sub, Pi.sub_apply]
    abel
  have hts : |t - s| ≤ R * ϑ := by
    have he : t - s = R * ((t - c) / R - A (z - z₀)) := by
      rw [hs, boundaryModelHeight_BCG8b]
      field_simp
      ring
    rw [he, abs_mul, abs_of_pos hR]
    exact mul_le_mul_of_nonneg_left hval.le hR.le
  have hAv : |A v| ≤ 2 * N := by
    have h1 : ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
    rw [Real.norm_eq_abs] at h1
    nlinarith only [h1, hA, hv, norm_nonneg A, norm_nonneg v]
  have h1 : ‖fderiv ℝ boundaryBlock t (f - A v)‖ ≤ P * (θ' * N) := by
    refine ((fderiv ℝ boundaryBlock t).le_opNorm _).trans ?_
    rw [Real.norm_eq_abs]
    exact mul_le_mul (hP t) hdiff (abs_nonneg _) hP0
  have h2 : ‖(fderiv ℝ boundaryBlock t - fderiv ℝ boundaryBlock s) (A v)‖ ≤
      P * (R * ϑ) * (2 * N) := by
    refine ((fderiv ℝ boundaryBlock t - fderiv ℝ boundaryBlock s).le_opNorm _).trans ?_
    rw [Real.norm_eq_abs]
    refine mul_le_mul ?_ hAv (abs_nonneg _) (by positivity)
    exact (norm_fderiv_boundaryBlock_sub_le_BCG8b hP2 t s).trans
      (mul_le_mul_of_nonneg_left hts hP0)
  rw [hsplit]
  calc ‖fderiv ℝ boundaryBlock t (f - A v) +
        (fderiv ℝ boundaryBlock t - fderiv ℝ boundaryBlock s) (A v)‖
      ≤ P * (θ' * N) + P * (R * ϑ) * (2 * N) := (norm_add_le _ _).trans (add_le_add h1 h2)
    _ ≤ 3 * P * ϑ * N := by
        have h3 : P * (θ' * N) ≤ P * (ϑ * N) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hθ' hN) hP0
        have h4 : P * (R * ϑ) * (2 * N) ≤ P * (1 * ϑ) * (2 * N) := by
          have : R * ϑ ≤ 1 * ϑ := mul_le_mul_of_nonneg_right hR1 hϑ
          have h5 : 0 ≤ 2 * N := by linarith only [hN]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hP0) h5
        nlinarith only [h3, h4]

/-- **Consumer: (BCG03.b) with the early constant of BCG.0.** There is one `P_* ≥ 1` such that for
every reference scale `0 < R < 1`, every row with `‖A‖ ≤ 1` and all `c, z₀, z`:
`‖DΦ(z)‖ ≤ P_*` and `‖D²Φ(z)‖ ≤ R P_* < P_*`. -/
theorem exists_boundaryModel_derivative_bounds_BCG8b :
    ∃ P : ℝ, 1 ≤ P ∧ ∀ (c R : ℝ), 0 < R → R < 1 → ∀ (A : E →L[ℝ] ℝ), ‖A‖ ≤ 1 → ∀ z₀ z : E,
      ‖fderiv ℝ (boundaryModel_BCG8b c R A z₀) z‖ ≤ P ∧
      ‖fderiv ℝ (fderiv ℝ (boundaryModel_BCG8b c R A z₀)) z‖ ≤ R * P ∧ R * P < P := by
  obtain ⟨P, hP1, hP, hP2⟩ := exists_boundaryBlock_derivative_bounds
  refine ⟨P, hP1, fun c R hR hR1 A hA z₀ z => ⟨norm_fderiv_boundaryModel_le_BCG8b hP c hR.ne' hA
    z₀ z, norm_fderiv_fderiv_boundaryModel_le_BCG8b hP2 c hR hA z₀ z, ?_⟩⟩
  have hP0 : 0 < P := lt_of_lt_of_le one_pos hP1
  calc R * P < 1 * P := mul_lt_mul_of_pos_right hR1 hP0
    _ = P := one_mul P

end DifferentialGeometry.Analysis
