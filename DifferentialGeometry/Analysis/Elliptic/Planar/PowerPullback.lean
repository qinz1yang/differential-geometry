import DifferentialGeometry.Analysis.Elliptic.Planar.CoordinateChange
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis

/-- The real matrix of multiplication by a complex number in the basis `1, I`. -/
def planarComplexMulMatrix (q : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![q.re, -q.im; q.im, q.re]

/-- The trace-free combination appearing in the Hessian correction for a
holomorphic change of planar coordinates. No symmetry is required. -/
def planarMatrixSpin (K : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  (K 0 0 - K 1 1 : ℝ) + (K 0 1 + K 1 0 : ℝ) * Complex.I

private theorem complex_bilinear_coordinates
    (T : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (z t : ℂ) :
    T z t = z.re * t.re * T 1 1 + z.re * t.im * T 1 Complex.I +
      z.im * t.re * T Complex.I 1 + z.im * t.im * T Complex.I Complex.I := by
  have hdecomp (v : ℂ) : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    T z t = T (z.re • (1 : ℂ) + z.im • Complex.I)
        (t.re • (1 : ℂ) + t.im • Complex.I) := by rw [← hdecomp z, ← hdecomp t]
    _ = _ := by
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      ring

/-- Conjugation by complex multiplication gives the exact scalar principal
factor. Neither the coefficient matrix nor the bilinear form must be symmetric. -/
theorem planar_principal_contraction_complex_conjugate
    (A : Matrix (Fin 2) (Fin 2) ℝ) {q : ℂ} (hq : q ≠ 0)
    (T : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :
    let K := planarComplexMulMatrix q⁻¹ * A * planarComplexMulMatrix q
    (∑ i : Fin 2, ∑ j : Fin 2, K i j *
      T (q * ((![1, Complex.I] : Fin 2 → ℂ) i))
        (q * ((![1, Complex.I] : Fin 2 → ℂ) j))) =
      ‖q‖ ^ 2 * (∑ i : Fin 2, ∑ j : Fin 2, A i j *
        T ((![1, Complex.I] : Fin 2 → ℂ) i)
          ((![1, Complex.I] : Fin 2 → ℂ) j)) := by
  intro K
  rw [← Complex.normSq_eq_norm_sq]
  simp only [K, planarComplexMulMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [complex_bilinear_coordinates T (q * 1) (q * 1),
    complex_bilinear_coordinates T (q * 1) (q * Complex.I),
    complex_bilinear_coordinates T (q * Complex.I) (q * 1),
    complex_bilinear_coordinates T (q * Complex.I) (q * Complex.I)]
  simp only [Complex.inv_re, Complex.inv_im,
    Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_sub]
  field_simp [(Complex.normSq_pos.mpr hq).ne']
  simp only [Complex.normSq_apply]
  ring

private theorem planar_second_derivative_contraction
    (K : Matrix (Fin 2) (Fin 2) ℝ) (D : ℂ →L[ℝ] ℝ) (delta : ℂ) :
    (∑ i : Fin 2, ∑ j : Fin 2, K i j *
      D (delta * ((![1, Complex.I] : Fin 2 → ℂ) i) *
        ((![1, Complex.I] : Fin 2 → ℂ) j))) = D (delta * planarMatrixSpin K) := by
  have hsum : (∑ i : Fin 2, ∑ j : Fin 2, K i j •
      (delta * ((![1, Complex.I] : Fin 2 → ℂ) i) *
        ((![1, Complex.I] : Fin 2 → ℂ) j))) = delta * planarMatrixSpin K := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, planarMatrixSpin, Complex.real_smul]
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im] <;> ring
  rw [← hsum]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- The complete finite-dimensional power-pullback identity, including the
coordinate-Hessian drift and the original lower terms. The coefficient `q`
and coordinate second derivative `delta` are kept literal. -/
theorem planar_full_contraction_complex_conjugate
    (A : Matrix (Fin 2) (Fin 2) ℝ) {q : ℂ} (hq : q ≠ 0)
    (delta beta : ℂ) (c value : ℝ)
    (T : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (D : ℂ →L[ℝ] ℝ) :
    let K := planarComplexMulMatrix q⁻¹ * A * planarComplexMulMatrix q
    let b := star q * beta - q⁻¹ * delta * planarMatrixSpin K
    (∑ i : Fin 2, ∑ j : Fin 2, K i j *
      (T (q * ((![1, Complex.I] : Fin 2 → ℂ) i))
          (q * ((![1, Complex.I] : Fin 2 → ℂ) j)) +
        D (delta * ((![1, Complex.I] : Fin 2 → ℂ) i) *
          ((![1, Complex.I] : Fin 2 → ℂ) j)))) + D (q * b) +
      (‖q‖ ^ 2 * c) * value =
    ‖q‖ ^ 2 * ((∑ i : Fin 2, ∑ j : Fin 2, A i j *
      T ((![1, Complex.I] : Fin 2 → ℂ) i)
        ((![1, Complex.I] : Fin 2 → ℂ) j)) + D beta + c * value) := by
  intro K b
  have hb : q * b = (‖q‖ ^ 2 : ℝ) • beta - delta * planarMatrixSpin K := by
    change q * (star q * beta - q⁻¹ * delta * planarMatrixSpin K) = _
    calc
      _ = (q * star q) * beta - (q * q⁻¹) * (delta * planarMatrixSpin K) := by ring
      _ = _ := by
        rw [Complex.star_def, Complex.mul_conj', mul_inv_cancel₀ hq, one_mul]
        simp only [Complex.real_smul, Complex.ofReal_pow]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [planar_principal_contraction_complex_conjugate A hq T,
    planar_second_derivative_contraction K D delta, hb, map_sub, map_smul]
  simp only [smul_eq_mul]
  ring

/-- The actual scalar operator chain rule receives the conjugated coefficient
and explicit lower terms. The hypotheses identify the genuine first and second
coordinate derivatives at this point; no equation for the solution is assumed. -/
theorem planarScalarOperator_comp_complex_conjugate
    (A : Matrix (Fin 2) (Fin 2) ℝ) {q : ℂ} (hq : q ≠ 0)
    (delta beta : ℂ) (c : ℝ) {f : ℂ → ℝ} {P : ℂ → ℂ} {w : ℂ}
    (hf : ContDiffAt ℝ 2 f (P w)) (hP : ContDiffAt ℝ 2 P w)
    (hfirst : ∀ v : ℂ, fderiv ℝ P w v = q * v)
    (hsecond : ∀ v t : ℂ, fderiv ℝ (fderiv ℝ P) w v t = delta * v * t) :
    let K := planarComplexMulMatrix q⁻¹ * A * planarComplexMulMatrix q
    let b := star q * beta - q⁻¹ * delta * planarMatrixSpin K
    planarScalarOperator (fun _ => K) (fun _ => ![b.re, b.im])
      (fun _ => ‖q‖ ^ 2 * c) (fun z => f (P z)) w =
    ‖q‖ ^ 2 * planarScalarOperator (fun _ => A)
      (fun _ => ![beta.re, beta.im]) (fun _ => c) f (P w) := by
  intro K b
  have hdecomp (v : ℂ) : v.re • (1 : ℂ) + v.im • Complex.I = v := by
    apply Complex.ext <;> simp
  have hD (D : ℂ →L[ℝ] ℝ) (v : ℂ) :
      (∑ i : Fin 2, (![v.re, v.im] : Fin 2 → ℝ) i *
        D ((![1, Complex.I] : Fin 2 → ℂ) i)) = D v := by
    calc
      _ = v.re * D 1 + v.im * D Complex.I := by
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
      _ = D (v.re • (1 : ℂ) + v.im • Complex.I) := by
        simp only [map_add, map_smul, smul_eq_mul]
      _ = D v := congrArg D (hdecomp v)
  rw [planarScalarOperator_comp _ _ _ hf hP]
  simp only [planarCoordinateDrift, hfirst, hsecond]
  have hvec : (∑ i : Fin 2, (![b.re, b.im] : Fin 2 → ℝ) i •
      (q * ((![1, Complex.I] : Fin 2 → ℂ) i))) = q * b := by
    calc
      _ = q * (b.re • (1 : ℂ) + b.im • Complex.I) := by
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, Complex.real_smul]
        ring
      _ = q * b := by rw [hdecomp b]
  rw [hvec]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  have hid := planar_full_contraction_complex_conjugate A hq delta beta c
    (f (P w)) (fderiv ℝ (fderiv ℝ f) (P w)) (fderiv ℝ f (P w))
  dsimp only at hid
  simp only [mul_add, Finset.sum_add_distrib] at hid
  rw [planarScalarOperator, hD]
  simpa only [K, b, mul_add, add_assoc] using hid

private theorem normalized_power_hasFDerivAt (m : ℕ) (center z : ℂ) :
    HasFDerivAt (fun v : ℂ => center + v ^ (m + 1) / ((m + 1 : ℕ) : ℂ))
      (ContinuousLinearMap.mul ℝ ℂ (z ^ m)) z := by
  have hm : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hd : HasDerivAt
      (fun v : ℂ => center + v ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) (z ^ m) z := by
    convert (hasDerivAt_const z center).add
      ((hasDerivAt_pow (m + 1) z).div_const ((m + 1 : ℕ) : ℂ)) using 1
    simp only [Nat.add_sub_cancel, zero_add, mul_div_cancel_left₀ _ hm]
  convert hd.hasFDerivAt.restrictScalars ℝ using 1
  ext v
  change z ^ m * v = v * z ^ m
  exact mul_comm _ _

/-- Specialization to the literal normalized branch power. The original
solution and all three original coefficients are retained; the equality includes
the singular drift factor `m / w`, rather than discarding it. -/
theorem planarScalarOperator_normalized_power_pullback
    {m : ℕ} (hm : 1 ≤ m) (center : ℂ) {w : ℂ} (hw : w ≠ 0)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (beta : ℂ) (c : ℝ) {f : ℂ → ℝ}
    (hf : ContDiffAt ℝ 2 f (center + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ))) :
    let P : ℂ → ℂ := fun v => center + v ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
    let K := planarComplexMulMatrix (w ^ m)⁻¹ * A * planarComplexMulMatrix (w ^ m)
    let b := star (w ^ m) * beta - ((m : ℂ) / w) * planarMatrixSpin K
    planarScalarOperator (fun _ => K) (fun _ => ![b.re, b.im])
      (fun _ => ‖w ^ m‖ ^ 2 * c) (fun z => f (P z)) w =
    ‖w ^ m‖ ^ 2 * planarScalarOperator (fun _ => A)
      (fun _ => ![beta.re, beta.im]) (fun _ => c) f (P w) := by
  intro P K b
  have hP : ContDiffAt ℝ 2 P w :=
    contDiffAt_const.add ((contDiffAt_id.pow (m + 1)).div_const ((m + 1 : ℕ) : ℂ))
  have hfirst (v : ℂ) : fderiv ℝ P w v = w ^ m * v := by
    rw [(normalized_power_hasFDerivAt m center w).fderiv]
    rfl
  have hsecond (v t : ℂ) :
      fderiv ℝ (fderiv ℝ P) w v t = ((m : ℂ) * w ^ (m - 1)) * v * t := by
    have hfun : fderiv ℝ P = fun z => ContinuousLinearMap.mul ℝ ℂ (z ^ m) :=
      funext fun z => (normalized_power_hasFDerivAt m center z).fderiv
    rw [hfun]
    have hp := (hasDerivAt_pow m w).hasFDerivAt.restrictScalars ℝ
    have hd := ((ContinuousLinearMap.mul ℝ ℂ).hasFDerivAt.comp w hp).fderiv
    change fderiv ℝ ((ContinuousLinearMap.mul ℝ ℂ) ∘ (fun z : ℂ => z ^ m)) w v t = _
    rw [hd]
    change (v * ((m : ℂ) * w ^ (m - 1))) * t = _
    ring
  have hquot : (w ^ m)⁻¹ * ((m : ℂ) * w ^ (m - 1)) = (m : ℂ) / w := by
    have he : w ^ m = w ^ (m - 1) * w := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    rw [he]
    field_simp [hw]
  have hid := planarScalarOperator_comp_complex_conjugate A (pow_ne_zero m hw)
    ((m : ℂ) * w ^ (m - 1)) beta c (f := f) (P := P) (w := w) hf hP hfirst hsecond
  dsimp only at hid
  simpa only [hquot] using hid

end DifferentialGeometry.Analysis
