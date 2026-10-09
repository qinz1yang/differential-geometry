import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedWindowConstantsCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedArithmeticCXSP

/-!
# CX-SPINE G7: physical seed scales from dimensionless window constants

Set `Q = H / r²`, `ell = lam / sqrt Q`, `K = k Q`, `tau = delta / Q`,
and `a = t - tau`. These are elementary scale identities and inequalities.
The existential corollary chooses all constants before `r` and `t`.
In particular, `Q * tau = delta` is a fixed positive dimensionless depth.
Neither a positive stage age nor the terminal distance margin is asserted here.
-/

set_option autoImplicit false

open scoped NNReal

namespace GC.LongTime.Ch11

/-- Dimensionless bounds imply the physical radius, curvature, time, age,
and drift inequalities at every legal seed scale. -/
theorem seed_window_scale_of_constants_CXSP
    {H M Δ γ k lam delta : ℝ} (hH : 4 ≤ H) (hM : 0 < M)
    (Ctime Cgrad : ℝ≥0) (hlam : 0 < lam) (hdelta : 0 < delta)
    (hJ : 2 * Real.sqrt 3 * (4 * M + max (8 * M) (2 * Real.exp 4)) ≤ k)
    (hHi : H⁻¹ ≤ k) (hlamH : lam ≤ Real.sqrt H / 50)
    (hlamγ : 2 * lam < γ * Real.sqrt H)
    (hgrad : (Cgrad : ℝ) * lam * Real.sqrt (2 * M) ≤ 1 / 4)
    (hkLam : k * lam ^ 2 ≤ 1) (hdeltaH : delta ≤ H / 4)
    (htimeDim : (Ctime : ℝ) * M * delta ≤ 1 / 2)
    (hdrift : 8 * delta / lam < Δ * Real.sqrt H)
    (r t : ℝ) (hr : 0 < r) (htime : 2 * r ^ 2 < t) :
    let Q := H * (r ^ 2)⁻¹
    let ell := lam / Real.sqrt Q
    let K := k * Q
    let tau := delta / Q
    let a := t - tau
    0 < ell ∧ 0 < tau ∧ tau ≤ r ^ 2 / 4 ∧ 1 ≤ Q * a ∧
      ell ≤ r / 50 ∧ 2 * ell < γ * r ∧
      (Cgrad : ℝ) * ell * Real.sqrt (2 * (M * Q)) ≤ 1 / 4 ∧
      K * ell ^ 2 ≤ 1 ∧ (r ^ 2)⁻¹ ≤ K ∧
      (2 * Real.sqrt 3 * (4 * M + max (8 * M) (2 * Real.exp 4))) * Q ≤ K ∧
      (Ctime : ℝ) * (M * Q) * tau ≤ 1 / 2 ∧ 8 * tau / ell < Δ * r := by
  intro Q ell K tau a
  have hH0 : 0 < H := by linarith
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hell : 0 < ell := div_pos hlam hsQ
  have htau : 0 < tau := div_pos hdelta hQ
  have hrootSq : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt hQ.le
  have hroot : Real.sqrt Q = Real.sqrt H / r := sqrt_seed_scale_CXSP hH0 hr
  have hrRoot : r * Real.sqrt Q = Real.sqrt H := by
    rw [hroot, mul_comm]
    exact div_mul_cancel₀ _ hr.ne'
  have hellRoot : ell * Real.sqrt Q = lam := div_mul_cancel₀ _ hsQ.ne'
  have htauQ : tau * Q = delta := div_mul_cancel₀ _ hQ.ne'
  have hr2Q : r ^ 2 * Q = H := by
    calc
      r ^ 2 * Q = H * (r ^ 2 * (r ^ 2)⁻¹) := by dsimp only [Q]; ring
      _ = H := by rw [mul_inv_cancel₀ (pow_pos hr 2).ne', mul_one]
  refine ⟨hell, htau, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (mul_le_mul_iff_of_pos_right hQ).mp
    calc
      tau * Q = delta := htauQ
      _ ≤ H / 4 := hdeltaH
      _ = (r ^ 2 / 4) * Q := by rw [← hr2Q]; ring
  · have htQ : 2 * H < t * Q := by
      have hh := mul_lt_mul_of_pos_right htime hQ
      nlinarith only [hh, hr2Q]
    have hQa : Q * a = t * Q - delta := by
      calc
        Q * a = t * Q - tau * Q := by dsimp only [a]; ring
        _ = t * Q - delta := by rw [htauQ]
    nlinarith only [hQa, htQ, hdeltaH, hH]
  · apply (mul_le_mul_iff_of_pos_right hsQ).mp
    calc
      ell * Real.sqrt Q = lam := hellRoot
      _ ≤ Real.sqrt H / 50 := hlamH
      _ = (r / 50) * Real.sqrt Q := by rw [← hrRoot]; ring
  · apply (mul_lt_mul_iff_of_pos_right hsQ).mp
    calc
      (2 * ell) * Real.sqrt Q = 2 * lam := by rw [mul_assoc, hellRoot]
      _ < γ * Real.sqrt H := hlamγ
      _ = (γ * r) * Real.sqrt Q := by rw [mul_assoc, hrRoot]
  · have hrootMQ : Real.sqrt (2 * (M * Q)) =
        Real.sqrt (2 * M) * Real.sqrt Q := by
      rw [show 2 * (M * Q) = (2 * M) * Q by ring,
        Real.sqrt_mul (by positivity : 0 ≤ 2 * M)]
    calc
      (Cgrad : ℝ) * ell * Real.sqrt (2 * (M * Q)) =
          (Cgrad : ℝ) * (ell * Real.sqrt Q) * Real.sqrt (2 * M) := by
        rw [hrootMQ]
        ring
      _ = (Cgrad : ℝ) * lam * Real.sqrt (2 * M) := by rw [hellRoot]
      _ ≤ 1 / 4 := hgrad
  · calc
      K * ell ^ 2 = (k * Q) * (lam ^ 2 / Q) := by
        dsimp only [K, ell]
        rw [div_pow, hrootSq]
      _ = k * ((lam ^ 2 / Q) * Q) := by ring
      _ = k * lam ^ 2 := by rw [div_mul_cancel₀ _ hQ.ne']
      _ ≤ 1 := hkLam
  · have hInvQ : H⁻¹ * Q = (r ^ 2)⁻¹ := by
      dsimp only [Q]
      rw [← mul_assoc, inv_mul_cancel₀ hH0.ne', one_mul]
    calc
      (r ^ 2)⁻¹ = H⁻¹ * Q := hInvQ.symm
      _ ≤ k * Q := mul_le_mul_of_nonneg_right hHi hQ.le
      _ = K := rfl
  · exact mul_le_mul_of_nonneg_right hJ hQ.le
  · calc
      (Ctime : ℝ) * (M * Q) * tau = (Ctime : ℝ) * M * (tau * Q) := by ring
      _ = (Ctime : ℝ) * M * delta := by rw [htauQ]
      _ ≤ 1 / 2 := htimeDim
  · apply (div_lt_iff₀ hell).mpr
    apply (mul_lt_mul_iff_of_pos_right hQ).mp
    calc
      (8 * tau) * Q = 8 * delta := by rw [mul_assoc, htauQ]
      _ < (Δ * Real.sqrt H) * lam := (div_lt_iff₀ hlam).mp hdrift
      _ = (Δ * r * ell) * Q := by
        calc
          (Δ * Real.sqrt H) * lam =
              Δ * (r * Real.sqrt Q) * (ell * Real.sqrt Q) := by rw [hrRoot, hellRoot]
          _ = (Δ * r * ell) * (Real.sqrt Q) ^ 2 := by ring
          _ = (Δ * r * ell) * Q := by rw [hrootSq]

/-- Choose the positive dimensionless constants before any seed radius or time. -/
theorem exists_seed_window_scale_CXSP
    {H M Δ γ : ℝ} (hH : 4 ≤ H) (hM : 0 < M)
    (Ctime Cgrad : ℝ≥0) (hΔ : 0 < Δ) (hγ : 0 < γ) :
    ∃ k lam delta : ℝ, 0 < k ∧ 0 < lam ∧ 0 < delta ∧
      ∀ r t : ℝ, 0 < r → 2 * r ^ 2 < t →
        let Q := H * (r ^ 2)⁻¹
        let ell := lam / Real.sqrt Q
        let K := k * Q
        let tau := delta / Q
        let a := t - tau
        0 < ell ∧ 0 < tau ∧ tau ≤ r ^ 2 / 4 ∧ 1 ≤ Q * a ∧
          ell ≤ r / 50 ∧ 2 * ell < γ * r ∧
          (Cgrad : ℝ) * ell * Real.sqrt (2 * (M * Q)) ≤ 1 / 4 ∧
          K * ell ^ 2 ≤ 1 ∧ (r ^ 2)⁻¹ ≤ K ∧
          (2 * Real.sqrt 3 * (4 * M + max (8 * M) (2 * Real.exp 4))) * Q ≤ K ∧
          (Ctime : ℝ) * (M * Q) * tau ≤ 1 / 2 ∧ 8 * tau / ell < Δ * r := by
  obtain ⟨k, lam, delta, hk, hlam, hdelta, hJ, hHi, hlamH, hlamγ, hgrad, hkLam,
    hdeltaH, htimeDim, hdrift⟩ := exists_seed_window_constants_CXSP hH hM Ctime Cgrad hΔ hγ
  refine ⟨k, lam, delta, hk, hlam, hdelta, ?_⟩
  exact seed_window_scale_of_constants_CXSP hH hM Ctime Cgrad hlam hdelta hJ hHi
    hlamH hlamγ hgrad hkLam hdeltaH htimeDim hdrift

end GC.LongTime.Ch11
