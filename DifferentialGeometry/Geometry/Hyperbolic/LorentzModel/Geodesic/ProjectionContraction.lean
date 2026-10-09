/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Geodesic.Projection

open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.ProjectionContraction

open DifferentialGeometry.Hyperbolic
open DifferentialGeometry.HyperbolicConvexity
open DifferentialGeometry.GeodesicProjection

variable {n : ℕ}

section Decomposition

variable (a : HUpper n) (U : LorVec n)

noncomputable def perpComp (x : HUpper n) : LorVec n :=
  x.val - (- lorB x.val a.val) • a.val - (lorB x.val U) • U

theorem perpComp_orth_a (hUa : lorB U a.val = 0) (x : HUpper n) :
    lorB (perpComp a U x) a.val = 0 := by
  change lorB (x.val - (- lorB x.val a.val) • a.val - (lorB x.val U) • U) a.val = 0
  simp only [lorB_sub_left, lorB_smul_left]
  rw [a.is_unit, hUa]
  ring

theorem perpComp_orth_U (hU : lorB U U = 1) (hUa : lorB U a.val = 0) (x : HUpper n) :
    lorB (perpComp a U x) U = 0 := by
  change lorB (x.val - (- lorB x.val a.val) • a.val - (lorB x.val U) • U) U = 0
  simp only [lorB_sub_left, lorB_smul_left]
  have hUa' : lorB a.val U = 0 := by rw [lorB_comm a.val U]; exact hUa
  rw [hU, hUa']
  ring

theorem perpComp_norm_sq (hU : lorB U U = 1) (hUa : lorB U a.val = 0) (x : HUpper n) :
    lorB (perpComp a U x) (perpComp a U x)
      = (- lorB x.val a.val) ^ 2 - (lorB x.val U) ^ 2 - 1 := by
  have hVa : lorB (perpComp a U x) a.val = 0 := perpComp_orth_a a U hUa x
  have hVU : lorB (perpComp a U x) U = 0 := perpComp_orth_U a U hU hUa x
  have h1 : lorB (perpComp a U x) (perpComp a U x) = lorB (perpComp a U x) x.val := by
    change lorB (perpComp a U x) (x.val - (- lorB x.val a.val) • a.val - (lorB x.val U) • U)
      = lorB (perpComp a U x) x.val
    simp only [lorB_sub_right, lorB_smul_right]
    rw [hVa, hVU]
    ring
  rw [h1, lorB_comm (perpComp a U x) x.val]
  change lorB x.val (x.val - (- lorB x.val a.val) • a.val - (lorB x.val U) • U) = _
  simp only [lorB_sub_right, lorB_smul_right]
  rw [x.is_unit]
  ring

theorem perpComp_norm_nonneg (hUa : lorB U a.val = 0) (x : HUpper n) :
    0 ≤ lorB (perpComp a U x) (perpComp a U x) :=
  lorB_self_nonneg_of_orth a.is_unit (perpComp_orth_a a U hUa x)

theorem cosh_dist_eq_quad (hU : lorB U U = 1) (hUa : lorB U a.val = 0) (x y : HUpper n) :
    Real.cosh (dist x y)
      = (- lorB x.val a.val) * (- lorB y.val a.val) - lorB x.val U * lorB y.val U
        - lorB (perpComp a U x) (perpComp a U y) := by
  have hVa : lorB (perpComp a U x) a.val = 0 := perpComp_orth_a a U hUa x
  have hVU : lorB (perpComp a U x) U = 0 := perpComp_orth_U a U hU hUa x
  have hWa : lorB (perpComp a U y) a.val = 0 := perpComp_orth_a a U hUa y
  have hWU : lorB (perpComp a U y) U = 0 := perpComp_orth_U a U hU hUa y
  have hx : x.val = (- lorB x.val a.val) • a.val + (lorB x.val U) • U + perpComp a U x := by
    change x.val = (- lorB x.val a.val) • a.val + (lorB x.val U) • U
      + (x.val - (- lorB x.val a.val) • a.val - (lorB x.val U) • U)
    abel
  have hy : y.val = (- lorB y.val a.val) • a.val + (lorB y.val U) • U + perpComp a U y := by
    change y.val = (- lorB y.val a.val) • a.val + (lorB y.val U) • U
      + (y.val - (- lorB y.val a.val) • a.val - (lorB y.val U) • U)
    abel
  have hUa' : lorB a.val U = 0 := by rw [lorB_comm a.val U]; exact hUa
  have hWa' : lorB a.val (perpComp a U y) = 0 := by rw [lorB_comm a.val]; exact hWa
  have hWU' : lorB U (perpComp a U y) = 0 := by rw [lorB_comm U]; exact hWU
  rw [cosh_dist]
  conv_lhs => rw [hx, hy]
  simp only [lorB_add_left, lorB_add_right, lorB_smul_left, lorB_smul_right]
  rw [a.is_unit, hU, hUa, hUa', hVa, hVU, hWa', hWU']
  ring

theorem cosh_dist_ge_quad (hU : lorB U U = 1) (hUa : lorB U a.val = 0) (x y : HUpper n) :
    Real.cosh (dist x y)
      ≥ (- lorB x.val a.val) * (- lorB y.val a.val) - lorB x.val U * lorB y.val U
        - Real.sqrt (((- lorB x.val a.val) ^ 2 - (lorB x.val U) ^ 2 - 1)
                     * ((- lorB y.val a.val) ^ 2 - (lorB y.val U) ^ 2 - 1)) := by
  have hVa : lorB (perpComp a U x) a.val = 0 := perpComp_orth_a a U hUa x
  have hWa : lorB (perpComp a U y) a.val = 0 := perpComp_orth_a a U hUa y
  have hVV := perpComp_norm_sq a U hU hUa x
  have hWW := perpComp_norm_sq a U hU hUa y
  have hcs : lorB (perpComp a U x) (perpComp a U y) ^ 2
      ≤ lorB (perpComp a U x) (perpComp a U x) * lorB (perpComp a U y) (perpComp a U y) :=
    lorB_sq_le_of_orth a.is_unit hVa hWa
  have hbound : lorB (perpComp a U x) (perpComp a U y)
      ≤ Real.sqrt (((- lorB x.val a.val) ^ 2 - (lorB x.val U) ^ 2 - 1)
                   * ((- lorB y.val a.val) ^ 2 - (lorB y.val U) ^ 2 - 1)) := by
    have h1 : lorB (perpComp a U x) (perpComp a U y)
        ≤ |lorB (perpComp a U x) (perpComp a U y)| := le_abs_self _
    have h2 : |lorB (perpComp a U x) (perpComp a U y)|
        = Real.sqrt (lorB (perpComp a U x) (perpComp a U y) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    have h3 : Real.sqrt (lorB (perpComp a U x) (perpComp a U y) ^ 2)
        ≤ Real.sqrt (lorB (perpComp a U x) (perpComp a U x)
            * lorB (perpComp a U y) (perpComp a U y)) :=
      Real.sqrt_le_sqrt hcs
    rw [hVV, hWW] at h3
    exact h1.trans (h2 ▸ h3)
  rw [cosh_dist_eq_quad a U hU hUa x y]
  linarith [hbound]

end Decomposition

theorem log_le_arcosh {z : ℝ} (hz : 1 ≤ z) : Real.log z ≤ Real.arcosh z := by
  have h2 : z ≤ z + Real.sqrt (z ^ 2 - 1) := by
    have h := Real.sqrt_nonneg (z ^ 2 - 1); linarith
  rw [Real.arcosh]
  exact Real.log_le_log (by positivity) h2

theorem arcosh_cosh_cosh_ge (u v : ℝ) :
    u + v - Real.log 4 ≤ Real.arcosh (Real.cosh u * Real.cosh v) := by
  have hcosh_u : Real.exp u / 2 ≤ Real.cosh u := by
    rw [Real.cosh_eq]
    have h := Real.exp_nonneg (-u)
    have h2 := Real.exp_pos u
    linarith
  have hcosh_v : Real.exp v / 2 ≤ Real.cosh v := by
    rw [Real.cosh_eq]
    have h := Real.exp_nonneg (-v)
    have h2 := Real.exp_pos v
    linarith
  have hcu : (0:ℝ) ≤ Real.cosh u := zero_le_one.trans (Real.one_le_cosh u)
  have hprod : Real.exp (u + v) / 4 ≤ Real.cosh u * Real.cosh v := by
    have h1 : Real.exp u / 2 * (Real.exp v / 2) = Real.exp (u + v) / 4 := by
      rw [Real.exp_add]; ring
    have h2 : Real.exp u / 2 * (Real.exp v / 2) ≤ Real.cosh u * Real.cosh v :=
      mul_le_mul hcosh_u hcosh_v (by positivity) hcu
    linarith [h1, h2]
  have hge1 : (1:ℝ) ≤ Real.cosh u * Real.cosh v := by
    have h1 := Real.one_le_cosh u
    have h2 := Real.one_le_cosh v
    nlinarith [h1, h2]
  have hlog : Real.log (Real.exp (u + v) / 4) ≤ Real.log (Real.cosh u * Real.cosh v) :=
    Real.log_le_log (by positivity) hprod
  have hlogeq : Real.log (Real.exp (u + v) / 4) = u + v - Real.log 4 := by
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (by norm_num : (4:ℝ) ≠ 0), Real.log_exp]
  have hla : Real.log (Real.cosh u * Real.cosh v) ≤ Real.arcosh (Real.cosh u * Real.cosh v) :=
    log_le_arcosh hge1
  linarith [hlog, hlogeq, hla]

theorem proj_coeff {o a b : HUpper n} (hd : a ≠ b) {R t₀ : ℝ}
    (hform : ∀ t : ℝ, Real.cosh (dist o (geodFromTo a b hd t)) = R * Real.cosh (t - t₀)) :
    Real.cosh (dist o a) = R * Real.cosh t₀
    ∧ lorB o.val (dirVec a b) = R * Real.sinh t₀ := by
  have hform' : ∀ t : ℝ, Real.cosh (dist o (geodFromTo a b hd t))
      = (R * Real.cosh t₀) * Real.cosh t - (R * Real.sinh t₀) * Real.sinh t := by
    intro t
    rw [hform t, Real.cosh_sub]
    ring
  have hexp : ∀ t : ℝ, Real.cosh (dist o (geodFromTo a b hd t))
      = Real.cosh t * Real.cosh (dist o a) - lorB o.val (dirVec a b) * Real.sinh t := by
    intro t
    rw [GeodesicProjection.cosh_dist_geod o a b hd t]
    show Real.cosh t * Real.cosh (dist o a) + Real.sinh t * orthCoeff o a b = _
    rw [show orthCoeff o a b = - lorB o.val (dirVec a b) from rfl]
    ring
  have hkey : ∀ t : ℝ, (Real.cosh (dist o a) - R * Real.cosh t₀) * Real.cosh t
      = (lorB o.val (dirVec a b) - R * Real.sinh t₀) * Real.sinh t := by
    intro t
    have e1 := hexp t
    have e2 := hform' t
    linarith [e1, e2]
  have hcosh : Real.cosh (dist o a) = R * Real.cosh t₀ := by
    have e := hkey 0
    rw [Real.cosh_zero, Real.sinh_zero, mul_one, mul_zero] at e
    linarith [e]
  refine ⟨hcosh, ?_⟩
  have e1 := hkey 1
  rw [hcosh, sub_self, zero_mul] at e1
  have hsinh1 : Real.sinh (1:ℝ) ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr zero_lt_one)
  have hz : lorB o.val (dirVec a b) - R * Real.sinh t₀ = 0 :=
    (mul_eq_zero.mp e1.symm).resolve_right hsinh1
  linarith [hz]

theorem cosh_dist_ge_quad_geodesic {x y a b : HUpper n} (hd : a ≠ b)
    {Rx tx Ry ty : ℝ}
    (hformx : ∀ t : ℝ, Real.cosh (dist x (geodFromTo a b hd t)) = Rx * Real.cosh (t - tx))
    (hformy : ∀ t : ℝ, Real.cosh (dist y (geodFromTo a b hd t)) = Ry * Real.cosh (t - ty))
    : Real.cosh (dist x y)
      ≥ Rx * Ry * Real.cosh (tx - ty) - Real.sqrt ((Rx ^ 2 - 1) * (Ry ^ 2 - 1)) := by
  obtain ⟨hx0, hx1⟩ := proj_coeff hd hformx
  obtain ⟨hy0, hy1⟩ := proj_coeff hd hformy
  have h := cosh_dist_ge_quad a (dirVec a b) (lorB_dirVec_self hd) (lorB_dirVec_left a b) x y
  have hcx : - lorB x.val a.val = Rx * Real.cosh tx := by
    have := cosh_dist x a
    linarith [this, hx0]
  have hcy : - lorB y.val a.val = Ry * Real.cosh ty := by
    have := cosh_dist y a
    linarith [this, hy0]
  rw [hcx, hcy, hx1, hy1] at h
  have hcomb : Rx * Real.cosh tx * (Ry * Real.cosh ty)
      - Rx * Real.sinh tx * (Ry * Real.sinh ty)
      = Rx * Ry * Real.cosh (tx - ty) := by
    rw [Real.cosh_sub]; ring
  have hsqrt : (Rx * Real.cosh tx) ^ 2 - (Rx * Real.sinh tx) ^ 2 - 1 = Rx ^ 2 - 1 := by
    have hcs : Real.cosh tx ^ 2 - Real.sinh tx ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq tx
    nlinarith [hcs]
  have hsqrty : (Ry * Real.cosh ty) ^ 2 - (Ry * Real.sinh ty) ^ 2 - 1 = Ry ^ 2 - 1 := by
    have hcs : Real.cosh ty ^ 2 - Real.sinh ty ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq ty
    nlinarith [hcs]
  rw [hsqrt, hsqrty] at h
  linarith [h, hcomb]

theorem cosh_proj_le {x y a b : HUpper n} (hd : a ≠ b)
    {Rx tx Ry ty : ℝ}
    (hformx : ∀ t : ℝ, Real.cosh (dist x (geodFromTo a b hd t)) = Rx * Real.cosh (t - tx))
    (hformy : ∀ t : ℝ, Real.cosh (dist y (geodFromTo a b hd t)) = Ry * Real.cosh (t - ty))
    (hRx : 1 ≤ Rx) (hRy : 1 ≤ Ry) :
    Real.cosh (tx - ty)
      ≤ (Real.cosh (dist x y) + Real.sqrt ((Rx ^ 2 - 1) * (Ry ^ 2 - 1))) / (Rx * Ry) := by
  have h := cosh_dist_ge_quad_geodesic hd hformx hformy
  have hRpos : 0 < Rx * Ry :=
    mul_pos (lt_of_lt_of_le one_pos hRx) (lt_of_lt_of_le one_pos hRy)
  rw [le_div_iff₀ hRpos]
  have h2 : Real.cosh (tx - ty) * (Rx * Ry) = Rx * Ry * Real.cosh (tx - ty) := by ring
  rw [h2]
  linarith [h]

theorem half_le_sinh {t : ℝ} (ht : 0 ≤ t) : t / 2 ≤ Real.sinh t := by
  rw [Real.sinh_eq]
  have h1 : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  have h2 : Real.exp (-t) ≤ 1 := by
    rw [Real.exp_neg]
    exact inv_le_one_of_one_le₀ (by linarith [h1])
  have h3 := Real.exp_pos t
  linarith [h1, h2]

theorem sq_div_eight_le_cosh_sub_one (t : ℝ) : t ^ 2 / 8 ≤ Real.cosh t - 1 := by
  have h1 : Real.cosh t - 1 = 2 * Real.sinh (t / 2) ^ 2 := by
    have e1 : Real.cosh t = Real.cosh (2 * (t / 2)) := by ring_nf
    rw [e1, Real.cosh_two_mul]
    have e2 : Real.cosh (t / 2) ^ 2 = Real.sinh (t / 2) ^ 2 + 1 := by
      have h := Real.cosh_sq_sub_sinh_sq (t / 2)
      linarith [h]
    linarith [e2]
  rw [h1]
  rcases le_or_gt 0 (t / 2) with htv | htv
  · have hs := half_le_sinh htv
    have h2 : (t / 2 / 2) ^ 2 ≤ Real.sinh (t / 2) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hs 2
    nlinarith [h2]
  · have hs := half_le_sinh (show (0:ℝ) ≤ -(t / 2) by linarith)
    rw [show -(t / 2) = -(t / 2) from rfl] at hs
    rw [Real.sinh_neg] at hs
    have h3 : Real.sinh (t / 2) ≤ t / 2 / 2 := by linarith [hs]
    have h5 : (0:ℝ) ≤ (Real.sinh (t / 2) - t / 2 / 2) * (Real.sinh (t / 2) + t / 2 / 2) := by
      apply mul_nonneg_of_nonpos_of_nonpos (by linarith [h3])
      have htv' : t / 2 < 0 := htv
      have : Real.sinh (t / 2) + t / 2 / 2 ≤ t / 2 / 2 + t / 2 / 2 := by linarith [h3]
      linarith [this, htv']
    have h6 : (Real.sinh (t / 2) - t / 2 / 2) * (Real.sinh (t / 2) + t / 2 / 2)
        = Real.sinh (t / 2) ^ 2 - (t / 2 / 2) ^ 2 := by ring
    have h7 : (t / 2 / 2) ^ 2 ≤ Real.sinh (t / 2) ^ 2 := by linarith [h5, h6]
    nlinarith [h7]

theorem cosh_proj_sub_one_le {x y a b : HUpper n} (hd : a ≠ b)
    {Rx tx Ry ty : ℝ}
    (hformx : ∀ t : ℝ, Real.cosh (dist x (geodFromTo a b hd t)) = Rx * Real.cosh (t - tx))
    (hformy : ∀ t : ℝ, Real.cosh (dist y (geodFromTo a b hd t)) = Ry * Real.cosh (t - ty))
    (hRx : 1 ≤ Rx) (hRy : 1 ≤ Ry) :
    Real.cosh (tx - ty) - 1 ≤ Real.cosh (dist x y) / (Rx * Ry) := by
  have h := cosh_proj_le hd hformx hformy hRx hRy
  have hRpos : (0:ℝ) < Rx * Ry :=
    mul_pos (lt_of_lt_of_le one_pos hRx) (lt_of_lt_of_le one_pos hRy)
  have hsqrt : Real.sqrt ((Rx ^ 2 - 1) * (Ry ^ 2 - 1)) ≤ Rx * Ry := by
    have h1 : (Rx ^ 2 - 1) * (Ry ^ 2 - 1) ≤ (Rx * Ry) ^ 2 := by
      have hRx2 : (1:ℝ) ^ 2 ≤ Rx ^ 2 := (sq_le_sq₀ zero_le_one (zero_le_one.trans hRx)).mpr hRx
      have hRy2 : (1:ℝ) ^ 2 ≤ Ry ^ 2 := (sq_le_sq₀ zero_le_one (zero_le_one.trans hRy)).mpr hRy
      nlinarith [sq_nonneg Rx, sq_nonneg Ry, hRx2, hRy2]
    calc Real.sqrt ((Rx ^ 2 - 1) * (Ry ^ 2 - 1)) ≤ Real.sqrt ((Rx * Ry) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Rx * Ry := Real.sqrt_sq hRpos.le
  have h2 : Real.cosh (tx - ty)
      ≤ (Real.cosh (dist x y) + Rx * Ry) / (Rx * Ry) := by
    rw [le_div_iff₀ hRpos]
    have h4 := (le_div_iff₀ hRpos).mp h
    linarith [h4, hsqrt]
  have h5 : (Real.cosh (dist x y) + Rx * Ry) / (Rx * Ry)
      = Real.cosh (dist x y) / (Rx * Ry) + 1 := by
    rw [add_div, div_self hRpos.ne']
  linarith [h2, h5]

theorem dist_proj_le_exp {x y a b : HUpper n} (hd : a ≠ b)
    {Rx tx Ry ty : ℝ}
    (hformx : ∀ t : ℝ, Real.cosh (dist x (geodFromTo a b hd t)) = Rx * Real.cosh (t - tx))
    (hformy : ∀ t : ℝ, Real.cosh (dist y (geodFromTo a b hd t)) = Ry * Real.cosh (t - ty))
    (hRx : 1 ≤ Rx) (hRy : 1 ≤ Ry)
    {R : ℝ} (hRxR : Real.cosh R ≤ Rx) (hRyR : Real.cosh R ≤ Ry) :
    |tx - ty| ≤ 2 * Real.sqrt (8 * Real.cosh (dist x y)) * Real.exp (-R) := by
  have hsub := cosh_proj_sub_one_le hd hformx hformy hRx hRy
  set u := |tx - ty| with hu
  have hu0 : (0:ℝ) ≤ u := abs_nonneg _
  have hcosh_eq : Real.cosh u = Real.cosh (tx - ty) := by rw [hu, Real.cosh_abs]
  have hcoshR0 : (0:ℝ) < Real.cosh R := Real.cosh_pos R
  have hRR : Real.cosh R * Real.cosh R ≤ Rx * Ry :=
    mul_le_mul hRxR hRyR hcoshR0.le (zero_le_one.trans hRx)
  have hRpos : (0:ℝ) < Rx * Ry :=
    mul_pos (lt_of_lt_of_le one_pos hRx) (lt_of_lt_of_le one_pos hRy)
  have hquad : u ^ 2 / 8 ≤ Real.cosh (dist x y) / (Rx * Ry) := by
    have h1 := sq_div_eight_le_cosh_sub_one u
    rw [hcosh_eq] at h1
    exact h1.trans hsub
  have h1 : Real.cosh (dist x y) / (Rx * Ry)
      ≤ Real.cosh (dist x y) / (Real.cosh R * Real.cosh R) :=
    div_le_div_of_nonneg_left (Real.cosh_pos _).le (by positivity) hRR
  have h2 : u ^ 2 / 8 ≤ Real.cosh (dist x y) / (Real.cosh R * Real.cosh R) :=
    hquad.trans h1
  have hquad2 : u ^ 2 ≤ 8 * Real.cosh (dist x y) / (Real.cosh R) ^ 2 := by
    have h4 : Real.cosh (dist x y) / (Real.cosh R * Real.cosh R) * 8
        = 8 * Real.cosh (dist x y) / (Real.cosh R) ^ 2 := by
      have h3 : Real.cosh R ^ 2 = Real.cosh R * Real.cosh R := pow_two _
      rw [h3]
      ring
    rw [← h4]
    exact (div_le_iff₀ (by norm_num : (0:ℝ) < 8)).mp h2
  have hu_le : u ≤ Real.sqrt (8 * Real.cosh (dist x y) / (Real.cosh R) ^ 2) := by
    have h1 : u = Real.sqrt (u ^ 2) := (Real.sqrt_sq hu0).symm
    rw [h1]
    exact Real.sqrt_le_sqrt hquad2
  have hsplit : Real.sqrt (8 * Real.cosh (dist x y) / (Real.cosh R) ^ 2)
      = Real.sqrt (8 * Real.cosh (dist x y)) / Real.cosh R := by
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hcoshR0.le]
  have hinv : (Real.cosh R)⁻¹ ≤ 2 * Real.exp (-R) := by
    have h1 : Real.exp R / 2 ≤ Real.cosh R := GromovBoundary.exp_div_two_le_cosh R
    calc (Real.cosh R)⁻¹ ≤ (Real.exp R / 2)⁻¹ :=
          inv_anti₀ (by positivity : (0:ℝ) < Real.exp R / 2) h1
      _ = 2 * Real.exp (-R) := by
          rw [Real.exp_neg, inv_div]
          exact (div_eq_mul_inv 2 (Real.exp R)).symm
  calc u ≤ Real.sqrt (8 * Real.cosh (dist x y)) / Real.cosh R :=
        hu_le.trans_eq hsplit
    _ = Real.sqrt (8 * Real.cosh (dist x y)) * (Real.cosh R)⁻¹ := div_eq_mul_inv _ _
    _ ≤ Real.sqrt (8 * Real.cosh (dist x y)) * (2 * Real.exp (-R)) :=
        mul_le_mul_of_nonneg_left hinv (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (8 * Real.cosh (dist x y)) * Real.exp (-R) := by ring

end DifferentialGeometry.ProjectionContraction
