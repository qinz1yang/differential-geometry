/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.CriticalPoint
import DifferentialGeometry.Topology.Morse.CriticalPoints
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.Compact

open Set Filter Function
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Topology.Morse (IsCriticalPointAt IsNondegenerateCriticalPointAt
  isNondegenerateCriticalPointAt_model_iff chartHessianAt)

namespace DifferentialGeometry.Morse

private theorem exists_pos_bound_of_contDiff_compactSupport {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, |f x| ≤ B ∧ |deriv f x| ≤ B := by
  have hd : Continuous (deriv f) :=
    hf.continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := hf.continuous.abs.bddAbove_range_of_hasCompactSupport hfc.abs
  obtain ⟨C, hC⟩ := hd.abs.bddAbove_range_of_hasCompactSupport hfc.deriv.abs
  refine ⟨max (max B C) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  exact ⟨(hB (mem_range_self x)).trans ((le_max_left _ _).trans (le_max_left _ _)),
    (hC (mem_range_self x)).trans ((le_max_right _ _).trans (le_max_left _ _))⟩

theorem exists_compactly_supported_cubic_perturbation {a : ℝ} (ha : 0 < a) :
    ∃ u : ℝ → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
      ∀ x : ℝ, 0 < x ^ 2 - a + deriv u x := by
  let χ : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let θ : ℝ → ℝ := fun x => x * χ x
  have hθ : ContDiff ℝ ∞ θ := contDiff_id.mul χ.contDiff
  have hθc : HasCompactSupport θ := χ.hasCompactSupport.mul_left
  obtain ⟨B, hB, hbound⟩ := exists_pos_bound_of_contDiff_compactSupport hθ hθc
  let R := Real.sqrt (a + 2 * a * B + 1)
  have hR : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hR2 : R ^ 2 = a + 2 * a * B + 1 := Real.sq_sqrt (by positivity)
  let u : ℝ → ℝ := fun x => 2 * a * R * θ (x / R)
  have hu : ContDiff ℝ ∞ u := contDiff_const.mul (hθ.comp (contDiff_id.div_const R))
  have huc : HasCompactSupport u := by
    have hc : HasCompactSupport (fun x => θ (x / R)) :=
      hθc.comp_homeomorph (Homeomorph.mulRight₀ R hR.ne').symm
    exact hc.mul_left
  have hdu (x : ℝ) : deriv u x = 2 * a * deriv θ (x / R) := by
    have hd := ((hθ.differentiable (by simp)) (x / R)).hasDerivAt.comp x
      ((hasDerivAt_id x).div_const R)
    have hdc := hd.const_mul (2 * a * R)
    calc
      deriv u x = 2 * a * R * (deriv θ (x / R) * (1 / R)) := hdc.deriv
      _ = 2 * a * deriv θ (x / R) := by field_simp
  refine ⟨u, hu, huc, fun x => ?_⟩
  rw [hdu]
  by_cases hx : |x / R| < 1
  · have heq : θ =ᶠ[𝓝 (x / R)] id := by
      filter_upwards [χ.eventuallyEq_one_of_mem_ball (by
        simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hx)] with y hy
      simp only [θ, hy, Pi.one_apply, mul_one, id_eq]
    have hdθ : deriv θ (x / R) = 1 := by rw [heq.deriv_eq]; exact deriv_id _
    rw [hdθ]
    nlinarith [sq_nonneg x]
  · have hxR : R ≤ |x| := by
      have := le_of_not_gt hx
      rw [abs_div, abs_of_pos hR, le_div_iff₀ hR] at this
      simpa only [one_mul] using this
    have hx2 : R ^ 2 ≤ x ^ 2 := by
      have h := sq_le_sq₀ hR.le (abs_nonneg x) |>.mpr hxR
      simpa only [sq_abs] using h
    have hdθ := (abs_le.mp (hbound (x / R)).2).1
    nlinarith

theorem exists_regular_quadratic_suspension {f u : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u)
    (hreg : ∀ x, deriv f x + deriv u x ≠ 0) :
    ∃ g : ℝ × ℝ → ℝ, ContDiff ℝ ∞ g ∧
      HasCompactSupport (fun p => g p - (f p.1 + p.2 ^ 2)) ∧
      (∀ p, ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt 𝓘(ℝ, ℝ × ℝ) g p) ∧
      ∃ S : ℝ, 0 < S ∧ ∀ x y : ℝ, |y| < S → g (x, y) = f x + u x + y ^ 2 := by
  let χ : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  obtain ⟨B, hB, hBu⟩ := exists_pos_bound_of_contDiff_compactSupport hu huc
  obtain ⟨C, hC, hCχ⟩ := exists_pos_bound_of_contDiff_compactSupport
    (χ.contDiff : ContDiff ℝ ∞ χ) χ.hasCompactSupport
  let S := Real.sqrt (B * C + 1)
  have hS : 0 < S := Real.sqrt_pos.mpr (by positivity)
  have hS2 : S ^ 2 = B * C + 1 := Real.sq_sqrt (by positivity)
  let b : ℝ → ℝ := fun y => χ (y / S)
  have hb : ContDiff ℝ ∞ b := χ.contDiff.comp (contDiff_id.div_const S)
  have hbc : HasCompactSupport b :=
    χ.hasCompactSupport.comp_homeomorph (Homeomorph.mulRight₀ S hS.ne').symm
  let g : ℝ × ℝ → ℝ := fun p => f p.1 + p.2 ^ 2 + u p.1 * b p.2
  have hg : ContDiff ℝ ∞ g :=
    ((hf.comp contDiff_fst).add (contDiff_snd.pow 2)).add
      ((hu.comp contDiff_fst).mul (hb.comp contDiff_snd))
  have hcompact : HasCompactSupport (fun p : ℝ × ℝ => g p - (f p.1 + p.2 ^ 2)) := by
    have hs : support (fun p : ℝ × ℝ => g p - (f p.1 + p.2 ^ 2)) ⊆
        tsupport u ×ˢ tsupport b := by
      intro p hp
      constructor
      · by_contra hx
        have hz := image_eq_zero_of_notMem_tsupport hx
        exact hp (by simp [g, hz])
      · by_contra hy
        have hz := image_eq_zero_of_notMem_tsupport hy
        exact hp (by simp [g, hz])
    exact (huc.prod hbc).of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal hs ((isClosed_tsupport u).prod (isClosed_tsupport b)))
  have hbone {y : ℝ} (hy : |y| < S) : b y = 1 := by
    apply χ.one_of_mem_closedBall
    change |y / S - 0| ≤ 1
    rw [sub_zero, abs_div, abs_of_pos hS, div_le_iff₀ hS, one_mul]
    exact hy.le
  have hbderiv (y : ℝ) : deriv b y = deriv χ (y / S) / S := by
    have hd := ((χ.contDiff : ContDiff ℝ ∞ χ).differentiable (by simp) (y / S)).hasDerivAt
    simpa only [b, comp_def, id_eq, div_eq_mul_inv, one_mul] using
      (hd.comp y ((hasDerivAt_id y).div_const S)).deriv
  refine ⟨g, hg, hcompact, ?_, S, hS, ?_⟩
  · rintro ⟨x, y⟩ hc
    have hzero : fderiv ℝ g (x, y) = 0 := by
      change mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) g (x, y) = 0 at hc
      rw [mfderiv_eq_fderiv] at hc
      exact hc
    have hxzero : deriv (fun z => g (z, y)) x = 0 := by
      have hd := (hg.differentiable (by simp) (x, y)).hasFDerivAt.comp x
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
      rw [hzero, ContinuousLinearMap.zero_comp] at hd
      simpa only [comp_def, zero_apply] using hd.hasDerivAt.deriv
    have hyzero : deriv (fun z => g (x, z)) y = 0 := by
      have hd := (hg.differentiable (by simp) (x, y)).hasFDerivAt.comp y
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)
      rw [hzero, ContinuousLinearMap.zero_comp] at hd
      simpa only [comp_def, zero_apply] using hd.hasDerivAt.deriv
    have hdy : 2 * y + u x * deriv b y = 0 := by
      have hd := ((hasDerivAt_const y (f x)).add ((hasDerivAt_id y).pow 2)).add
        ((hb.differentiable (by simp) y).hasDerivAt.const_mul (u x))
      have heq : deriv (fun z => g (x, z)) y = 2 * y + u x * deriv b y := by
        simpa only [g, Pi.add_apply, Pi.pow_apply, id_eq, pow_one, Nat.cast_ofNat,
          mul_one, zero_add, Nat.reduceSub] using! hd.deriv
      exact heq.symm.trans hyzero
    have hy : y = 0 := by
      by_cases hy : |y| < S
      · have heq : b =ᶠ[𝓝 y] 1 := by
          filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hy] with z hz
          exact hbone hz
        have hdb : deriv b y = 0 := by rw [heq.deriv_eq]; exact deriv_const y 1
        rw [hdb, mul_zero, add_zero] at hdy
        linarith
      · have hyS : S ≤ |y| := le_of_not_gt hy
        have hnorm : |u x * deriv b y| ≤ B * C / S := by
          rw [hbderiv, abs_mul, abs_div, abs_of_pos hS, ← mul_div_assoc]
          exact div_le_div_of_nonneg_right
            (mul_le_mul (hBu x).1 (hCχ (y / S)).2 (abs_nonneg _) hB.le) hS.le
        have habs : |u x * deriv b y| = 2 * |y| := by
          have heq : u x * deriv b y = -(2 * y) := by linarith
          rw [heq, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        rw [habs, le_div_iff₀ hS] at hnorm
        nlinarith [mul_le_mul_of_nonneg_right hyS hS.le]
    subst y
    have hdx : deriv f x + deriv u x = 0 := by
      have hd := ((hf.differentiable (by simp) x).hasDerivAt.add_const (0 : ℝ)).add
        ((hu.differentiable (by simp) x).hasDerivAt.mul_const (b 0))
      have heq : deriv (fun z => g (z, 0)) x = deriv f x + deriv u x := by
        have hb0 : b 0 = 1 := hbone (by simpa only [abs_zero] using hS)
        simpa only [g, Pi.add_apply, id_eq, zero_pow (by decide : 2 ≠ 0),
          add_zero, hb0, mul_one] using! hd.deriv
      exact heq.symm.trans hxzero
    exact hreg x hdx
  · intro x y hy
    dsimp [g]
    rw [hbone hy]
    ring

theorem exists_compactly_supported_cubic_suspension_cancellation {a : ℝ} (ha : 0 < a) :
    ∃ g : ℝ × ℝ → ℝ, ContDiff ℝ ∞ g ∧
      HasCompactSupport (fun p => g p - (p.1 ^ 3 / 3 - a * p.1 + p.2 ^ 2)) ∧
      ∀ p, ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt 𝓘(ℝ, ℝ × ℝ) g p := by
  obtain ⟨u, hu, huc, hpos⟩ := exists_compactly_supported_cubic_perturbation ha
  have hf : ContDiff ℝ ∞ (fun x : ℝ => x ^ 3 / 3 - a * x) := by fun_prop
  have hdf (x : ℝ) : deriv (fun x : ℝ => x ^ 3 / 3 - a * x) x = x ^ 2 - a := by
    have hd := (((hasDerivAt_id x).pow 3).div_const 3).sub
      ((hasDerivAt_id x).const_mul a)
    simpa only [Pi.sub_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat,
      mul_one, Nat.reduceSub, mul_div_cancel_left₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
      using! hd.deriv
  obtain ⟨g, hg, hgc, hreg, _⟩ := exists_regular_quadratic_suspension hf hu huc
    (fun x => by rw [hdf]; exact (hpos x).ne')
  exact ⟨g, hg, hgc, hreg⟩

theorem hasFDerivAt_cubic_suspension (a : ℝ) (p : ℝ × ℝ) :
    HasFDerivAt (fun q : ℝ × ℝ => q.1 ^ 3 / 3 - a * q.1 + q.2 ^ 2)
      ((p.1 ^ 2 - a) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (2 * p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  have hx : HasFDerivAt (fun q : ℝ × ℝ => q.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hy : HasFDerivAt (fun q : ℝ × ℝ => q.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have hd := (((hx.pow 3).mul_const ((3 : ℝ)⁻¹)).sub (hx.const_mul a)).add (hy.pow 2)
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  change (p.1 ^ 2 - a) * v.1 + (2 * p.2) * v.2 =
    (3 : ℝ)⁻¹ * (3 * p.1 ^ (3 - 1) * v.1) - a * v.1 +
      2 * p.2 ^ (2 - 1) * v.2
  norm_num
  ring

theorem isCriticalPointAt_cubic_suspension_iff (a : ℝ) (p : ℝ × ℝ) :
    DifferentialGeometry.Topology.Morse.IsCriticalPointAt 𝓘(ℝ, ℝ × ℝ)
      (fun q : ℝ × ℝ => q.1 ^ 3 / 3 - a * q.1 + q.2 ^ 2) p ↔
        p.1 ^ 2 = a ∧ p.2 = 0 := by
  unfold DifferentialGeometry.Topology.Morse.IsCriticalPointAt
  rw [mfderiv_eq_fderiv, (hasFDerivAt_cubic_suspension a p).fderiv]
  constructor
  · intro h
    have hx := congrArg (fun D : ℝ × ℝ →L[ℝ] ℝ => D (1, 0)) h
    have hy := congrArg (fun D : ℝ × ℝ →L[ℝ] ℝ => D (0, 1)) h
    change (p.1 ^ 2 - a) * 1 + (2 * p.2) * 0 = 0 at hx
    change (p.1 ^ 2 - a) * 0 + (2 * p.2) * 1 = 0 at hy
    constructor <;> linarith
  · rintro ⟨hx, hy⟩
    rw [hx, hy]
    apply ContinuousLinearMap.ext
    intro v
    change (a - a) * v.1 + (2 * 0) * v.2 = 0
    ring

theorem fderiv_fderiv_cubic_suspension_apply (a : ℝ) (p v w : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => q.1 ^ 3 / 3 - a * q.1 + q.2 ^ 2)) p v w =
      2 * p.1 * v.1 * w.1 + 2 * v.2 * w.2 := by
  have heq : fderiv ℝ (fun q : ℝ × ℝ => q.1 ^ 3 / 3 - a * q.1 + q.2 ^ 2) =
      fun q => (q.1 ^ 2 - a) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (2 * q.2) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    funext q
    exact (hasFDerivAt_cubic_suspension a q).fderiv
  have hx : HasFDerivAt (fun q : ℝ × ℝ => q.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hy : HasFDerivAt (fun q : ℝ × ℝ => q.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have hd := (((hx.pow 2).sub_const a).smul_const (ContinuousLinearMap.fst ℝ ℝ ℝ)).add
    ((hy.const_mul 2).smul_const (ContinuousLinearMap.snd ℝ ℝ ℝ))
  change HasFDerivAt (fun q : ℝ × ℝ => (q.1 ^ 2 - a) •
    ContinuousLinearMap.fst ℝ ℝ ℝ + (2 * q.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) _ p at hd
  rw [heq, hd.fderiv]
  simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul]

theorem isNondegenerateCriticalPointAt_cubic_suspension_iff (a : ℝ) (p : ℝ × ℝ) :
    IsNondegenerateCriticalPointAt 𝓘(ℝ, ℝ × ℝ)
      (fun q : ℝ × ℝ => q.1 ^ 3 / 3 - a * q.1 + q.2 ^ 2) p ↔
      p.1 ^ 2 = a ∧ p.2 = 0 ∧ p.1 ≠ 0 := by
  have hs : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => q.1 ^ 3 / 3 - a * q.1 + q.2 ^ 2) p := by
    fun_prop
  rw [isNondegenerateCriticalPointAt_model_iff hs]
  have hc : (fderiv ℝ (fun q : ℝ × ℝ => q.1 ^ 3 / 3 - a * q.1 + q.2 ^ 2) p = 0) ↔
      p.1 ^ 2 = a ∧ p.2 = 0 := by
    simpa only [IsCriticalPointAt, mfderiv_eq_fderiv] using!
      isCriticalPointAt_cubic_suspension_iff a p
  rw [hc]
  constructor
  · rintro ⟨⟨hpa, hp2⟩, hinj⟩
    refine ⟨hpa, hp2, fun hp1 => ?_⟩
    have hker : fderiv ℝ (fderiv ℝ
        (fun q : ℝ × ℝ => q.1 ^ 3 / 3 - a * q.1 + q.2 ^ 2)) p (1, 0) = 0 := by
      apply ContinuousLinearMap.ext
      intro w
      rw [fderiv_fderiv_cubic_suspension_apply]
      simp [hp1]
    have he := hinj (hker.trans (map_zero _).symm)
    have hb := congrArg Prod.fst he
    norm_num at hb
  · rintro ⟨hpa, hp2, hp1⟩
    refine ⟨⟨hpa, hp2⟩, fun v w hvw => ?_⟩
    have hx := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ => L (1, 0)) hvw
    have hy := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ => L (0, 1)) hvw
    simp only [fderiv_fderiv_cubic_suspension_apply] at hx hy
    apply Prod.ext
    · have hmul : (2 * p.1) * v.1 = (2 * p.1) * w.1 := by simpa using hx
      exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hp1) hmul
    · linarith

theorem sigNeg_chartHessianAt_cubic_suspension (a : ℝ) (p : ℝ × ℝ) :
    sigNeg (chartHessianAt (fun q : ℝ × ℝ => q.1 ^ 3 / 3 - a * q.1 + q.2 ^ 2) p) =
      if p.1 < 0 then 1 else 0 := by
  classical
  let w : Fin 2 → ℝ := ![2 * p.1, 2]
  have he : QuadraticMap.Equivalent
      (chartHessianAt (fun q : ℝ × ℝ => q.1 ^ 3 / 3 - a * q.1 + q.2 ^ 2) p)
      (QuadraticMap.weightedSumSquares ℝ w) := by
    refine ⟨{ (LinearEquiv.finTwoArrow ℝ ℝ).symm with map_app' := ?_ }⟩
    intro v
    change _ = fderiv ℝ (fderiv ℝ
      (fun q : ℝ × ℝ => q.1 ^ 3 / 3 - a * q.1 + q.2 ^ 2)) p v v
    rw [fderiv_fderiv_cubic_suspension_apply]
    simp [QuadraticMap.weightedSumSquares_apply, w, Fin.sum_univ_two,
      LinearEquiv.finTwoArrow, mul_assoc]
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares he]
  by_cases hp : p.1 < 0
  · have hw : {i | w i < 0} = ({0} : Set (Fin 2)) := by
      ext i
      fin_cases i <;> simp [w]
      linarith
    rw [hw, Set.ncard_singleton, ite_eq_left hp]
  · have hw : {i | w i < 0} = (∅ : Set (Fin 2)) := by
      ext i
      fin_cases i <;> simp [w]
      linarith
    rw [hw, Set.ncard_empty, ite_eq_right hp]

theorem strictAntiOn_cubic_between_critical_points {a : ℝ} (ha : 0 ≤ a) :
    StrictAntiOn (fun x : ℝ => x ^ 3 / 3 - a * x)
      (Icc (-Real.sqrt a) (Real.sqrt a)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (by fun_prop)
  intro x hx
  rw [interior_Icc] at hx
  have hd : deriv (fun x : ℝ => x ^ 3 / 3 - a * x) x = x ^ 2 - a := by
    have h := (((hasDerivAt_id x).pow 3).div_const 3).sub ((hasDerivAt_id x).const_mul a)
    simpa only [Pi.sub_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat,
      mul_one, Nat.reduceSub, mul_div_cancel_left₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
      using! h.deriv
  rw [hd]
  have hpos : 0 < (x + Real.sqrt a) * (Real.sqrt a - x) :=
    mul_pos (by linarith [hx.1]) (by linarith [hx.2])
  nlinarith [Real.sq_sqrt ha]

end DifferentialGeometry.Morse
