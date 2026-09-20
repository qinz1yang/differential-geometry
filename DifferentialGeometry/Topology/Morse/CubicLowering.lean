/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.CubicCancellation
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Lowering cubic critical pairs with arbitrarily narrow transverse support. -/

open Set Filter Function
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Morse

theorem exists_nonpos_cubic_perturbation {a : ℝ} (ha : 0 < a) :
    ∃ R : ℝ, Real.sqrt a < R ∧ ∃ u : ℝ → ℝ,
      ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧ tsupport u ⊆ Icc (-R) R ∧
      (∀ x, u x ≤ 0) ∧ ∀ x, 0 < x ^ 2 - a + deriv u x := by
  obtain ⟨u, hu, huc, hpos⟩ := exists_compactly_supported_cubic_perturbation ha
  obtain ⟨R, hR, hRu⟩ := huc.isBounded.subset_ball_lt 0 0
  obtain ⟨B₀, hB₀⟩ := hu.continuous.abs.bddAbove_range_of_hasCompactSupport huc.abs
  let B := max B₀ 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hBu (x : ℝ) : |u x| ≤ B := (hB₀ (mem_range_self x)).trans (le_max_left _ _)
  let χ : ContDiffBump (0 : ℝ) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  obtain ⟨C₀, hC₀⟩ := ((χ.contDiff : ContDiff ℝ ∞ χ).continuous_deriv (by simp)).abs
    |>.bddAbove_range_of_hasCompactSupport χ.hasCompactSupport.deriv.abs
  let C := max C₀ 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCχ (x : ℝ) : |deriv χ x| ≤ C :=
    (hC₀ (mem_range_self x)).trans (le_max_left _ _)
  let T := max R (Real.sqrt (a + B * C + 1)) + 1
  have hRT : R < T := (le_max_left _ _).trans_lt (lt_add_one _)
  have hT1 : 1 ≤ T := by
    dsimp [T]
    linarith [le_max_left R (Real.sqrt (a + B * C + 1))]
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hT2 : a + B * C < T ^ 2 := by
    have hs := Real.sq_sqrt (show 0 ≤ a + B * C + 1 by positivity)
    have ht : Real.sqrt (a + B * C + 1) < T :=
      (le_max_right _ _).trans_lt (lt_add_one _)
    nlinarith [Real.sqrt_nonneg (a + B * C + 1)]
  let b : ℝ → ℝ := fun x => χ (x / T)
  have hb : ContDiff ℝ ∞ b := χ.contDiff.comp (contDiff_id.div_const T)
  have hbc : HasCompactSupport b :=
    χ.hasCompactSupport.comp_homeomorph (Homeomorph.mulRight₀ T hT.ne').symm
  have hbone {x : ℝ} (hx : |x| < T) : b =ᶠ[𝓝 x] 1 := by
    have hx' : x / T ∈ Metric.ball 0 χ.rIn := by
      change |x / T - 0| < 1
      rw [sub_zero, abs_div, abs_of_pos hT, div_lt_iff₀ hT, one_mul]
      exact hx
    exact (χ.eventuallyEq_one_of_mem_ball hx').comp_tendsto
      ((continuous_id.div_const T).tendsto x)
  have hbderiv (x : ℝ) : deriv b x = deriv χ (x / T) / T := by
    have hd := ((χ.contDiff : ContDiff ℝ ∞ χ).differentiable (by simp) (x / T)).hasDerivAt
    simpa only [b, comp_def, id_eq, div_eq_mul_inv, one_mul] using
      (hd.comp x ((hasDerivAt_id x).div_const T)).deriv
  have huz {x : ℝ} (hx : T ≤ |x|) : x ∉ tsupport u := by
    intro hx'
    have huR : |x| < R := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hRu hx'
    linarith
  let v : ℝ → ℝ := fun x => u x - B * b x
  have hv : ContDiff ℝ ∞ v := hu.sub (contDiff_const.mul hb)
  have hvc : HasCompactSupport v := huc.sub hbc.mul_left
  refine ⟨2 * T, ?_, v, hv, hvc, ?_, ?_, ?_⟩
  · have hs := Real.sq_sqrt ha.le
    nlinarith [Real.sqrt_nonneg a, mul_pos hB hC]
  · apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hx'
    have hxT : 2 * T < |x| := lt_of_not_ge (fun h => hx' (abs_le.mp h))
    have hu0 := image_eq_zero_of_notMem_tsupport (huz (by linarith : T ≤ |x|))
    have hχ0 : χ (x / T) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      rw [χ.tsupport_eq]
      change ¬ |x / T - 0| ≤ 2
      rw [sub_zero, abs_div, abs_of_pos hT, div_le_iff₀ hT]
      exact not_le.mpr hxT
    exact hx (by simp [v, b, hu0, hχ0])
  · intro x
    by_cases hx : |x| < T
    · have hb1 := (hbone hx).eq_of_nhds
      change u x - B * b x ≤ 0
      rw [show b x = 1 from hb1, mul_one]
      exact sub_nonpos.mpr ((le_abs_self _).trans (hBu x))
    · have hu0 := image_eq_zero_of_notMem_tsupport (huz (le_of_not_gt hx))
      change u x - B * b x ≤ 0
      rw [hu0]
      exact sub_nonpos.mpr (mul_nonneg hB.le χ.nonneg)
  · intro x
    have hdv : deriv v x = deriv u x - B * deriv b x :=
      ((hu.differentiable (by simp) x).hasDerivAt.sub
        ((hb.differentiable (by simp) x).hasDerivAt.const_mul B)).deriv
    rw [hdv]
    by_cases hx : |x| < T
    · have hdb : deriv b x = 0 := by rw [(hbone hx).deriv_eq]; exact deriv_const x 1
      simpa only [hdb, mul_zero, sub_zero] using hpos x
    · rw [deriv_of_notMem_tsupport (huz (le_of_not_gt hx)), hbderiv]
      have hdx : deriv χ (x / T) / T ≤ C := by
        apply (div_le_iff₀ hT).mpr
        exact ((le_abs_self _).trans (hCχ _)).trans
          (le_mul_of_one_le_right hC.le hT1)
      have hx2 : T ^ 2 ≤ x ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ hT.le (abs_nonneg x)).mpr (le_of_not_gt hx)
      have hmul := mul_le_mul_of_nonneg_left hdx hB.le
      nlinarith

private theorem exists_transverse_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ℝ → ℝ, ContDiff ℝ ∞ b ∧ tsupport b ⊆ Icc (-ε) ε ∧
      (∀ y, 0 ≤ b y) ∧ (∀ y, |y| < ε / 2 → b y = 1) ∧
      ∀ y, y * deriv b y ≤ 0 := by
  let t : ℝ → ℝ := fun y => 2 - (2 * y / ε) ^ 2
  let b : ℝ → ℝ := fun y => Real.smoothTransition (t y)
  have ht : ContDiff ℝ ∞ t := by dsimp [t]; fun_prop
  have hb : ContDiff ℝ ∞ b := Real.smoothTransition.contDiff.comp ht
  refine ⟨b, hb, ?_, fun y => Real.smoothTransition.nonneg (t y), ?_, ?_⟩
  · apply closure_minimal _ isClosed_Icc
    intro y hy
    by_contra hy'
    have hyε : ε < |y| := lt_of_not_ge (fun h => hy' (abs_le.mp h))
    have hy22 : 2 < (2 * y / ε) ^ 2 := by
      have hyε2 : 2 < |2 * y / ε| := by
        rw [abs_div, abs_mul, abs_of_pos hε,
          abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact (lt_div_iff₀ hε).mpr (by linarith)
      nlinarith [sq_abs (2 * y / ε)]
    exact hy (Real.smoothTransition.zero_of_nonpos (by dsimp [t]; linarith))
  · intro y hy
    apply Real.smoothTransition.one_of_one_le
    have habs : |2 * y / ε| < 1 := by
      rw [abs_div, abs_mul, abs_of_pos hε, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact (div_lt_iff₀ hε).mpr (by linarith)
    dsimp [t]
    nlinarith [sq_abs (2 * y / ε), abs_nonneg (2 * y / ε)]
  · intro y
    have hdt : HasDerivAt t (-8 * y / ε ^ 2) y := by
      convert! (hasDerivAt_const y (2 : ℝ)).sub
        ((((hasDerivAt_id y).const_mul 2).div_const ε).pow 2) using 1
      simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      field_simp
      ring
    have hst : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
    have hd := (hst.differentiable (by simp) (t y)).hasDerivAt
    have hdb : deriv b y = deriv Real.smoothTransition (t y) * (-8 * y / ε ^ 2) :=
      (hd.comp y hdt).deriv
    rw [hdb]
    have hn : 0 ≤ deriv Real.smoothTransition (t y) :=
      Real.smoothTransition.monotone.deriv_nonneg
    have heq : y * (deriv Real.smoothTransition (t y) * (-8 * y / ε ^ 2)) =
        -(8 * deriv Real.smoothTransition (t y) * y ^ 2 / ε ^ 2) := by ring
    rw [heq]
    exact neg_nonpos.mpr (by positivity)

theorem exists_regular_quadratic_suspension_of_nonpos {f u : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u) (huc : HasCompactSupport u)
    (hu0 : ∀ x, u x ≤ 0) (hreg : ∀ x, deriv f x + deriv u x ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ × ℝ → ℝ, ContDiff ℝ ∞ g ∧
      HasCompactSupport (fun p => g p - (f p.1 + p.2 ^ 2)) ∧
      tsupport (fun p => g p - (f p.1 + p.2 ^ 2)) ⊆ tsupport u ×ˢ Icc (-ε) ε ∧
      (∀ p, g p ≤ f p.1 + p.2 ^ 2) ∧
      (∀ p, ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt 𝓘(ℝ, ℝ × ℝ) g p) ∧
      ∀ x y : ℝ, |y| < ε / 2 → g (x, y) = f x + u x + y ^ 2 := by
  obtain ⟨b, hb, hbs, hb0, hbone, hdb⟩ := exists_transverse_cutoff hε
  let g : ℝ × ℝ → ℝ := fun p => f p.1 + p.2 ^ 2 + u p.1 * b p.2
  have hg : ContDiff ℝ ∞ g :=
    ((hf.comp contDiff_fst).add (contDiff_snd.pow 2)).add
      ((hu.comp contDiff_fst).mul (hb.comp contDiff_snd))
  have hs : tsupport (fun p : ℝ × ℝ => g p - (f p.1 + p.2 ^ 2)) ⊆
      tsupport u ×ˢ Icc (-ε) ε := by
    apply closure_minimal _ ((isClosed_tsupport u).prod isClosed_Icc)
    intro p hp
    constructor
    · by_contra hx
      have hz := image_eq_zero_of_notMem_tsupport hx
      exact hp (by simp [g, hz])
    · by_contra hy
      have hz := image_eq_zero_of_notMem_tsupport (fun h => hy (hbs h))
      exact hp (by simp [g, hz])
  refine ⟨g, hg, (huc.prod isCompact_Icc).of_isClosed_subset (isClosed_tsupport _) hs,
    hs, ?_, ?_, ?_⟩
  · intro p
    exact add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg (hu0 p.1) (hb0 p.2))
  · rintro ⟨x, y⟩ hc
    have hzero : fderiv ℝ g (x, y) = 0 := by
      change mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ) g (x, y) = 0 at hc
      rwa [mfderiv_eq_fderiv] at hc
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
      have hnonneg := mul_nonneg_of_nonpos_of_nonpos (hu0 x) (hdb y)
      have hz := congrArg (fun z : ℝ => y * z) hdy
      nlinarith [sq_nonneg y]
    subst y
    have hdx : deriv f x + deriv u x = 0 := by
      have hd := ((hf.differentiable (by simp) x).hasDerivAt.add_const (0 : ℝ)).add
        ((hu.differentiable (by simp) x).hasDerivAt.mul_const (b 0))
      have heq : deriv (fun z => g (z, 0)) x = deriv f x + deriv u x := by
        have hb1 : b 0 = 1 := hbone 0 (by simpa only [abs_zero] using half_pos hε)
        simpa only [g, Pi.add_apply, id_eq, zero_pow (by decide : 2 ≠ 0),
          add_zero, hb1, mul_one] using! hd.deriv
      exact heq.symm.trans hxzero
    exact hreg x hdx
  · intro x y hy
    dsimp [g]
    rw [hbone y hy]
    ring

theorem exists_cubic_cancellation_in_strip {a : ℝ} (ha : 0 < a) :
    ∃ R : ℝ, Real.sqrt a < R ∧ ∀ ε : ℝ, 0 < ε →
      ∃ g : ℝ × ℝ → ℝ, ContDiff ℝ ∞ g ∧
        HasCompactSupport (fun p => g p - (p.1 ^ 3 / 3 - a * p.1 + p.2 ^ 2)) ∧
        tsupport (fun p => g p - (p.1 ^ 3 / 3 - a * p.1 + p.2 ^ 2)) ⊆
          Icc (-R) R ×ˢ Icc (-ε) ε ∧
        (∀ p, g p ≤ p.1 ^ 3 / 3 - a * p.1 + p.2 ^ 2) ∧
        ∀ p, ¬ DifferentialGeometry.Topology.Morse.IsCriticalPointAt 𝓘(ℝ, ℝ × ℝ) g p := by
  obtain ⟨R, hR, u, hu, huc, hus, hu0, hpos⟩ := exists_nonpos_cubic_perturbation ha
  refine ⟨R, hR, fun ε hε => ?_⟩
  have hf : ContDiff ℝ ∞ (fun x : ℝ => x ^ 3 / 3 - a * x) := by fun_prop
  have hdf (x : ℝ) : deriv (fun x : ℝ => x ^ 3 / 3 - a * x) x = x ^ 2 - a := by
    have hd := (((hasDerivAt_id x).pow 3).div_const 3).sub
      ((hasDerivAt_id x).const_mul a)
    simpa only [Pi.sub_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat,
      mul_one, Nat.reduceSub, mul_div_cancel_left₀ _ (by norm_num : (3 : ℝ) ≠ 0)]
      using! hd.deriv
  obtain ⟨g, hg, hgc, hgs, hgl, hgr, _⟩ := exists_regular_quadratic_suspension_of_nonpos
    hf hu huc hu0 (fun x => by rw [hdf]; exact (hpos x).ne') hε
  exact ⟨g, hg, hgc, hgs.trans (prod_mono hus Subset.rfl), hgl, hgr⟩

end DifferentialGeometry.Morse
