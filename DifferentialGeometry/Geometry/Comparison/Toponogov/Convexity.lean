/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow, OpenAI
-/
import Mathlib.Analysis.Convex.Deriv

open Filter Set Topology

namespace DifferentialGeometry.Toponogov

structure LowerSupportAt (f : ℝ → ℝ) (I : Set ℝ) (x : ℝ) where

  support : ℝ → ℝ

  supportDeriv : ℝ → ℝ

  supportSecondDeriv : ℝ

  domain : Set ℝ
  domain_mem_nhds : domain ∈ 𝓝 x
  domain_subset : domain ⊆ I
  support_le : ∀ y ∈ domain, support y ≤ f y
  support_eq : support x = f x
  hasDerivAt_support : ∀ y ∈ domain, HasDerivAt support (supportDeriv y) y
  hasDerivAt_supportDeriv : HasDerivAt supportDeriv supportSecondDeriv x
  supportSecondDeriv_nonneg : 0 ≤ supportSecondDeriv

private lemma secondDeriv_nonpos_of_isLocalMax
    {φ φ' : ℝ → ℝ} {x d : ℝ} {U : Set ℝ} (hmax : IsLocalMax φ x)
    (hU : U ∈ 𝓝 x) (hφ : ∀ y ∈ U, HasDerivAt φ (φ' y) y)
    (hφ' : HasDerivAt φ' d x) : d ≤ 0 := by
  by_contra hd
  have hd_pos : 0 < d := lt_of_not_ge hd
  have hxU : x ∈ U := mem_of_mem_nhds hU
  have hφ'x : φ' x = 0 := hmax.hasDerivAt_eq_zero (hφ x hxU)
  have hslope : ∀ᶠ y in 𝓝[≠] x, 0 < slope φ' x y :=
    hφ'.tendsto_slope.eventually (eventually_gt_nhds hd_pos)
  have hφ'_pos : ∀ᶠ y in 𝓝[>] x, 0 < φ' y := by
    filter_upwards [hslope.filter_mono (nhdsWithin_mono x (by
        intro y hy
        simpa only [mem_compl_iff, mem_singleton_iff] using hy.ne')),
      self_mem_nhdsWithin] with y hy hxy
    rw [slope_def_field, hφ'x, sub_zero, div_pos_iff] at hy
    rcases hy with hy | hy
    · exact hy.1
    · exfalso
      have hxy' : x < y := hxy
      linarith
  have hgood : ∀ᶠ y in 𝓝[>] x, y ∈ U ∧ φ y ≤ φ x ∧ 0 < φ' y := by
    filter_upwards [(show ∀ᶠ y in 𝓝 x, y ∈ U from hU).filter_mono nhdsWithin_le_nhds,
      hmax.filter_mono nhdsWithin_le_nhds, hφ'_pos] with y hyU hymax hypos
    exact ⟨hyU, hymax, hypos⟩
  obtain ⟨b, hxb, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hgood
  obtain ⟨c, hxc, hcb⟩ := exists_between (show x < b from hxb)
  have hcgood := hb ⟨hxc, hcb⟩
  have hIccU : Icc x c ⊆ U := by
    intro y hy
    rcases hy.1.eq_or_lt with rfl | hxy
    · exact hxU
    · exact (hb ⟨hxy, hy.2.trans_lt hcb⟩).1
  have hcont : ContinuousOn φ (Icc x c) := fun y hy =>
    (hφ y (hIccU hy)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ φ (Ioo x c) := fun y hy =>
    (hφ y (hIccU ⟨hy.1.le, hy.2.le⟩)).differentiableAt.differentiableWithinAt
  obtain ⟨y, hy, hyderiv⟩ := exists_deriv_eq_slope φ hxc hcont hdiff
  have hygood := hb ⟨hy.1, hy.2.trans hcb⟩
  have hypos : 0 < deriv φ y := by
    rw [(hφ y hygood.1).deriv]
    exact hygood.2.2
  have hslope_pos : 0 < (φ c - φ x) / (c - x) := hyderiv ▸ hypos
  have hφxc : φ x < φ c := by
    rcases div_pos_iff.mp hslope_pos with hslope | hslope
    · exact sub_pos.mp hslope.1
    · exfalso
      linarith
  exact (not_lt_of_ge hcgood.2.1) hφxc

theorem convexOn_of_lowerSupport {I : Set ℝ} {f : ℝ → ℝ} (hI : Convex ℝ I)
    (hf : ContinuousOn f I)
    (hsupport : ∀ x ∈ interior I, LowerSupportAt f I x) : ConvexOn ℝ I f := by
  refine convexOn_of_slope_mono_adjacent hI ?_
  intro x y z hx hz hxy hyz
  by_contra hslopes
  have hslopes_gt : (f z - f y) / (z - y) < (f y - f x) / (y - x) :=
    lt_of_not_ge hslopes
  have hxz : x < z := hxy.trans hyz
  have hxz_ne : z - x ≠ 0 := sub_ne_zero.mpr hxz.ne'
  let m : ℝ := (f z - f x) / (z - x)
  let line : ℝ → ℝ := fun s => f x + (s - x) * m
  have hline_x : line x = f x := by simp [line]
  have hline_z : line z = f z := by
    dsimp [line, m]
    field_simp [hxz_ne]
    ring
  have hgap : 0 < f y - line y := by
    have hcross_lt : (f z - f y) * (y - x) < (f y - f x) * (z - y) :=
      (div_lt_div_iff₀ (sub_pos.mpr hyz) (sub_pos.mpr hxy)).mp hslopes_gt
    have hcross : 0 < (z - y) * (f y - f x) - (y - x) * (f z - f y) := by
      rw [sub_pos]
      simpa [mul_comm] using hcross_lt
    have hnum : 0 < (f y - f x) * (z - x) - (y - x) * (f z - f x) := by
      convert hcross using 1
      ring
    dsimp [line, m]
    have hterm :
      (y - x) * ((f z - f x) / (z - x)) =
          ((y - x) * (f z - f x)) / (z - x) := by ring
    rw [hterm]
    have hquotient : ((y - x) * (f z - f x)) / (z - x) < f y - f x :=
      (div_lt_iff₀ (sub_pos.mpr hxz)).2 (by linarith)
    linarith
  have hbump : 0 < (y - x) * (z - y) := mul_pos (sub_pos.mpr hxy) (sub_pos.mpr hyz)
  let η : ℝ := (f y - line y) / (2 * ((y - x) * (z - y)))
  have hη : 0 < η := by
    exact div_pos hgap (mul_pos (by norm_num) hbump)
  let bump : ℝ → ℝ := fun s => (s - x) * (z - s)
  let g : ℝ → ℝ := fun s => f s - line s - η * bump s
  have hg_y : 0 < g y := by
    dsimp [g, bump, η]
    have heq :
        f y - line y - (f y - line y) / (2 * ((y - x) * (z - y))) *
            ((y - x) * (z - y)) = (f y - line y) / 2 := by
      field_simp [hbump.ne']
      ring
    rw [heq]
    exact div_pos hgap (by norm_num)
  have hg_x : g x = 0 := by simp [g, bump, hline_x]
  have hg_z : g z = 0 := by simp [g, bump, hline_z]
  have hxzI : Icc x z ⊆ I := hI.ordConnected.out hx hz
  have hline_cont : Continuous line := by fun_prop
  have hbump_cont : Continuous bump := by fun_prop
  have hg_cont : ContinuousOn g (Icc x z) :=
    ((hf.mono hxzI).sub hline_cont.continuousOn).sub
      (continuous_const.mul hbump_cont).continuousOn
  obtain ⟨r, hr, hrmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨y, hxy.le, hyz.le⟩ hg_cont
  have hg_r : 0 < g r := hg_y.trans_le (hrmax ⟨hxy.le, hyz.le⟩)
  have hr_ne_x : r ≠ x := by
    intro hrx
    rw [hrx, hg_x] at hg_r
    exact hg_r.false
  have hr_ne_z : r ≠ z := by
    intro hrz
    rw [hrz, hg_z] at hg_r
    exact hg_r.false
  have hxr : x < r := lt_of_le_of_ne hr.1 hr_ne_x.symm
  have hrz : r < z := lt_of_le_of_ne hr.2 hr_ne_z
  have hIoo_interior : Ioo x z ⊆ interior I :=
    subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxzI⟩
  let S := hsupport r (hIoo_interior ⟨hxr, hrz⟩)
  have hg_localMax : IsLocalMax g r :=
    hrmax.isLocalMax (mem_of_superset (Ioo_mem_nhds hxr hrz) Ioo_subset_Icc_self)
  let k : ℝ → ℝ := fun s => S.support s - line s - η * bump s
  have hk_le_g : k ≤ᶠ[𝓝 r] g := by
    filter_upwards [(show ∀ᶠ s in 𝓝 r, s ∈ S.domain from S.domain_mem_nhds)] with s hs
    dsimp [k, g]
    linarith [S.support_le s hs]
  have hgk_r : g r = k r := by simp only [g, k, S.support_eq]
  have hk_localMax : IsLocalMax k r := hk_le_g.isLocalMax hgk_r hg_localMax
  let k' : ℝ → ℝ := fun s =>
    S.supportDeriv s - m - η * ((z - s) - (s - x))
  have hline_deriv (s : ℝ) : HasDerivAt line m s := by
    dsimp [line]
    convert (hasDerivAt_const s (f x)).add
      (((hasDerivAt_id s).sub_const x).mul_const m) using 1
    · rfl
    · rfl
    · funext t
      simp
    · ring
  have hbump_deriv (s : ℝ) : HasDerivAt bump ((z - s) - (s - x)) s := by
    dsimp [bump]
    convert ((hasDerivAt_id s).sub_const x).mul
      ((hasDerivAt_const s z).sub (hasDerivAt_id s)) using 1
    · rfl
    · rfl
    · funext t
      simp
    · simp
      ring
  have hk_deriv (s : ℝ) (hs : s ∈ S.domain) : HasDerivAt k (k' s) s := by
    dsimp [k, k']
    convert ((S.hasDerivAt_support s hs).sub (hline_deriv s)).sub
      ((hbump_deriv s).const_mul η) using 1
    · rfl
    · rfl
    · funext t
      simp
  have hlinear_deriv : HasDerivAt (fun s : ℝ => (z - s) - (s - x)) (-2) r := by
    convert ((hasDerivAt_const r z).sub (hasDerivAt_id r)).sub
      ((hasDerivAt_id r).sub_const x) using 1
    · rfl
    · rfl
    · funext t
      simp
    · ring
  have hk'_deriv : HasDerivAt k' (S.supportSecondDeriv + 2 * η) r := by
    dsimp [k']
    convert (S.hasDerivAt_supportDeriv.sub_const m).sub
      (hlinear_deriv.const_mul η) using 1
    · rfl
    · rfl
    · funext t
      simp
    · ring
  have hk''_nonpos : S.supportSecondDeriv + 2 * η ≤ 0 :=
    secondDeriv_nonpos_of_isLocalMax hk_localMax S.domain_mem_nhds hk_deriv hk'_deriv
  linarith [S.supportSecondDeriv_nonneg, hη]

theorem convex_div_mono_of_zero {T s₁ s₂ : ℝ} {f : ℝ → ℝ} (hT : 0 < T)
    (hf : ConvexOn ℝ (Icc 0 T) f) (hf_zero : f 0 = 0)
    (hs₁ : 0 < s₁) (hs₁₂ : s₁ ≤ s₂) (hs₂T : s₂ ≤ T) :
    f s₁ / s₁ ≤ f s₂ / s₂ := by
  have hs₂ : 0 < s₂ := hs₁.trans_le hs₁₂
  have h := hf.secant_mono (by simp [hT.le]) ⟨hs₁.le, hs₁₂.trans hs₂T⟩
    ⟨hs₂.le, hs₂T⟩ hs₁.ne' hs₂.ne' hs₁₂
  simpa [hf_zero] using h

theorem convex_endpoint_ge_of_lower_support {T ε d : ℝ} {f ψ : ℝ → ℝ}
    (hT : 0 < T) (hε : 0 < ε) (hεT : ε ≤ T) (hf : ConvexOn ℝ (Icc 0 T) f)
    (hψ_le : ∀ r ∈ Ico 0 ε, ψ r ≤ f r) (hψ_zero : ψ 0 = f 0)
    (hψ_deriv : HasDerivWithinAt ψ d (Ioi 0) 0) :
    f 0 + T * d ≤ f T := by
  have hd_slope : d ≤ slope f 0 T := by
    apply le_of_tendsto
      ((hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hψ_deriv)
    filter_upwards [Ioo_mem_nhdsGT hε] with r hr
    have hrT : r ≤ T := hr.2.le.trans hεT
    have hsecant : slope f 0 r ≤ slope f 0 T :=
      by simpa only [slope_def_field, sub_zero] using
        hf.secant_mono (by simp [hT.le]) ⟨hr.1.le, hrT⟩ (by simp [hT.le])
          hr.1.ne' hT.ne' hrT
    have hsupport : slope ψ 0 r ≤ slope f 0 r := by
      rw [slope_def_field, slope_def_field, hψ_zero]
      exact div_le_div_of_nonneg_right (sub_le_sub_right (hψ_le r ⟨hr.1.le, hr.2⟩) _)
        (sub_nonneg.mpr hr.1.le)
    exact hsupport.trans hsecant
  rw [slope_def_field, sub_zero] at hd_slope
  have := (le_div_iff₀ hT).mp hd_slope
  linarith

end DifferentialGeometry.Toponogov
