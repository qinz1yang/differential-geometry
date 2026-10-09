/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.VisualMetric

noncomputable section

open Filter

namespace DifferentialGeometry.BoundaryDistortion

open Hyperbolic HyperbolicFaithful HyperbolicBoundary BoundaryTopology AsymptoticRays
open GromovBoundary MorseDivergence BoundaryExtension BoundaryHomeomorph
open PseudoIsometry BoundaryVisual

variable {n : ℕ}

def upperConst (K C : ℝ) : ℝ :=
  4 * Real.exp (2 * (C + morseDist K C + Real.log 2)) * (2 : ℝ) ^ K⁻¹

theorem upperConst_pos (K C : ℝ) : 0 < upperConst K C := by
  unfold upperConst
  positivity

theorem interiorRatio_image_le {K C : ℝ} {Φ : HUpper n → HUpper n}
    (hΦ : IsPseudoIsometry K C Φ) (hn : 1 ≤ n) (o x y : HUpper n) :
    interiorRatio (Φ o) (Φ x) (Φ y) ≤ upperConst K C * (interiorRatio o x y) ^ K⁻¹ := by
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hΦ.hK
  have hα : 0 ≤ K⁻¹ := (inv_pos.mpr hK).le
  let D := C + morseDist K C + Real.log 2
  have hgp := gromovProduct_image_ge hΦ hn o x y
  have hexp : Real.exp (-(2 * gromovProduct (Φ o) (Φ x) (Φ y))) ≤
      Real.exp (2 * D) * (Real.exp (-(2 * gromovProduct o x y))) ^ K⁻¹ := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by dsimp [D]; linarith)
  have hsrc : Real.exp (-(2 * gromovProduct o x y)) ≤ 2 * interiorRatio o x y := by
    have := half_exp_le_interiorRatio hn o x y
    linarith
  calc interiorRatio (Φ o) (Φ x) (Φ y)
      ≤ 4 * Real.exp (-(2 * gromovProduct (Φ o) (Φ x) (Φ y))) :=
        interiorRatio_le hn _ _ _
    _ ≤ 4 * (Real.exp (2 * D) * (Real.exp (-(2 * gromovProduct o x y))) ^ K⁻¹) :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ ≤ 4 * (Real.exp (2 * D) * (2 * interiorRatio o x y) ^ K⁻¹) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Real.exp_pos _).le hsrc hα)
          (Real.exp_pos _).le) (by norm_num)
    _ = upperConst K C * (interiorRatio o x y) ^ K⁻¹ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (interiorRatio_nonneg o x y)]
      unfold upperConst D
      ring

theorem ratio_bExt_le {K C : ℝ} {Φ : HUpper n → HUpper n}
    (hΦ : IsPseudoIsometry K C Φ) (hn : 1 ≤ n) (o : HUpper n) (a b : BoundaryH n) :
    ratio (Φ o) (bExt (gromovCauchy_image_ray hΦ hn) a)
        (bExt (gromovCauchy_image_ray hΦ hn) b) ≤
      upperConst K C * (ratio o a b) ^ K⁻¹ := by
  have hα : 0 ≤ K⁻¹ := (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hΦ.hK)).le
  have hsrc := tendsto_interiorRatio o (tendsto_rayTo basepointH a) (tendsto_rayTo basepointH b)
  have htgt := tendsto_interiorRatio (Φ o)
    (bExt_spec (gromovCauchy_image_ray hΦ hn) a)
    (bExt_spec (gromovCauchy_image_ray hΦ hn) b)
  have hrpow := (Real.continuousAt_rpow_const (ratio o a b) K⁻¹ (Or.inr hα)).tendsto.comp hsrc
  exact le_of_tendsto_of_tendsto htgt (hrpow.const_mul (upperConst K C))
    (Eventually.of_forall fun k => interiorRatio_image_le hΦ hn o _ _)

def reverseConst (K C E : ℝ) : ℝ := (Real.exp (2 * E) * upperConst K C) ^ K

theorem reverseConst_pos (K C E : ℝ) : 0 < reverseConst K C E :=
  Real.rpow_pos_of_pos (mul_pos (Real.exp_pos _) (upperConst_pos K C)) K

theorem ratio_pow_le_bExtHomeomorph {K C K' C' E E' : ℝ} {Φ Ψ : HUpper n → HUpper n}
    (hΦ : IsPseudoIsometry K C Φ) (hΨ : IsPseudoIsometry K' C' Ψ)
    (hleft : ∀ x, dist (Ψ (Φ x)) x ≤ E) (hright : ∀ y, dist (Φ (Ψ y)) y ≤ E')
    (hn : 1 ≤ n) (o : HUpper n) (a b : BoundaryH n) :
    (ratio o a b) ^ K' ≤ reverseConst K' C' E *
      ratio (Φ o) (bExtHomeomorph hΦ hΨ hleft hright hn a)
        (bExtHomeomorph hΦ hΨ hleft hright hn b) := by
  let φ := bExtHomeomorph hΦ hΨ hleft hright hn
  have hi (c : BoundaryH n) : bExt (gromovCauchy_image_ray hΨ hn) (φ c) = c :=
    φ.symm_apply_apply c
  have hΨb := ratio_bExt_le hΨ hn (Φ o) (φ a) (φ b)
  rw [hi a, hi b] at hΨb
  have hdist : dist o (Ψ (Φ o)) ≤ E := by rw [dist_comm]; exact hleft o
  have hmove : ratio o a b ≤ Real.exp (2 * E) * ratio (Ψ (Φ o)) a b :=
    (ratio_change_basepoint o (Ψ (Φ o)) a b).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (ratio_nonneg _ _ _))
  have htotal : ratio o a b ≤ (Real.exp (2 * E) * upperConst K' C') *
      (ratio (Φ o) (φ a) (φ b)) ^ K'⁻¹ := by
    calc ratio o a b ≤ Real.exp (2 * E) * ratio (Ψ (Φ o)) a b := hmove
      _ ≤ Real.exp (2 * E) * (upperConst K' C' * (ratio (Φ o) (φ a) (φ b)) ^ K'⁻¹) :=
        mul_le_mul_of_nonneg_left hΨb (Real.exp_pos _).le
      _ = _ := by ring
  have hK' : 0 < K' := lt_of_lt_of_le zero_lt_one hΨ.hK
  have hp := Real.rpow_le_rpow (ratio_nonneg o a b) htotal hK'.le
  rw [Real.mul_rpow (mul_pos (Real.exp_pos _) (upperConst_pos K' C')).le
      (Real.rpow_nonneg (ratio_nonneg _ _ _) _),
    ← Real.rpow_mul (ratio_nonneg _ _ _), inv_mul_cancel₀ hK'.ne', Real.rpow_one] at hp
  exact hp

def distortion (D α β t : ℝ) : ℝ := D * t ^ α * (2 + t) ^ β

theorem distortion_nonneg {D α β t : ℝ} (hD : 0 ≤ D) (ht : 0 ≤ t) :
    0 ≤ distortion D α β t := by
  unfold distortion
  exact mul_nonneg (mul_nonneg hD (Real.rpow_nonneg ht _))
    (Real.rpow_nonneg (by linarith) _)

theorem distortion_zero (D β : ℝ) {α : ℝ} (hα : 0 < α) : distortion D α β 0 = 0 := by
  simp [distortion, Real.zero_rpow hα.ne']

theorem continuousAt_distortion_zero (D β : ℝ) {α : ℝ} (hα : 0 < α) :
    ContinuousAt (distortion D α β) 0 := by
  apply ContinuousAt.mul
  · exact continuousAt_const.mul (Real.continuousAt_rpow_const 0 α (Or.inr hα.le))
  · have hbase : Tendsto (fun t : ℝ => 2 + t) (nhds 0) (nhds 2) := by
      simpa only [add_zero, id_eq] using
        (tendsto_const_nhds.add (tendsto_id : Tendsto (id : ℝ → ℝ) (nhds 0) (nhds 0)))
    simpa only [ContinuousAt, Function.comp_def, add_zero] using
      (Real.continuousAt_rpow_const 2 β (Or.inl (by norm_num))).tendsto.comp hbase

theorem tendsto_distortion_zero (D β : ℝ) {α : ℝ} (hα : 0 < α) :
    Tendsto (distortion D α β) (nhds 0) (nhds 0) := by
  simpa only [distortion_zero D β hα] using (continuousAt_distortion_zero D β hα).tendsto

theorem strictMonoOn_distortion {D α β : ℝ} (hD : 0 < D) (hα : 0 < α) (hβ : 0 ≤ β) :
    StrictMonoOn (distortion D α β) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hx2 : 0 < 2 + x := by linarith
  have hp := Real.rpow_lt_rpow hx0 hxy hα
  have hp₂ := Real.rpow_le_rpow hx2.le (by linarith : 2 + x ≤ 2 + y) hβ
  calc distortion D α β x = D * x ^ α * (2 + x) ^ β := rfl
    _ < D * y ^ α * (2 + x) ^ β :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hp hD) (Real.rpow_pos_of_pos hx2 β)
    _ ≤ D * y ^ α * (2 + y) ^ β :=
      mul_le_mul_of_nonneg_left hp₂ (mul_nonneg hD.le (Real.rpow_nonneg hy0 α))
    _ = distortion D α β y := rfl

theorem continuousOn_distortion (D β : ℝ) {α : ℝ} (hα : 0 < α) :
    ContinuousOn (distortion D α β) (Set.Ici 0) := by
  intro t ht
  have hbase : ContinuousAt (fun s : ℝ => 2 + s) t := continuousAt_const.add continuousAt_id
  have h₂ := hbase.rpow_const (p := β) (Or.inl (by have : 0 ≤ t := ht; linarith))
  exact ((continuousAt_const.mul (Real.continuousAt_rpow_const t α (Or.inr hα.le))).mul
    h₂).continuousWithinAt

theorem tendsto_distortion_atTop {D α β : ℝ} (hD : 0 < D) (hα : 0 < α) (hβ : 0 ≤ β) :
    Tendsto (distortion D α β) atTop atTop := by
  have hbase : Tendsto (fun t : ℝ => D * t ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).const_mul_atTop hD
  apply tendsto_atTop_mono' atTop ?_ hbase
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact le_mul_of_one_le_right (mul_nonneg hD.le (Real.rpow_nonneg ht α))
    (Real.one_le_rpow (by linarith : 1 ≤ 2 + t) hβ)

theorem crossRatioSq_le_of_visual_bounds (hn : 1 ≤ n)
    {Φ : HUpper n → HUpper n} {φ : BoundaryH n → BoundaryH n}
    {A B α β : ℝ} (hA : 0 < A) (hB : 0 < B) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hi : Function.Injective φ)
    (hupper : ∀ o a b, ratio (Φ o) (φ a) (φ b) ≤ A * (ratio o a b) ^ α)
    (hlower : ∀ o a b, (ratio o a b) ^ β ≤ B * ratio (Φ o) (φ a) (φ b))
    (a b c d : BoundaryH n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hbd : b ≠ d) :
    crossRatioSq (φ a) (φ b) (φ c) (φ d) ≤
      distortion (2 * A * B ^ 2) α β (crossRatioSq a b c d) := by
  obtain ⟨o, hoab, hoac, hobc⟩ := exists_triple_center a b c hab hac hbc
  let t := crossRatioSq a b c d
  let s := ratio o b d
  have ht : 0 ≤ t := crossRatioSq_nonneg a b c d
  have hs : 0 < s := ratio_pos o hbd
  have hts : t * s = 2 * ratio o c d := by
    dsimp [t, s]
    rw [crossRatioSq_eq_ratio o a b c d hac hbd, hoab, hoac, one_mul]
    exact div_mul_cancel₀ _ hs.ne'
  have hcd : ratio o c d ≤ t := by
    have hs2 : s ≤ 2 := ratio_le_two hn o b d
    have := mul_le_mul_of_nonneg_left hs2 ht
    linarith
  have hone : 1 ≤ (2 + t) * s := by
    have htri := ratio_triangle hn o b d c
    rw [hobc, ratio_comm o d c] at htri
    change 1 ≤ 2 * (s + ratio o c d) at htri
    nlinarith
  have hac' : φ a ≠ φ c := fun h => hac (hi h)
  have hbd' : φ b ≠ φ d := fun h => hbd (hi h)
  let p := ratio (Φ o) (φ a) (φ c)
  let q := ratio (Φ o) (φ b) (φ d)
  have hp : 0 < p := ratio_pos (Φ o) hac'
  have hq : 0 < q := ratio_pos (Φ o) hbd'
  have hden₁ : 1 ≤ B * p := by
    have h := hlower o a c
    rw [hoac, Real.one_rpow] at h
    exact h
  have hpow : 1 ≤ (2 + t) ^ β * s ^ β := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hone hβ
    rwa [Real.one_rpow, Real.mul_rpow (by linarith : 0 ≤ 2 + t) hs.le] at h
  have hden₂ : 1 ≤ B * (2 + t) ^ β * q := by
    calc 1 ≤ (2 + t) ^ β * s ^ β := hpow
      _ ≤ (2 + t) ^ β * (B * q) :=
        mul_le_mul_of_nonneg_left (hlower o b d) (Real.rpow_nonneg (by linarith) _)
      _ = _ := by ring
  have hden : 1 ≤ B ^ 2 * (2 + t) ^ β * (p * q) := by
    calc 1 = (1 : ℝ) * 1 := by ring
      _ ≤ (B * p) * (B * (2 + t) ^ β * q) :=
        mul_le_mul hden₁ hden₂ (by norm_num) (mul_pos hB hp).le
      _ = _ := by ring
  have hcd' : ratio (Φ o) (φ c) (φ d) ≤ A * t ^ α :=
    (hupper o c d).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (ratio_nonneg o c d) hcd hα) hA.le)
  have hnum : ratio (Φ o) (φ a) (φ b) * ratio (Φ o) (φ c) (φ d) ≤ 2 * A * t ^ α := by
    calc ratio (Φ o) (φ a) (φ b) * ratio (Φ o) (φ c) (φ d) ≤ 2 * (A * t ^ α) :=
        mul_le_mul (ratio_le_two hn _ _ _) hcd' (ratio_nonneg _ _ _) (by norm_num)
      _ = _ := by ring
  rw [crossRatioSq_eq_ratio (Φ o) (φ a) (φ b) (φ c) (φ d) hac' hbd']
  apply (div_le_iff₀ (mul_pos hp hq)).mpr
  calc ratio (Φ o) (φ a) (φ b) * ratio (Φ o) (φ c) (φ d) ≤ 2 * A * t ^ α := hnum
    _ ≤ (2 * A * t ^ α) * (B ^ 2 * (2 + t) ^ β * (p * q)) := by
      have hh := mul_le_mul_of_nonneg_left hden
        (mul_nonneg (by linarith : 0 ≤ 2 * A) (Real.rpow_nonneg ht α))
      simpa only [mul_one] using hh
    _ = _ := by unfold distortion t p q; ring

def HasCrossRatioControl (φ : BoundaryH n → BoundaryH n) : Prop :=
  ∃ D α β : ℝ, 0 < D ∧ 0 < α ∧ 0 ≤ β ∧
    ∀ a b c d : BoundaryH n, a ≠ b → a ≠ c → b ≠ c → b ≠ d →
      crossRatioSq (φ a) (φ b) (φ c) (φ d) ≤
        distortion D α β (crossRatioSq a b c d)

theorem bExtHomeomorph_hasCrossRatioControl {K C K' C' E E' : ℝ}
    {Φ Ψ : HUpper n → HUpper n}
    (hΦ : IsPseudoIsometry K C Φ) (hΨ : IsPseudoIsometry K' C' Ψ)
    (hleft : ∀ x, dist (Ψ (Φ x)) x ≤ E) (hright : ∀ y, dist (Φ (Ψ y)) y ≤ E')
    (hn : 1 ≤ n) :
    HasCrossRatioControl (bExtHomeomorph hΦ hΨ hleft hright hn) := by
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hΦ.hK
  have hK' : 0 < K' := lt_of_lt_of_le zero_lt_one hΨ.hK
  refine ⟨2 * upperConst K C * reverseConst K' C' E ^ 2, K⁻¹, K',
    mul_pos (mul_pos (by norm_num) (upperConst_pos K C))
      (sq_pos_of_pos (reverseConst_pos K' C' E)), inv_pos.mpr hK, hK'.le, ?_⟩
  exact crossRatioSq_le_of_visual_bounds hn (upperConst_pos K C) (reverseConst_pos K' C' E)
    (inv_pos.mpr hK).le hK'.le (bExtHomeomorph hΦ hΨ hleft hright hn).injective
    (ratio_bExt_le hΦ hn) (ratio_pow_le_bExtHomeomorph hΦ hΨ hleft hright hn)

theorem bExtHomeomorph_symm_hasCrossRatioControl {K C K' C' E E' : ℝ}
    {Φ Ψ : HUpper n → HUpper n}
    (hΦ : IsPseudoIsometry K C Φ) (hΨ : IsPseudoIsometry K' C' Ψ)
    (hleft : ∀ x, dist (Ψ (Φ x)) x ≤ E) (hright : ∀ y, dist (Φ (Ψ y)) y ≤ E')
    (hn : 1 ≤ n) :
    HasCrossRatioControl (bExtHomeomorph hΦ hΨ hleft hright hn).symm :=
  bExtHomeomorph_hasCrossRatioControl hΨ hΦ hright hleft hn

theorem HasCrossRatioControl.small_crossRatios {φ : BoundaryH n → BoundaryH n}
    (hφ : HasCrossRatioControl φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b c d : BoundaryH n,
      a ≠ b → a ≠ c → b ≠ c → b ≠ d → crossRatioSq a b c d < δ →
        crossRatioSq (φ a) (φ b) (φ c) (φ d) < ε := by
  obtain ⟨D, α, β, _, hα, _, hbound⟩ := hφ
  have he := (tendsto_distortion_zero D β hα).eventually (Iio_mem_nhds hε)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ, hδ, fun a b c d hab hac hbc hbd hsmall => ?_⟩
  apply lt_of_le_of_lt (hbound a b c d hab hac hbc hbd)
  apply hball
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero,
    abs_of_nonneg (crossRatioSq_nonneg a b c d)] using hsmall

end DifferentialGeometry.BoundaryDistortion
