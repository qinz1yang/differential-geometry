import DifferentialGeometry.Analysis.InnerProductSpace.SpectralProjectionBounds
import DifferentialGeometry.Analysis.InnerProductSpace.SpectralProjectionRegularity
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section

open Complex Metric ContinuousLinearMap Submodule
open scoped Real NNReal Topology

namespace ContourProjectionApplications

private abbrev H := EuclideanSpace ℂ (Fin 2)
private def e (i : Fin 2) : H := PiLp.single 2 i 1
private def P : Submodule ℂ H := ℂ ∙ e 0
private def S : Submodule ℂ H := ℂ ∙ (e 0 + e 1)
private def A (t : ℝ) : H →L[ℂ] H := P.starProjection + (t : ℂ) • S.starProjection
private def Q (t : ℝ) : H →L[ℂ] H :=
  (⨆ μ ∈ ball (1 : ℂ) (1 / 2), Module.End.eigenspace (A t).toLinearMap μ).starProjection

private theorem self (t : ℝ) : (A t).toLinearMap.IsSymmetric := by
  change (P.starProjection.toLinearMap + (t : ℂ) • S.starProjection.toLinearMap).IsSymmetric
  exact P.starProjection_isSymmetric.add (LinearMap.IsSymmetric.smul (by simp) S.starProjection_isSymmetric)

private theorem close (t : ℝ) : ‖A t - P.starProjection‖ ≤ |t| := by
  rw [A, add_sub_cancel_left, norm_smul]
  have hn : ‖(t : ℂ)‖ = |t| := by simp
  rw [hn]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left S.starProjection_norm_le (abs_nonneg t)

private theorem circle (t : ℝ) (ht : |t| < 1 / 4) :
    sphere (1 : ℂ) (1 / 2) ⊆ resolventSet ℂ (A t) := by
  intro z hz
  rw [Metric.mem_sphere, dist_eq_norm] at hz
  have hn := norm_sub_norm_le (1 : ℂ) z
  rw [norm_one, norm_sub_rev, hz] at hn
  have hg : (1 / 2 : ℝ) ≤ min ‖z‖ ‖z - 1‖ := le_min (by linarith) hz.ge
  apply mem_resolventSet_of_norm_sub_starProjection_lt (A t) P
  exact (close t).trans_lt (ht.trans_le (by linarith))

private theorem smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) A := by
  exact contDiff_const.add (Complex.ofRealCLM.contDiff.smul_const S.starProjection)

private theorem dimP : Module.finrank ℂ P = 1 := by
  apply finrank_span_singleton
  intro h
  have hh := congrArg (fun v : H => v 0) h
  norm_num [e] at hh

example : ContDiffOn ℝ (↑(⊤ : ℕ∞)) Q {t : ℝ | |t| < 1 / 4} :=
  smooth.contDiffOn.starProjection_eigenspace_ball (fun t _ => self t) (by norm_num) circle

example (t : ℝ) (ht : |t| < 1 / 4) :
    Module.finrank ℂ (⨆ μ ∈ ball (1 : ℂ) (1 / 2),
      Module.End.eigenspace (A t).toLinearMap μ : Submodule ℂ H) = 1 := by
  rw [finrank_eigenspace_ball_eq_of_norm_sub_starProjection_lt (A t) (self t) P
    ((close t).trans_lt ht), dimP]

example (t : ℝ) (ht : |t| ≤ 1 / 4) : ‖Q t - P.starProjection‖ ≤ 4 * |t| := by
  exact (norm_starProjection_eigenspace_ball_sub_le (A t) (self t) P ((close t).trans ht)).trans
    (mul_le_mul_of_nonneg_left (close t) (by norm_num))

example : Q 0 = P.starProjection := by
  have hh := P.iSup_eigenspace_starProjection_eq (ball (1 : ℂ) (1 / 2))
    (by norm_num [mem_ball, dist_eq_norm]) (by norm_num [mem_ball, dist_eq_norm])
  have heq : (⨆ μ ∈ ball (1 : ℂ) (1 / 2), Module.End.eigenspace (A 0).toLinearMap μ) = P := by
    simpa only [A, Complex.ofReal_zero, zero_smul, add_zero] using hh
  exact congrArg (fun U : Submodule ℂ H => U.starProjection) heq

example (t : ℝ) (ht : |t| < 1 / 4) :
    (2 * ↑Real.pi * I : ℂ)⁻¹ • (∮ z in C(1, 1 / 2), resolvent (A t) z) = Q t :=
  circleIntegral_resolvent_eq_starProjection (A t) (self t) (by norm_num) (circle t ht)

example : ContDiffOn ℝ (↑(⊤ : ℕ∞)) (fun t => ∮ z in C(1, 1 / 2), resolvent (A t) z)
    {t : ℝ | |t| < 1 / 4} := by
  apply smooth.contDiffOn.circleIntegral_resolvent
  simpa using circle

example : A (1 / 8) ≠ A 0 := by
  intro h
  have he : (1 / 8 : ℂ) • S.starProjection = 0 := by
    have hh := congrArg (fun B : H →L[ℂ] H => B - P.starProjection) h
    simpa [A] using hh
  have hS : S.starProjection = 0 := (smul_eq_zero.mp he).resolve_left (by norm_num)
  have hp : S.starProjection (e 0 + e 1) = e 0 + e 1 :=
    starProjection_eq_self_iff.mpr (mem_span_singleton_self _)
  rw [hS, zero_apply] at hp
  have hh := congrArg (fun v : H => v 0) hp
  norm_num [e] at hh

example : ‖ContinuousMap.circleIntegralCLM (E := ℂ) 1 (-1 / 2)‖ ≤ Real.pi := by
  have h := ContinuousMap.norm_circleIntegralCLM_le (E := ℂ) 1 (-1 / 2)
  norm_num at h
  nlinarith

example : (1 / 2 : ℂ) ∉ resolventSet ℂ ((1 / 2 : ℂ) • ContinuousLinearMap.id ℂ ℂ) := by
  change ¬IsUnit (algebraMap ℂ (ℂ →L[ℂ] ℂ) (1 / 2) - (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ ℂ)
  have hz : algebraMap ℂ (ℂ →L[ℂ] ℂ) (1 / 2) - (1 / 2 : ℂ) • ContinuousLinearMap.id ℂ ℂ = 0 := by
    exact sub_self _
  rw [hz]
  exact not_isUnit_zero

example : ContinuousMap.circleIntegralCLM (E := ℂ) 1 (1 / 2)
    ⟨fun z => (z : ℂ), continuous_subtype_val⟩ = 0 := by
  rw [ContinuousMap.circleIntegralCLM_apply 1 (1 / 2) (f := fun z : ℂ => z) continuousOn_id]
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    (by norm_num) Set.countable_empty continuousOn_id
  intro z _
  exact differentiableAt_id

private def D : ℝ →L[ℝ] (H →L[ℂ] H) := (ContinuousLinearMap.id ℝ ℝ).smulRight S.starProjection

private theorem derivative (t : ℝ) : HasFDerivAt A D t := by
  simpa [A, D] using! (hasFDerivAt_const P.starProjection t).add D.hasFDerivAt

private theorem normD : ‖D‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro t
  change ‖t • S.starProjection‖ ≤ 1 * ‖t‖
  rw [norm_smul, one_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left S.starProjection_norm_le (norm_nonneg t)

private theorem boundR (t : ℝ) (ht : |t| < 1 / 4) (z : ℂ)
    (hz : z ∈ sphere (1 : ℂ) (1 / 2)) : ‖resolvent (A t) z‖ ≤ (4 : ℝ≥0) := by
  rw [mem_sphere, dist_eq_norm] at hz
  have hn := norm_sub_norm_le (1 : ℂ) z
  rw [norm_one, norm_sub_rev, hz] at hn
  have hg : (1 / 2 : ℝ) ≤ min ‖z‖ ‖z - 1‖ := le_min (by linarith) hz.ge
  have hgap : (1 / 4 : ℝ) < min ‖z‖ ‖z - 1‖ := by linarith
  apply (norm_resolvent_le_of_norm_sub_starProjection_le (A t) P
    ((close t).trans ht.le) hgap).trans
  apply (div_le_iff₀ (sub_pos.mpr hgap)).mpr
  norm_num only [NNReal.coe_ofNat]
  linarith

example (t : ℝ) (ht : |t| < 1 / 4) :
    ‖fderiv ℝ (fun y => (2 * ↑Real.pi * I : ℂ)⁻¹ •
      (∮ z in C(1, 1 / 2), resolvent (A y) z)) t‖ ≤ 8 := by
  have h := (derivative t).differentiableAt.norm_fderiv_normalized_circleIntegral_resolvent_le
    1 (1 / 2) (by simpa using circle t ht) 4 (by simpa using boundR t ht)
  rw [(derivative t).fderiv] at h
  rw [show |(1 / 2 : ℝ)| * ((4 : ℝ≥0) : ℝ) ^ 2 = 8 by norm_num] at h
  nlinarith [normD]

example (t : ℝ) (ht : |t| < 1 / 4) : ‖fderiv ℝ Q t‖ ≤ 8 := by
  have h := (derivative t).differentiableAt.norm_fderiv_starProjection_eigenspace_ball_le
    (Filter.Eventually.of_forall self) (by norm_num : (0 : ℝ) ≤ 1 / 2) (circle t ht) 4 (boundR t ht)
  rw [(derivative t).fderiv] at h
  change ‖fderiv ℝ Q t‖ ≤ _ at h
  rw [show (1 / 2 : ℝ) * ((4 : ℝ≥0) : ℝ) ^ 2 = 8 by norm_num] at h
  nlinarith [normD]

example (ε t : ℝ) (hε : 0 ≤ ε) (ht : |ε * t| < 1 / 4) :
    ‖fderiv ℝ (fun y => Q (ε * y)) t‖ ≤ 8 * ε := by
  have hm : HasFDerivAt (fun y : ℝ => ε * y) (ε • ContinuousLinearMap.id ℝ ℝ) t := by
    simpa only [smul_eq_mul] using! (hasFDerivAt_id t).const_smul ε
  have hd := (derivative (ε * t)).comp t hm
  have hn : ‖D.comp (ε • ContinuousLinearMap.id ℝ ℝ)‖ ≤ ε := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    rw [norm_smul, norm_id, mul_one, Real.norm_eq_abs, abs_of_nonneg hε]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right normD hε
  have h := hd.differentiableAt.norm_fderiv_starProjection_eigenspace_ball_le
    (Filter.Eventually.of_forall (fun y => self (ε * y)))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (circle (ε * t) ht) 4 (boundR (ε * t) ht)
  rw [hd.fderiv] at h
  change ‖fderiv ℝ (fun y => Q (ε * y)) t‖ ≤ _ at h
  rw [show (1 / 2 : ℝ) * ((4 : ℝ≥0) : ℝ) ^ 2 = 8 by norm_num] at h
  nlinarith

example : IsOpen {a : ℂ | sphere (1 : ℂ) (1 / 2) ⊆ resolventSet ℂ a} := by
  simpa using isOpen_setOf_circle_subset_resolventSet (A := ℂ) 1 (1 / 2)

private theorem scaled_jets (ε t : ℝ) (hε : 0 ≤ ε) (j : ℕ) (hj : 1 ≤ j) :
    ‖iteratedFDeriv ℝ j (fun y => A (ε * y)) t‖ ≤ ε := by
  have hd (y : ℝ) : fderiv ℝ (fun z => A (ε * z)) y =
      D.comp (ε • ContinuousLinearMap.id ℝ ℝ) := by
    apply HasFDerivAt.fderiv
    apply (derivative (ε * y)).comp
    simpa only [smul_eq_mul] using! (hasFDerivAt_id y).const_smul ε
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  rw [← norm_iteratedFDeriv_fderiv, show fderiv ℝ (fun z => A (ε * z)) =
    (fun _ => D.comp (ε • ContinuousLinearMap.id ℝ ℝ)) from funext hd]
  by_cases hk : k = 0
  · subst k
    rw [norm_iteratedFDeriv_zero]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    rw [norm_smul, norm_id, mul_one, Real.norm_eq_abs, abs_of_nonneg hε]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right normD hε
  · rw [iteratedFDeriv_const_of_ne hk, Pi.zero_apply, norm_zero]
    exact hε

private theorem scaled_projection_jets (ε t : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ht : |ε * t| < 1 / 4) (n : ℕ) (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun y => Q (ε * y)) t‖ ≤
      (1 / 2 : ℝ) * ε * resolventDerivativeBound 4 1 n := by
  have hU : IsOpen {y : ℝ | |ε * y| < 1 / 4} := isOpen_lt (by fun_prop) continuous_const
  have hf : ContDiffOn ℝ n (fun y => A (ε * y)) {y : ℝ | |ε * y| < 1 / 4} :=
    ((smooth.of_le (by simp)).comp (contDiff_const.mul contDiff_id)).contDiffOn
  have h := hf.norm_iteratedFDeriv_starProjection_eigenspace_ball_le hU
    (fun y _ => self (ε * y)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (fun y hy => circle (ε * y) hy) ht hε hε1 (by norm_num : (0 : ℝ) ≤ 1) 4 1
    (boundR (ε * t) ht) (fun j hj _ => by simpa using scaled_jets ε t hε j hj) n hn le_rfl
  simpa only [Q, one_pow, mul_one] using h

example (ε t : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : |ε * t| < 1 / 4) :
    ‖iteratedFDeriv ℝ 2 (fun y => Q (ε * y)) t‖ ≤ 384 * ε := by
  have h := scaled_projection_jets ε t hε hε1 ht 2 (by norm_num)
  have hc : (resolventDerivativeBound 4 1 2 : ℝ) = 768 := by
    norm_num [resolventDerivativeBound]
  rw [hc] at h
  linarith

example (ε t : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : |ε * t| < 1 / 4)
    (n : ℕ) (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun y => Q (ε * y)) t‖ ≤
      (1 / 2 : ℝ) * ε * resolventDerivativeBound 4 1 n :=
  scaled_projection_jets ε t hε hε1 ht n hn

example (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    iteratedFDeriv ℝ n (fun y => Q ((0 : ℝ) * y)) t = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [mul_zero, zero_mul] using
    scaled_projection_jets 0 t (by norm_num) (by norm_num) (by norm_num) n hn

example (K B : ℝ≥0) (m n : ℕ) (hmn : m ≤ n) :
    resolventDerivativeBound K B m ≤ resolventDerivativeBound K B n :=
  resolventDerivativeBound_mono K B hmn

example : resolventDerivativeBound 1 1 3 = 81 := by
  norm_num [resolventDerivativeBound]

end ContourProjectionApplications

