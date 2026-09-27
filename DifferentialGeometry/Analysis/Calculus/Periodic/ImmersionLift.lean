import DifferentialGeometry.Analysis.Calculus.Inverse.SmoothLocalInverse
import DifferentialGeometry.Analysis.Calculus.Periodic.Affine
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Periodic

section

noncomputable section

open Set Filter Function
open scoped ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis

private theorem locallyLipschitz_lift_of_immersion
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {Γ : ℝ → F} (hΓ : ContDiff ℝ ∞ Γ)
    (himm : ∀ t, Function.Injective (fderiv ℝ Γ t))
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) {K : ℝ≥0} (hcomp : LipschitzWith K (Γ ∘ ψ)) :
    LocallyLipschitz ψ := by
  intro x
  obtain ⟨r, U, V, hU, hxU, hV, hxV, _, hr, hleft, _⟩ :=
    exists_smooth_local_leftInverse isOpen_univ hΓ.contDiffOn (mem_univ (ψ x)) (himm (ψ x))
  have hrx : ContDiffAt ℝ 1 r (Γ (ψ x)) :=
    (hr.of_le (by norm_cast)).contDiffAt (hU.mem_nhds hxU)
  obtain ⟨C, s, hs, hCs⟩ := hrx.exists_lipschitzOnWith
  let T := ψ ⁻¹' V ∩ (Γ ∘ ψ) ⁻¹' s
  have hT : T ∈ 𝓝 x :=
    inter_mem (hψ.continuousAt.preimage_mem_nhds (hV.mem_nhds hxV))
      (hcomp.continuous.continuousAt.preimage_mem_nhds hs)
  refine ⟨C * K, T, hT, ?_⟩
  intro y hy z hz
  rw [← hleft (ψ y) hy.1, ← hleft (ψ z) hz.1]
  exact (hCs hy.2 hz.2).trans (by
    simpa only [ENNReal.coe_mul, mul_assoc] using
      mul_le_mul' (le_refl (C : ℝ≥0∞)) (hcomp y z))

private theorem exists_lipschitzWith_of_locallyLipschitz_affinePeriodic
    {ψ : ℝ → ℝ} (hψ : LocallyLipschitz ψ)
    (hperiod : ∀ t, ψ (t + 1) = ψ t + 1) : ∃ C : ℝ≥0, LipschitzWith C ψ := by
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 2)) hψ.locallyLipschitzOn
  let d : ℝ → ℝ := fun t => ψ t - t
  have hd : Function.Periodic d 1 := affinePeriodic_sub_id hperiod
  obtain ⟨B, hB, hbound⟩ := exists_bound_of_continuous_unit_periodic
    (hψ.continuous.sub continuous_id) hd
  have hshift (t : ℝ) (n : ℤ) : ψ (t - (n : ℝ)) = ψ t - n := by
    have hh := hd.sub_int_mul_eq (x := t) n
    change ψ (t - (n : ℝ) * 1) - (t - (n : ℝ) * 1) = ψ t - t at hh
    simp only [mul_one] at hh
    linarith
  let C : ℝ≥0 := ⟨max (K : ℝ) (1 + 2 * B), le_trans K.coe_nonneg (le_max_left _ _)⟩
  refine ⟨C, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  change dist (ψ x) (ψ y) ≤ max (K : ℝ) (1 + 2 * B) * dist x y
  by_cases hnear : dist x y ≤ 1
  · let n := Int.floor y
    have hny : (n : ℝ) ≤ y := Int.floor_le y
    have hyn : y < (n : ℝ) + 1 := Int.lt_floor_add_one y
    have hxy : -1 ≤ x - y ∧ x - y ≤ 1 := by
      rw [Real.dist_eq] at hnear
      exact abs_le.mp hnear
    have hxI : x - (n : ℝ) ∈ Icc (-1 : ℝ) 2 := by
      constructor <;> linarith [hxy.1, hxy.2]
    have hyI : y - (n : ℝ) ∈ Icc (-1 : ℝ) 2 := by constructor <;> linarith
    have h := hK.dist_le_mul _ hxI _ hyI
    rw [hshift x n, hshift y n] at h
    simp only [Real.dist_eq, sub_sub_sub_cancel_right] at h
    have hdist : dist (ψ x) (ψ y) ≤ (K : ℝ) * dist x y := by
      simpa only [Real.dist_eq] using h
    exact hdist.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)
  · have hfar : 1 ≤ dist x y := (lt_of_not_ge hnear).le
    have hx : |ψ x - x| ≤ B := by simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs] using hbound x
    have hy : |ψ y - y| ≤ B := by simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs] using hbound y
    have htri : dist (ψ x) (ψ y) ≤ dist x y + 2 * B := by
      have h := abs_add_le (ψ x - x) ((x - y) - (ψ y - y))
      have h' := abs_sub_le (x - y) 0 (ψ y - y)
      simp only [sub_zero, zero_sub, abs_neg] at h'
      have heq : (ψ x - x) + ((x - y) - (ψ y - y)) = ψ x - ψ y := by ring
      rw [heq] at h
      rw [Real.dist_eq, Real.dist_eq]
      linarith
    calc
      dist (ψ x) (ψ y) ≤ dist x y + 2 * B := htri
      _ ≤ (1 + 2 * B) * dist x y := by nlinarith
      _ ≤ max (K : ℝ) (1 + 2 * B) * dist x y :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg

theorem exists_lipschitzWith_affinePeriodic_lift_of_immersion
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {Γ : ℝ → F} (hΓ : ContDiff ℝ ∞ Γ)
    (himm : ∀ t, Function.Injective (fderiv ℝ Γ t))
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hperiod : ∀ t, ψ (t + 1) = ψ t + 1)
    {K : ℝ≥0} (hcomp : LipschitzWith K (Γ ∘ ψ)) :
    ∃ C : ℝ≥0, LipschitzWith C ψ :=
  exists_lipschitzWith_of_locallyLipschitz_affinePeriodic
    (locallyLipschitz_lift_of_immersion hΓ himm hψ hcomp) hperiod

end DifferentialGeometry.Analysis

end

end
