import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Basic.FractionalPower
import Mathlib.Analysis.MeanInequalities
import DifferentialGeometry.Analysis.FunctionalAnalysis.PiLpMap

noncomputable section

open Filter
open scoped Topology ContDiff

private theorem tsum_rpow_mul_rpow_le {ι : Type*} (f g : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i)
    (hfs : Summable f) (hgs : Summable g) {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∑' i, f i ^ (1 - θ) * g i ^ θ ≤ (∑' i, f i) ^ (1 - θ) * (∑' i, g i) ^ θ := by
  rcases eq_or_lt_of_le hθ with hθ | hθ
  · rw [← hθ]
    simp
  rcases eq_or_lt_of_le hθ1 with hθ1 | hθ1
  · rw [hθ1]
    simp
  have h0 : 0 < 1 - θ := sub_pos.mpr hθ1
  have hf' : ∀ i, (f i ^ (1 - θ)) ^ (1 - θ)⁻¹ = f i := fun i => by
    rw [← Real.rpow_mul (hf i), mul_inv_cancel₀ h0.ne', Real.rpow_one]
  have hg' : ∀ i, (g i ^ θ) ^ θ⁻¹ = g i := fun i => by
    rw [← Real.rpow_mul (hg i), mul_inv_cancel₀ hθ.ne', Real.rpow_one]
  have H := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg
    (Real.HolderConjugate.one_sub_inv_inv hθ hθ1)
    (fun i => Real.rpow_nonneg (hf i) (1 - θ))
    (fun i => Real.rpow_nonneg (hg i) θ)
    (by simpa only [hf'] using hfs) (by simpa only [hg'] using hgs)
  simpa only [hf', hg', one_div, inv_inv] using H

namespace DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

private theorem weight_interpolation (i : TensorEigenIdx (I := I) (M := M) g r s)
    (a b θ c : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i ((1 - θ) * a + θ * b) * c ^ 2 =
      (tensorSobolevWeight (I := I) (M := M) i a * c ^ 2) ^ (1 - θ) *
        (tensorSobolevWeight (I := I) (M := M) i b * c ^ 2) ^ θ := by
  have hw := one_le_one_add_lambda (I := I) (M := M) i
  have hw0 : 0 < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := lt_of_lt_of_le zero_lt_one hw
  rw [Real.mul_rpow (tensorSobolevWeight_nonneg (I := I) (M := M) i a) (sq_nonneg c),
    Real.mul_rpow (tensorSobolevWeight_nonneg (I := I) (M := M) i b) (sq_nonneg c)]
  have hc : (c ^ 2) ^ (1 - θ) * (c ^ 2) ^ θ = c ^ 2 := by
    rw [← Real.rpow_add' (sq_nonneg c) (by linarith : (1 - θ) + θ ≠ 0),
      show (1 - θ) + θ = 1 by ring, Real.rpow_one]
  have hwc : tensorSobolevWeight (I := I) (M := M) i ((1 - θ) * a + θ * b) =
      tensorSobolevWeight (I := I) (M := M) i a ^ (1 - θ) *
        tensorSobolevWeight (I := I) (M := M) i b ^ θ := by
    unfold tensorSobolevWeight
    rw [← Real.rpow_mul hw0.le, ← Real.rpow_mul hw0.le, ← Real.rpow_add hw0]
    congr 1
    ring
  rw [hwc]
  calc
    _ = tensorSobolevWeight (I := I) (M := M) i a ^ (1 - θ) *
        tensorSobolevWeight (I := I) (M := M) i b ^ θ *
        ((c ^ 2) ^ (1 - θ) * (c ^ 2) ^ θ) := by rw [hc]
    _ = _ := by ring

private theorem norm_sq_inclusion_interpolation {a b θ : ℝ} (hab : a ≤ b)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (u : TensorHs (I := I) (M := M) g r s b) :
    ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      (show (1 - θ) * a + θ * b ≤ b by nlinarith) u‖ ^ 2 ≤
      (‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hab u‖ ^ 2) ^ (1 - θ) *
        (‖u‖ ^ 2) ^ θ := by
  rw [norm_sq_eq_tsum, norm_sq_eq_tsum, norm_sq_eq_tsum]
  simp only [tensorHsInclusion_coeff_apply]
  rcases eq_or_lt_of_le hθ with heq | hθ
  · have hθ0 : θ = 0 := heq.symm
    subst θ
    simp
  rcases eq_or_lt_of_le hθ1 with heq | hθ1
  · subst θ
    simp
  simp_rw [weight_interpolation _ a b θ _]
  exact tsum_rpow_mul_rpow_le _ _
    (fun i => mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i a) (sq_nonneg _))
    (fun i => mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i b) (sq_nonneg _))
    (u.weighted_summable_of_le hab) u.weighted_summable hθ.le hθ1.le

theorem norm_inclusion_interpolation {a b θ : ℝ} (hab : a ≤ b)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (u : TensorHs (I := I) (M := M) g r s b) :
    ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      (show (1 - θ) * a + θ * b ≤ b by nlinarith) u‖ ≤
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hab u‖ ^ (1 - θ) *
        ‖u‖ ^ θ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _))).mp
  rw [mul_pow, Real.rpow_pow_comm (norm_nonneg _) (1 - θ) 2,
    Real.rpow_pow_comm (norm_nonneg _) θ 2]
  exact norm_sq_inclusion_interpolation hab hθ hθ1 u

theorem norm_piLpMap_inclusion_interpolation {ι : Type*} [Fintype ι]
    {a b θ : ℝ} (hab : a ≤ b) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (u : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s b)) :
    ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show (1 - θ) * a + θ * b ≤ b by nlinarith)) u‖ ≤
      ‖ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hab) u‖ ^ (1 - θ) *
          ‖u‖ ^ θ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _))).mp
  rw [mul_pow, Real.rpow_pow_comm (norm_nonneg _) (1 - θ) 2,
    Real.rpow_pow_comm (norm_nonneg _) θ 2]
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  change (∑ i, ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
    (show (1 - θ) * a + θ * b ≤ b by nlinarith) (u i)‖ ^ 2) ≤ _
  calc
    _ ≤ ∑ i, (‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hab (u i)‖ ^ 2) ^
        (1 - θ) * (‖u i‖ ^ 2) ^ θ :=
      Finset.sum_le_sum fun i _ => norm_sq_inclusion_interpolation hab hθ hθ1 (u i)
    _ ≤ _ := by
      simpa only [tsum_fintype, ContinuousLinearMap.piLpMap_apply] using tsum_rpow_mul_rpow_le
        (fun i : ι => ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s) hab (u i)‖ ^ 2)
        (fun i : ι => ‖u i‖ ^ 2) (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
        (hasSum_fintype _).summable (hasSum_fintype _).summable hθ hθ1

end DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorHs
