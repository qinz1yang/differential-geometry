import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.Convolution.Lp
import Mathlib.MeasureTheory.Integral.PeakFunction

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic.Euclidean

open Filter MeasureTheory Bornology
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem tendsto_integral_heatKernel_smul {f : V → F} {x₀ : V}
    (hf : Integrable f) (hf0 : ContinuousAt f x₀) :
    Tendsto (fun t : ℝ => ∫ x : V, heatKernel t (x₀ - x) • f x)
      (𝓝[>] 0) (𝓝 (f x₀)) := by
  have htail : Tendsto (fun x : V => ‖x‖ ^ Module.finrank ℝ V * baseHeat x)
      (cobounded V) (𝓝 0) := by
    have hsq : Tendsto (fun x : V => ‖x‖ ^ 2) (cobounded V) atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_norm_cobounded_atTop
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (Module.finrank ℝ V / 2 : ℝ) 4⁻¹ (by norm_num)).comp hsq
    have h' := h.const_mul (baseHeatMass V)⁻¹
    simp only [Function.comp_def, mul_zero] at h'
    convert h' using 1
    funext x
    dsimp only [baseHeat]
    rw [← Real.rpow_natCast (‖x‖), ← Real.rpow_natCast (‖x‖) 2,
      ← Real.rpow_mul (norm_nonneg x)]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (Module.finrank ℝ V / 2) = Module.finrank ℝ V by ring]
    ring
  have hlim : Tendsto (fun c : ℝ => ∫ x : V,
      (c ^ Module.finrank ℝ V * baseHeat (c • (x₀ - x))) • f x) atTop (𝓝 (f x₀)) :=
    tendsto_integral_comp_smul_smul_of_integrable' baseHeat_nonneg integral_baseHeat htail hf hf0
  have hc : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) (𝓝[>] 0) atTop := by
    have h := Real.tendsto_sqrt_atTop.comp tendsto_inv_nhdsGT_zero
    simpa only [Function.comp_def, Real.sqrt_inv] using h
  simpa only [Function.comp_def, heatKernel, heatScale, inv_pow] using hlim.comp hc

omit [CompleteSpace F] in
theorem integrable_heatKernel_smul {f : V → F} (hf : Integrable f) (x₀ : V)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : V => heatKernel t (x₀ - x) • f x) := by
  apply hf.bdd_smul (((heatScale t) ^ Module.finrank ℝ V)⁻¹ * (baseHeatMass V)⁻¹)
  · apply Continuous.aestronglyMeasurable
    unfold heatKernel baseHeat
    fun_prop
  · apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg ht (x₀ - x))]
    unfold heatKernel baseHeat
    rw [← mul_assoc]
    apply mul_le_of_le_one_right
      (mul_nonneg (inv_nonneg.mpr (pow_nonneg (heatScale_pos ht).le _))
        (inv_nonneg.mpr (baseHeatMass_pos (V := V)).le))
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _))

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] in
theorem heatKernel_eq_of_finrank_eq_two (hn : Module.finrank ℝ V = 2)
    {t : ℝ} (ht : 0 < t) (x : V) :
    heatKernel t x = (4 * Real.pi * t)⁻¹ * Real.exp (-‖x‖ ^ 2 / (4 * t)) := by
  unfold heatKernel heatScale baseHeat baseHeatMass
  rw [hn]
  simp only [Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, Real.sq_sqrt ht.le]
  have he : -(4 : ℝ)⁻¹ * (t⁻¹ * ‖x‖ ^ 2) = -‖x‖ ^ 2 / (4 * t) := by ring
  rw [he]
  rw [← mul_assoc]
  congr 1
  field_simp

theorem tendsto_integral_heatKernel_smul_polynomial
    (N : ℕ) (a : ℕ → V → F) (x₀ : V)
    (ha : ∀ k ≤ N, Integrable (a k))
    (ha0 : ∀ k ≤ N, ContinuousAt (a k) x₀) :
    Tendsto (fun t : ℝ => ∫ x : V,
      heatKernel t (x₀ - x) • ∑ k ∈ Finset.range (N + 1), t ^ k • a k x)
      (𝓝[>] 0) (𝓝 (a 0 x₀)) := by
  have hzero : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hsum : Tendsto (fun t : ℝ =>
      ∑ k ∈ Finset.range (N + 1), t ^ k •
        ∫ x : V, heatKernel t (x₀ - x) • a k x)
      (𝓝[>] 0) (𝓝 (∑ k ∈ Finset.range (N + 1), (0 : ℝ) ^ k • a k x₀)) := by
    apply tendsto_finsetSum
    intro k hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact (hzero.pow k).smul (tendsto_integral_heatKernel_smul (ha k hkN) (ha0 k hkN))
  have hsum0 : (∑ k ∈ Finset.range (N + 1), (0 : ℝ) ^ k • a k x₀) = a 0 x₀ := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk
      simp only [zero_pow hk, zero_smul]
    · simp
  rw [hsum0] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  simp_rw [Finset.smul_sum]
  rw [integral_finsetSum _ (fun k hk => ?_)]
  · apply Finset.sum_congr rfl
    intro k _
    rw [← integral_smul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => smul_comm _ _ _
  · have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hi := integrable_heatKernel_smul (ha k hkN) x₀ ht
    have hi' := hi.smul (t ^ k)
    convert hi' using 1
    funext x
    exact smul_comm _ _ _

theorem tendsto_integral_heatKernel_smul_cutoff_polynomial
    (N : ℕ) (χ : V → ℝ) (a : ℕ → V → F) (x₀ : V)
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχ0 : χ x₀ = 1)
    (ha : ∀ k ≤ N, ∀ x ∈ tsupport χ, ContinuousAt (a k) x) :
    Tendsto (fun t : ℝ => ∫ x : V,
      heatKernel t (x₀ - x) •
        ∑ k ∈ Finset.range (N + 1), t ^ k • (χ x • a k x))
      (𝓝[>] 0) (𝓝 (a 0 x₀)) := by
  have hχa (k : ℕ) (hk : k ≤ N) : Continuous (fun x => χ x • a k x) := by
    apply continuous_of_tsupport
    intro x hx
    exact hχ.continuousAt.smul (ha k hk x (tsupport_smul_subset_left _ _ hx))
  have hχ0mem : x₀ ∈ tsupport χ := subset_closure (by simp [Function.mem_support, hχ0])
  have h := tendsto_integral_heatKernel_smul_polynomial N (fun k x => χ x • a k x) x₀
    (fun k hk => (hχa k hk).integrable_of_hasCompactSupport hχc.smul_right)
    (fun k hk => hχ.continuousAt.smul (ha k hk x₀ hχ0mem))
  simpa only [hχ0, one_smul] using h

end DifferentialGeometry.Analysis.Parabolic.Euclidean
