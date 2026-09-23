import DifferentialGeometry.Analysis.Calculus.Derivative.Right
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

noncomputable section
open scoped InnerProductSpace
namespace DifferentialGeometry.Analysis
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem rayleigh_quotient_derivative_le_of_residual_bound
    (u z f : H) {A K C N e' d' : ℝ}
    (henergy : 0 < ‖u‖ ^ 2) (hdirichlet : 0 ≤ ⟪z, u⟫_ℝ)
    (hf : ‖f‖ ≤ A * ‖u‖)
    (hC : C ≤ K * ‖u‖ ^ 2)
    (hN : N = ⟪z, u⟫_ℝ / ‖u‖ ^ 2)
    (he : e' = -2 * ⟪z, u⟫_ℝ + 2 * ⟪u, f⟫_ℝ - C)
    (hd : d' = -2 * ‖z‖ ^ 2 + 2 * ⟪z, f⟫_ℝ) :
    (d' * ‖u‖ ^ 2 - ⟪z, u⟫_ℝ * e') / (‖u‖ ^ 2) ^ 2 ≤
      K * N + A ^ 2 / 2 := by
  have hNpos : 0 ≤ N := hN ▸ div_nonneg hdirichlet henergy.le
  have hNE : N * ‖u‖ ^ 2 = ⟪z, u⟫_ℝ := by
    rw [hN,div_mul_cancel₀ _ henergy.ne']
  have hsq : ‖z - N • u‖ ^ 2 = ‖z‖ ^ 2 - 2 * N * ⟪z, u⟫_ℝ + N ^ 2 * ‖u‖ ^ 2 := by
    rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    ring
  have hinn : ⟪z - N • u, f⟫_ℝ = ⟪z, f⟫_ℝ - N * ⟪u, f⟫_ℝ := by
    rw [inner_sub_left,real_inner_smul_left]
  have hyoung : -2 * ‖z - N • u‖ ^ 2 + 2 * ⟪z - N • u, f⟫_ℝ ≤ ‖f‖ ^ 2 / 2 := by
    have hsqnon : 0 ≤ (2 * ‖z - N • u‖ - ‖f‖) ^ 2 := sq_nonneg _
    have hnorm : 0 ≤ ‖z - N • u‖ := norm_nonneg _
    have hfnon : 0 ≤ ‖f‖ := norm_nonneg _
    nlinarith [real_inner_le_norm (z - N • u) f]
  have hfsq : ‖f‖ ^ 2 ≤ A ^ 2 * ‖u‖ ^ 2 := by
    nlinarith [norm_nonneg f, norm_nonneg u]
  have hNC : N * C ≤ K * N * ‖u‖ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hC hNpos
    nlinarith
  have hbound : -2 * ‖z - N • u‖ ^ 2 + 2 * ⟪z - N • u, f⟫_ℝ + N * C ≤
      (K * N + A ^ 2 / 2) * ‖u‖ ^ 2 := by
    nlinarith
  have hnum : d' - N * e' =
      -2 * ‖z - N • u‖ ^ 2 + 2 * ⟪z - N • u, f⟫_ℝ + N * C := by
    rw [he,hd,hsq,hinn,← hNE]
    ring
  have hrat : (d' * ‖u‖ ^ 2 - ⟪z, u⟫_ℝ * e') / (‖u‖ ^ 2) ^ 2 =
      (d' - N * e') / ‖u‖ ^ 2 := by
    rw [← hNE]
    field_simp [henergy.ne']
  rw [hrat,hnum]
  exact (div_le_iff₀ henergy).mpr hbound

end DifferentialGeometry.Analysis

noncomputable section
open scoped InnerProductSpace
namespace DifferentialGeometry.Analysis
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem hasDerivAt_dirichlet_quotient_le
    (u z f : H) {energy dirichlet : ℝ → ℝ} {t A K C : ℝ}
    (henergy : energy t = ‖u‖ ^ 2) (hpositive : 0 < energy t)
    (hdirichlet : dirichlet t = ⟪z, u⟫_ℝ) (hdirichlet_nonneg : 0 ≤ dirichlet t)
    (hE : HasDerivAt energy (-2 * dirichlet t + 2 * ⟪u, f⟫_ℝ - C) t)
    (hD : HasDerivAt dirichlet (-2 * ‖z‖ ^ 2 + 2 * ⟪z, f⟫_ℝ) t)
    (hf : ‖f‖ ≤ A * ‖u‖) (hC : C ≤ K * energy t) :
    ∃ N' : ℝ, HasDerivAt (fun s => dirichlet s / energy s) N' t ∧
      N' ≤ K * (dirichlet t / energy t) + A ^ 2 / 2 := by
  let value := ((-2 * ‖z‖ ^ 2 + 2 * ⟪z, f⟫_ℝ) * energy t -
    dirichlet t * (-2 * dirichlet t + 2 * ⟪u, f⟫_ℝ - C)) / (energy t) ^ 2
  refine ⟨value, ?_, ?_⟩
  · exact hD.fun_div hE hpositive.ne'
  · dsimp only [value]
    rw [henergy] at hpositive hC ⊢
    rw [hdirichlet] at hdirichlet_nonneg ⊢
    exact rayleigh_quotient_derivative_le_of_residual_bound u z f hpositive
      hdirichlet_nonneg hf hC rfl rfl rfl

end DifferentialGeometry.Analysis


noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace DifferentialGeometry.Analysis

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

private theorem norm_toLp_sq_eq_integral (u : C(X, ℝ)) :
    ‖u.toLp 2 μ ℝ‖ ^ 2 = ∫ x, (u x) ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,ContinuousMap.inner_toLp]
  simp only [conj_trivial,← pow_two]

theorem dirichlet_quotient_derivative_le_of_integrals
    (u z f R : C(X, ℝ)) {energy dirichlet : ℝ → ℝ} {t A K : ℝ}
    (henergy : energy t = ∫ x, (u x) ^ 2 ∂μ) (hpositive : 0 < energy t)
    (hdirichlet : dirichlet t = ∫ x, z x * u x ∂μ) (hDnonneg : 0 ≤ dirichlet t)
    (hE : HasDerivAt energy (-2 * dirichlet t + 2 * (∫ x, u x * f x ∂μ) -
      ∫ x, R x * (u x) ^ 2 ∂μ) t)
    (hD : HasDerivAt dirichlet (-2 * (∫ x, (z x) ^ 2 ∂μ) + 2 * (∫ x, z x * f x ∂μ)) t)
    (hA : 0 ≤ A) (hresidual : ∀ x, |f x| ≤ A * |u x|)
    (hR : ∀ x, R x ≤ K) :
    ∃ N' : ℝ, HasDerivAt (fun s => dirichlet s / energy s) N' t ∧
      N' ≤ K * (dirichlet t / energy t) + A ^ 2 / 2 := by
  have hinner (v w : C(X, ℝ)) : ⟪v.toLp 2 μ ℝ, w.toLp 2 μ ℝ⟫_ℝ = ∫ x, v x * w x ∂μ := by
    rw [ContinuousMap.inner_toLp]
    simp only [conj_trivial,mul_comm]
  have hres : ‖f.toLp 2 μ ℝ‖ ≤ A * ‖u.toLp 2 μ ℝ‖ := by
    have hsq : ‖f.toLp 2 μ ℝ‖ ^ 2 ≤ A ^ 2 * ‖u.toLp 2 μ ℝ‖ ^ 2 := by
      rw [norm_toLp_sq_eq_integral,norm_toLp_sq_eq_integral,← integral_const_mul]
      apply integral_mono
      · exact (f.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact (continuous_const.mul (u.continuous.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · intro x
        have hh := hresidual x
        have hh2 := mul_le_mul hh hh (abs_nonneg (f x)) (mul_nonneg hA (abs_nonneg (u x)))
        calc
          (f x) ^ 2 = |f x| * |f x| := by rw [← pow_two,sq_abs]
          _ ≤ A * |u x| * (A * |u x|) := hh2
          _ = A ^ 2 * (u x) ^ 2 := by nlinarith [sq_abs (u x)]
    have hnn : 0 ≤ A * ‖u.toLp 2 μ ℝ‖ := mul_nonneg hA (norm_nonneg _)
    apply (sq_le_sq₀ (norm_nonneg _) hnn).mp
    simpa only [mul_pow] using hsq
  have hC : (∫ x, R x * (u x) ^ 2 ∂μ) ≤ K * energy t := by
    rw [henergy,← integral_const_mul]
    apply integral_mono
    · exact (R.continuous.mul (u.continuous.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact (continuous_const.mul (u.continuous.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · intro x
      exact mul_le_mul_of_nonneg_right (hR x) (sq_nonneg _)
  apply hasDerivAt_dirichlet_quotient_le (u.toLp 2 μ ℝ) (z.toLp 2 μ ℝ) (f.toLp 2 μ ℝ)
    (henergy.trans (norm_toLp_sq_eq_integral μ u).symm) hpositive
    (hdirichlet.trans (hinner z u).symm) hDnonneg
  · simpa only [hinner] using hE
  · simpa only [norm_toLp_sq_eq_integral,hinner] using hD
  · exact hres
  · exact hC

end DifferentialGeometry.Analysis

noncomputable section
open MeasureTheory
namespace DifferentialGeometry.Analysis
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem heat_energy_derivative_lower_bound
    (u V R : C(X, ℝ)) {energy dirichlet energy' A K : ℝ}
    (henergy : energy = ∫ x, (u x) ^ 2 ∂μ) (hpositive : 0 < energy)
    (hderiv : energy' = -2 * dirichlet + ∫ x, (2 * V x - R x) * (u x) ^ 2 ∂μ)
    (hV : ∀ x, -A ≤ V x) (hR : ∀ x, R x ≤ K) :
    -(2 * (dirichlet / energy) + (2 * A + K)) * energy ≤ energy' := by
  have hIntegral : -(2 * A + K) * energy ≤
      ∫ x, (2 * V x - R x) * (u x) ^ 2 ∂μ := by
    rw [henergy,← integral_const_mul]
    apply integral_mono
    · exact (continuous_const.mul (u.continuous.pow 2)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact (((continuous_const.mul V.continuous).sub R.continuous).mul
        (u.continuous.pow 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · intro x
      exact mul_le_mul_of_nonneg_right (by linarith [hV x,hR x]) (sq_nonneg _)
  rw [hderiv]
  have hquot : dirichlet / energy * energy = dirichlet := div_mul_cancel₀ _ hpositive.ne'
  nlinarith

end DifferentialGeometry.Analysis


noncomputable section
open MeasureTheory
namespace DifferentialGeometry.Analysis

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem integral_frequency_differential_bounds
    (u z V R : C(X, ℝ)) {energy dirichlet : ℝ → ℝ} {t A K : ℝ}
    (henergy : energy t = ∫ x, (u x) ^ 2 ∂μ) (hpositive : 0 < energy t)
    (hdirichlet : dirichlet t = ∫ x, z x * u x ∂μ) (hDnonneg : 0 ≤ dirichlet t)
    (hE : HasDerivAt energy (-2 * dirichlet t + ∫ x, (2 * V x - R x) * (u x) ^ 2 ∂μ) t)
    (hD : HasDerivAt dirichlet (-2 * (∫ x, (z x) ^ 2 ∂μ) +
      2 * (∫ x, z x * (V x * u x) ∂μ)) t)
    (hA : 0 ≤ A) (hV : ∀ x, |V x| ≤ A) (hR : ∀ x, R x ≤ K) :
    (deriv dirichlet t * energy t - dirichlet t * deriv energy t) / (energy t) ^ 2 ≤
      K * (dirichlet t / energy t) + A ^ 2 / 2 ∧
    -(2 * (dirichlet t / energy t) + (2 * A + K)) * energy t ≤ deriv energy t := by
  let f : C(X, ℝ) := V * u
  have hpotential : (∫ x, (2 * V x - R x) * (u x) ^ 2 ∂μ) =
      2 * (∫ x, u x * f x ∂μ) - ∫ x, R x * (u x) ^ 2 ∂μ := by
    have hfun : (fun x => (2 * V x - R x) * (u x) ^ 2) =
        (fun x => 2 * (u x * f x) - R x * (u x) ^ 2) := by
      funext x
      simp only [f,ContinuousMap.mul_apply]
      ring
    rw [hfun,integral_sub,integral_const_mul]
    · exact (continuous_const.mul (u.continuous.mul f.continuous)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact (R.continuous.mul (u.continuous.pow 2)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hE' : HasDerivAt energy (-2 * dirichlet t + 2 * (∫ x, u x * f x ∂μ) -
      ∫ x, R x * (u x) ^ 2 ∂μ) t := by
    rw [hpotential] at hE
    convert hE using 1
    ring
  obtain ⟨N',hN,hNbound⟩ := dirichlet_quotient_derivative_le_of_integrals μ u z f R
    henergy hpositive hdirichlet hDnonneg hE' hD hA
    (fun x => by
      change |V x * u x| ≤ A * |u x|
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hV x) (abs_nonneg _)) hR
  have hquot := (hD.fun_div hE hpositive.ne').deriv
  rw [hN.deriv] at hquot
  constructor
  · rw [hE.deriv,hD.deriv]
    exact hquot ▸ hNbound
  · exact heat_energy_derivative_lower_bound μ u V R henergy hpositive hE.deriv
      (fun x => (abs_le.mp (hV x)).1) hR

end DifferentialGeometry.Analysis


open Set
namespace DifferentialGeometry.Analysis

theorem exists_first_zero_of_nonneg_on_interval
    {energy : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn energy (Icc a b))
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ energy t)
    (hpositive : 0 < energy a) (hzero : energy b = 0) :
    ∃ c ∈ Ioc a b, energy c = 0 ∧ ∀ t ∈ Ico a c, 0 < energy t := by
  let Z := {t ∈ Icc a b | energy t = 0}
  have hZ : IsCompact Z := by
    have hc := hcont.lowerSemicontinuousOn.isCompact_inter_preimage_Iic isCompact_Icc 0
    convert hc using 1
    ext t
    simp only [Z,mem_ofPred_eq,mem_inter_iff,mem_preimage,mem_Iic]
    exact and_congr_right fun ht => ⟨fun h => h.le,fun h => le_antisymm h (hnonneg t ht)⟩
  have hZn : Z.Nonempty := ⟨b,⟨hab.le,le_rfl⟩,hzero⟩
  obtain ⟨c,hc,hmin⟩ := hZ.exists_isMinOn hZn continuousOn_id
  have hac : a < c := by
    have hh : a ≤ c := hc.1.1
    rcases hh.eq_or_lt with h | h
    · have hz : energy a = 0 := h ▸ hc.2
      linarith
    · exact h
  refine ⟨c,⟨hac,hc.1.2⟩,hc.2,?_⟩
  intro t ht
  have hti : t ∈ Icc a b := ⟨ht.1,ht.2.le.trans hc.1.2⟩
  have hnn := hnonneg t hti
  by_contra hnot
  have hz : energy t = 0 := le_antisymm (not_lt.mp hnot) hnn
  have hct : c ≤ t := hmin ⟨hti,hz⟩
  exact (not_le.mpr ht.2) hct

end DifferentialGeometry.Analysis


noncomputable section
open Set Filter
open scoped Topology
namespace DifferentialGeometry.Analysis

private theorem le_exp_mul_of_deriv_le_mul
    {f f' : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Ioo a b, f' t ≤ C * f t) :
    f b ≤ Real.exp (C * (b - a)) * f a := by
  have h := DifferentialGeometry.exp_neg_intervalIntegral_mul_le_of_deriv_add_mul_nonneg hab
    hf.neg (a := fun _ => -C) continuousOn_const
    (fun t ht => (hd t ht).neg) (fun t ht => by have hh := hbound t ht; dsimp; linarith)
  simp only [intervalIntegral.integral_const,smul_eq_mul,mul_neg,neg_neg] at h
  simpa only [Pi.neg_apply,mul_neg,neg_mul,neg_le_neg_iff,mul_comm] using h

theorem terminal_positive_of_dirichlet_quotient_bounds
    {energy frequency energy' frequency' : ℝ → ℝ} {a b K B C : ℝ}
    (hab : a < b) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (henergy : ContinuousOn energy (Icc a b))
    (hfrequency : ContinuousOn frequency (Ico a b))
    (hpositive : ∀ t ∈ Ico a b, 0 < energy t)
    (hnonneg : ∀ t ∈ Ico a b, 0 ≤ frequency t)
    (hE : ∀ t ∈ Ioo a b, HasDerivAt energy (energy' t) t)
    (hN : ∀ t ∈ Ioo a b, HasDerivAt frequency (frequency' t) t)
    (hNbound : ∀ t ∈ Ioo a b, frequency' t ≤ K * frequency t + B)
    (hEbound : ∀ t ∈ Ioo a b, -(2 * frequency t + C) * energy t ≤ energy' t) :
    0 < energy b := by
  let bound := (frequency a + 1) * Real.exp ((K + B) * (b - a))
  have hfreqA : 0 ≤ frequency a := hnonneg a ⟨le_rfl,hab⟩
  have hfreq (t : ℝ) (ht : t ∈ Ico a b) : frequency t ≤ bound := by
    rcases ht.1.eq_or_lt with rfl | hat
    · have hExp : 1 ≤ Real.exp ((K + B) * (b - a)) :=
        Real.one_le_exp_iff.mpr (mul_nonneg (add_nonneg hK hB) (sub_pos.mpr hab).le)
      dsimp [bound]
      nlinarith
    · have hncont : ContinuousOn (fun s => frequency s + 1) (Icc a t) :=
        (hfrequency.mono fun s hs => ⟨hs.1,hs.2.trans_lt ht.2⟩).add continuousOn_const
      have hfreq' := le_exp_mul_of_deriv_le_mul hat hncont
        (fun s hs => (hN s ⟨hs.1,hs.2.trans ht.2⟩).add_const 1)
        (C := K + B) (fun s hs => by
          have hn := hNbound s ⟨hs.1,hs.2.trans ht.2⟩
          have hnn := hnonneg s ⟨hs.1.le,hs.2.trans ht.2⟩
          nlinarith)
      have hExp : Real.exp ((K + B) * (t - a)) ≤ Real.exp ((K + B) * (b - a)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le a) (add_nonneg hK hB))
      have hh := mul_le_mul_of_nonneg_right hExp (by linarith : 0 ≤ frequency a + 1)
      dsimp [bound]
      nlinarith
  have hlower (t : ℝ) (ht : t ∈ Ioo a b) :
      Real.exp (-(2 * bound + C) * (t - a)) * energy a ≤ energy t := by
    have hh := DifferentialGeometry.exp_neg_intervalIntegral_mul_le_of_deriv_add_mul_nonneg ht.1
      (henergy.mono (Icc_subset_Icc_right ht.2.le))
      (a := fun _ => 2 * bound + C) continuousOn_const
      (fun s hs => hE s ⟨hs.1,hs.2.trans ht.2⟩)
      (fun s hs => by
        have hne := hEbound s ⟨hs.1,hs.2.trans ht.2⟩
        have hf := hfreq s ⟨hs.1.le,hs.2.trans ht.2⟩
        have he := (hpositive s ⟨hs.1.le,hs.2.trans ht.2⟩).le
        nlinarith)
    simpa only [intervalIntegral.integral_const,smul_eq_mul,neg_mul,mul_neg,mul_comm] using hh
  have hlim : Real.exp (-(2 * bound + C) * (b - a)) * energy a ≤ energy b := by
    apply le_of_tendsto_of_tendsto
      (((Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))).mul
        continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      ((henergy b ⟨hab.le,le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLT hab))
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht
    exact hlower t ht
  exact (mul_pos (Real.exp_pos _) (hpositive a ⟨le_rfl,hab⟩)).trans_le hlim

end DifferentialGeometry.Analysis


noncomputable section
open Set
namespace DifferentialGeometry.Analysis

theorem eq_zero_of_terminal_zero_of_dirichlet_quotient_bounds
    {energy dirichlet energy' dirichlet' : ℝ → ℝ} {a b K B C : ℝ}
    (hab : a < b) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (henergy : ContinuousOn energy (Icc a b))
    (hdirichlet : ContinuousOn dirichlet (Ioo a b))
    (hnonneg : ∀ t ∈ Icc a b, 0 ≤ energy t)
    (hdnonneg : ∀ t ∈ Icc a b, 0 ≤ dirichlet t)
    (hE : ∀ t ∈ Ioo a b, HasDerivAt energy (energy' t) t)
    (hD : ∀ t ∈ Ioo a b, HasDerivAt dirichlet (dirichlet' t) t)
    (hNbound : ∀ t ∈ Ioo a b, 0 < energy t →
      (dirichlet' t * energy t - dirichlet t * energy' t) / (energy t) ^ 2 ≤
        K * (dirichlet t / energy t) + B)
    (hEbound : ∀ t ∈ Ioo a b, 0 < energy t →
      -(2 * (dirichlet t / energy t) + C) * energy t ≤ energy' t)
    (hterminal : energy b = 0) :
    ∀ t ∈ Icc a b, energy t = 0 := by
  have hzero (t : ℝ) (ht : t ∈ Ioo a b) : energy t = 0 := by
    by_contra hne
    have hp : 0 < energy t := lt_of_le_of_ne (hnonneg t (Ioo_subset_Icc_self ht)) (Ne.symm hne)
    obtain ⟨c,hc,hcz,hpos⟩ := exists_first_zero_of_nonneg_on_interval ht.2
      (henergy.mono (Icc_subset_Icc_left ht.1.le))
      (fun s hs => hnonneg s ⟨ht.1.le.trans hs.1,hs.2⟩) hp hterminal
    let N := fun s => dirichlet s / energy s
    let N' := fun s => (dirichlet' s * energy s - dirichlet s * energy' s) / (energy s)^2
    have hsub : Icc t c ⊆ Icc a b := fun s hs => ⟨ht.1.le.trans hs.1,hs.2.trans hc.2⟩
    have hsubopen : Ioo t c ⊆ Ioo a b := fun s hs => ⟨ht.1.trans hs.1,hs.2.trans_le hc.2⟩
    have hNcont : ContinuousOn N (Ico t c) :=
      (hdirichlet.mono (fun s hs => ⟨ht.1.trans_le hs.1,hs.2.trans_le hc.2⟩)).div
        ((henergy.mono hsub).mono Ico_subset_Icc_self) (fun s hs => (hpos s hs).ne')
    have hnpos : ∀ s ∈ Ico t c, 0 ≤ N s := fun s hs =>
      div_nonneg (hdnonneg s (hsub (Ico_subset_Icc_self hs))) (hpos s hs).le
    have hNd : ∀ s ∈ Ioo t c, HasDerivAt N (N' s) s := fun s hs =>
      (hD s (hsubopen hs)).fun_div (hE s (hsubopen hs)) (hpos s ⟨hs.1.le,hs.2⟩).ne'
    have hpositive := terminal_positive_of_dirichlet_quotient_bounds hc.1 hK hB
      (henergy.mono hsub) hNcont hpos hnpos
      (fun s hs => hE s (hsubopen hs)) hNd
      (fun s hs => hNbound s (hsubopen hs) (hpos s ⟨hs.1.le,hs.2⟩))
      (fun s hs => hEbound s (hsubopen hs) (hpos s ⟨hs.1.le,hs.2⟩))
    exact (ne_of_gt hpositive) hcz
  have hEq : Set.EqOn energy (fun _ => 0) (Ioo a b) := fun s hs => hzero s hs
  exact hEq.of_subset_closure henergy continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hab.ne])

end DifferentialGeometry.Analysis
