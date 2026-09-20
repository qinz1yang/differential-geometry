import DifferentialGeometry.Topology.LoopSpace.JoinedLoop
import Mathlib.Analysis.Calculus.Deriv.CompMul
import DifferentialGeometry.Analysis.Sobolev.Interval.TraceCompactness
import DifferentialGeometry.Topology.LoopSpace.InverseLipschitz
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped NNReal Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem deriv_joinedLoop_first {a b : ℝ → F} (hba : b 1 = a 0) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) :
    deriv (joinedLoop a b) t = (2 : ℝ) • deriv a (2 * t) := by
  have heq : joinedLoop a b =ᶠ[𝓝 t] (fun s => a (2 * s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact joinedLoop_first hba (Ioo_subset_Icc_self hs)
  rw [heq.deriv_eq, deriv_comp_mul_left]

private theorem deriv_joinedLoop_second {a b : ℝ → F}
    (hab : a 1 = b 0) (hba : b 1 = a 0) {t : ℝ}
    (ht : t ∈ Ioo (1 / 2 : ℝ) 1) :
    deriv (joinedLoop a b) t = (2 : ℝ) • deriv b (2 * t - 1) := by
  have heq : joinedLoop a b =ᶠ[𝓝 t] (fun s => b (2 * s - 1)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact joinedLoop_second hab hba (Ioo_subset_Icc_self hs)
  rw [heq.deriv_eq]
  change deriv ((fun x => b (x - 1)) ∘ fun s => 2 * s) t = _
  dsimp only [Function.comp_def]
  rw [deriv_comp_mul_left (2 : ℝ) (fun x => b (x - 1)) t, deriv_comp_sub_const]

private theorem integral_Icc_deriv_sq_eq_of_lipschitz [CompleteSpace F]
    {f : ℝ → F} {K : ℝ≥0} (hf : LipschitzWith K f) (x y : ℝ) :
    IntegrableOn (fun t => ‖deriv f t‖ ^ 2) (Icc x y) := by
  have hm : MemLp (deriv f) 2 (volume.restrict (Icc x y)) :=
    MemLp.of_bound (aestronglyMeasurable_deriv f _) K
      (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hf)
  exact hm.norm.integrable_sq

private theorem integral_double_first (f : ℝ → ℝ) :
    (∫ t in Icc (0 : ℝ) (1 / 2), 4 * f (2 * t)) = 2 * ∫ t in Icc (0 : ℝ) 1, f t := by
  have h := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1 / 2) f 2
  norm_num only [mul_zero, mul_one_div_cancel (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at h
  rw [integral_const_mul]
  linarith

private theorem integral_double_second (f : ℝ → ℝ) :
    (∫ t in Icc (1 / 2 : ℝ) 1, 4 * f (2 * t - 1)) =
      2 * ∫ t in Icc (0 : ℝ) 1, f t := by
  have h := intervalIntegral.smul_integral_comp_mul_sub (a := (1 / 2 : ℝ)) (b := 1) f 2 1
  norm_num only [mul_one_div_cancel (by norm_num : (2 : ℝ) ≠ 0), sub_self,
    mul_one, show (2 : ℝ) - 1 = 1 by norm_num, smul_eq_mul] at h
  rw [intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at h
  rw [integral_const_mul]
  linarith

theorem integral_deriv_joinedLoop_sq [CompleteSpace F]
    {a b : ℝ → F} {Ka Kb : ℝ≥0} (ha : LipschitzWith Ka a) (hb : LipschitzWith Kb b)
    (hab : a 1 = b 0) (hba : b 1 = a 0) :
    (∫ t in Icc (0 : ℝ) 1, ‖deriv (joinedLoop a b) t‖ ^ 2) =
      2 * (∫ t in Icc (0 : ℝ) 1, ‖deriv a t‖ ^ 2) +
        2 * (∫ t in Icc (0 : ℝ) 1, ‖deriv b t‖ ^ 2) := by
  have hLip := joinedLoop_lipschitz ha hb hab hba
  have h₁ : (∫ t in Icc (0 : ℝ) (1 / 2), ‖deriv (joinedLoop a b) t‖ ^ 2) =
      2 * ∫ t in Icc (0 : ℝ) 1, ‖deriv a t‖ ^ 2 := by
    trans ∫ t in Icc (0 : ℝ) (1 / 2), 4 * ‖deriv a (2 * t)‖ ^ 2
    · apply integral_congr_ae
      have ht : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (1 / 2)), t ∈ Ioo (0 : ℝ) (1 / 2) := by
        rw [← restrict_Ioo_eq_restrict_Icc]
        exact ae_restrict_mem measurableSet_Ioo
      filter_upwards [ht] with t hti
      rw [deriv_joinedLoop_first hba hti, norm_smul]
      norm_num [mul_pow]
    · exact integral_double_first (fun t => ‖deriv a t‖ ^ 2)
  have h₂ : (∫ t in Icc (1 / 2 : ℝ) 1, ‖deriv (joinedLoop a b) t‖ ^ 2) =
      2 * ∫ t in Icc (0 : ℝ) 1, ‖deriv b t‖ ^ 2 := by
    trans ∫ t in Icc (1 / 2 : ℝ) 1, 4 * ‖deriv b (2 * t - 1)‖ ^ 2
    · apply integral_congr_ae
      have ht : ∀ᵐ t ∂volume.restrict (Icc (1 / 2 : ℝ) 1), t ∈ Ioo (1 / 2 : ℝ) 1 := by
        rw [← restrict_Ioo_eq_restrict_Icc]
        exact ae_restrict_mem measurableSet_Ioo
      filter_upwards [ht] with t hti
      rw [deriv_joinedLoop_second hab hba hti, norm_smul]
      norm_num [mul_pow]
    · exact integral_double_second (fun t => ‖deriv b t‖ ^ 2)
  have hi₁ := integral_Icc_deriv_sq_eq_of_lipschitz hLip (0 : ℝ) (1 / 2)
  have hi₂ := integral_Icc_deriv_sq_eq_of_lipschitz hLip (1 / 2 : ℝ) 1
  have ht := intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr hi₁)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)).mpr hi₂)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2),
    intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc,
    ← integral_Icc_eq_integral_Ioc, h₁, h₂] at ht
  exact ht.symm

end DifferentialGeometry.Analysis

end

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Topology
open scoped NNReal Topology

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
private theorem lipschitz_affine_parameter (p₀ p₁ : ℝ) :
    LipschitzWith (Real.nnabs (p₁ - p₀)) (fun t : ℝ => (1 - t) * p₀ + t * p₁) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.dist_eq]
  have heq : (1 - x) * p₀ + x * p₁ - ((1 - y) * p₀ + y * p₁) =
      (p₁ - p₀) * (x - y) := by ring
  rw [heq, abs_mul]
  rfl

private theorem integral_deriv_sq_le_lipschitz_sq {f : ℝ → F} {C : ℝ≥0}
    (hf : LipschitzWith C f) :
    (∫ t in Icc (0 : ℝ) 1, ‖deriv f t‖ ^ 2) ≤ (C : ℝ) ^ 2 := by
  have hm : MemLp (deriv f) 2 (volume.restrict (Icc (0 : ℝ) 1)) :=
    MemLp.of_bound (aestronglyMeasurable_deriv f _) C
      (Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hf)
  have h := integral_mono_ae hm.norm.integrable_sq
    (integrableOn_const (C := (C : ℝ) ^ 2) (by simp))
    (Eventually.of_forall fun t => pow_le_pow_left₀ (norm_nonneg _)
      (norm_deriv_le_of_lipschitz hf (x₀ := t)) 2)
  simpa using h

theorem joinedLoop_affine_arc_energy_and_norm_bound
    (a Γ : ℝ → F) {Ka KΓ J : ℝ≥0}
    (ha : LipschitzWith Ka a) (hΓ : LipschitzWith KΓ Γ) (hperiod : Function.Periodic Γ 1)
    (hInv : AntilipschitzWith J (hperiod.lift : loopCircle → F))
    {p₀ p₁ : ℝ} (hp : p₀ ≤ p₁) (hshort : p₁ - p₀ ≤ 2 / 3)
    (ha₀ : a 0 = Γ p₁) (ha₁ : a 1 = Γ p₀) :
    let b : ℝ → F := fun t => Γ ((1 - t) * p₀ + t * p₁)
    let E : ℝ := ∫ t in Icc (0 : ℝ) 1, ‖deriv a t‖ ^ 2
    b 0 = a 1 ∧ b 1 = a 0 ∧
      LipschitzWith (KΓ * Real.nnabs (p₁ - p₀)) b ∧
      (p₁ - p₀ ≤ 2 * (J : ℝ) * Real.sqrt E) ∧
      (∫ t in Icc (0 : ℝ) 1, ‖deriv b t‖ ^ 2) ≤
        4 * (KΓ : ℝ) ^ 2 * (J : ℝ) ^ 2 * E ∧
      (∫ t in Icc (0 : ℝ) 1, ‖deriv (joinedLoop a b) t‖ ^ 2) ≤
        (2 + 8 * (KΓ : ℝ) ^ 2 * (J : ℝ) ^ 2) * E ∧
      (∀ t, ‖joinedLoop a b t - a 0‖ ≤ (1 + 2 * (KΓ : ℝ) * (J : ℝ)) * Real.sqrt E) ∧
      (∫ t in Icc (0 : ℝ) 1, ‖joinedLoop a b t - a 0‖ ^ 2) ≤
        (1 + 2 * (KΓ : ℝ) * (J : ℝ)) ^ 2 * E := by
  let b : ℝ → F := fun t => Γ ((1 - t) * p₀ + t * p₁)
  let E : ℝ := ∫ t in Icc (0 : ℝ) 1, ‖deriv a t‖ ^ 2
  have hE : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  have hb : LipschitzWith (KΓ * Real.nnabs (p₁ - p₀)) b :=
    hΓ.comp (lipschitz_affine_parameter p₀ p₁)
  have hb₀ : b 0 = a 1 := by simpa [b] using ha₁.symm
  have hb₁ : b 1 = a 0 := by simpa [b] using ha₀.symm
  have haosc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖a t - a 0‖ ≤ Real.sqrt E := by
    apply Real.le_sqrt_of_sq_le
    have h := Sobolev.norm_sub_sq_le_mul_dist_of_integral_deriv_sq_le ha (le_refl E)
      ht (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    have ht1 : |t - 0| ≤ 1 := by rw [sub_zero, abs_of_nonneg ht.1]; exact ht.2
    exact h.trans ((mul_le_mul_of_nonneg_left ht1 hE).trans_eq (mul_one E))
  have hdelta : p₁ - p₀ ≤ 2 * (J : ℝ) * Real.sqrt E := by
    have h := sub_le_two_mul_norm_sub_of_antilipschitz_loop hInv hp hshort
    simp only [Function.Periodic.lift_coe] at h
    rw [← ha₀, ← ha₁, norm_sub_rev] at h
    exact h.trans (mul_le_mul_of_nonneg_left (haosc 1 (by norm_num)) (by positivity))
  have hdelta0 : 0 ≤ p₁ - p₀ := sub_nonneg.mpr hp
  have hbenergy : (∫ t in Icc (0 : ℝ) 1, ‖deriv b t‖ ^ 2) ≤
      4 * (KΓ : ℝ) ^ 2 * (J : ℝ) ^ 2 * E := by
    have h := integral_deriv_sq_le_lipschitz_sq hb
    have hs := pow_le_pow_left₀ hdelta0 hdelta 2
    have hsqrt := Real.sq_sqrt hE
    have hmul := mul_le_mul_of_nonneg_left hs (sq_nonneg (KΓ : ℝ))
    simp only [NNReal.coe_mul, Real.coe_nnabs, abs_of_nonneg hdelta0, mul_pow] at h
    apply h.trans
    convert hmul using 1
    simp only [mul_pow, hsqrt]
    ring
  let C : ℝ := 1 + 2 * (KΓ : ℝ) * (J : ℝ)
  have hC : 1 ≤ C := le_add_of_nonneg_right (by positivity)
  have haBall : MapsTo a (Icc (0 : ℝ) 1) (Metric.closedBall (a 0) (C * Real.sqrt E)) := by
    intro t ht
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (haosc t ht).trans (by nlinarith [Real.sqrt_nonneg E])
  have hbBall : MapsTo b (Icc (0 : ℝ) 1) (Metric.closedBall (a 0) (C * Real.sqrt E)) := by
    intro t ht
    rw [Metric.mem_closedBall, dist_eq_norm, ha₀]
    have hpar : |((1 - t) * p₀ + t * p₁) - p₁| ≤ p₁ - p₀ := by
      have heq : ((1 - t) * p₀ + t * p₁) - p₁ = -(1 - t) * (p₁ - p₀) := by ring
      rw [heq, abs_mul, abs_neg, abs_of_nonneg (by linarith [ht.2]),
        abs_of_nonneg hdelta0]
      nlinarith [mul_nonneg ht.1 hdelta0]
    have hn := hΓ.dist_le_mul ((1 - t) * p₀ + t * p₁) p₁
    rw [dist_eq_norm, Real.dist_eq] at hn
    change ‖Γ ((1 - t) * p₀ + t * p₁) - Γ p₁‖ ≤ C * Real.sqrt E
    exact hn.trans ((mul_le_mul_of_nonneg_left hpar KΓ.coe_nonneg).trans
      ((mul_le_mul_of_nonneg_left hdelta KΓ.coe_nonneg).trans (by
        dsimp [C]
        nlinarith [Real.sqrt_nonneg E])))
  have hjoined (t : ℝ) : ‖joinedLoop a b t - a 0‖ ≤ C * Real.sqrt E := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using
      mapsTo_joinedLoop haBall hbBall (mem_univ t)
  have hjlip := joinedLoop_lipschitz ha hb hb₀.symm hb₁
  have hjenergy : (∫ t in Icc (0 : ℝ) 1, ‖deriv (joinedLoop a b) t‖ ^ 2) ≤
      (2 + 8 * (KΓ : ℝ) ^ 2 * (J : ℝ) ^ 2) * E := by
    rw [integral_deriv_joinedLoop_sq ha hb hb₀.symm hb₁]
    change 2 * E + 2 * (∫ t in Icc (0 : ℝ) 1, ‖deriv b t‖ ^ 2) ≤ _
    nlinarith [hbenergy]
  refine ⟨hb₀, hb₁, hb, hdelta, hbenergy, hjenergy, hjoined, ?_⟩
  have hgi : IntegrableOn (fun t => ‖joinedLoop a b t - a 0‖ ^ 2) (Icc (0 : ℝ) 1) :=
    ((hjlip.continuous.sub continuous_const).norm.pow 2).integrableOn_Icc
  have hbound (t : ℝ) : ‖joinedLoop a b t - a 0‖ ^ 2 ≤ C ^ 2 * E := by
    have hs := pow_le_pow_left₀ (norm_nonneg _) (hjoined t) 2
    simpa only [mul_pow, Real.sq_sqrt hE] using hs
  have hi := integral_mono_ae hgi (integrableOn_const (C := C ^ 2 * E) (by simp))
    (Eventually.of_forall hbound)
  simpa only [setIntegral_const, Measure.real, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
    ENNReal.toReal_one, one_smul] using hi

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] in
theorem mapsTo_joinedLoop_affine_arc
    {a Γ : ℝ → F} {p₀ p₁ : ℝ} {S : Set F}
    (ha : MapsTo a (Icc (0 : ℝ) 1) S) (hΓ : range Γ ⊆ S) :
    MapsTo (joinedLoop a (fun t => Γ ((1 - t) * p₀ + t * p₁))) univ S :=
  mapsTo_joinedLoop ha (fun _ _ => hΓ (mem_range_self _))

end DifferentialGeometry.Analysis

end

noncomputable section

open Set MeasureTheory

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integral_deriv_affine_interval_sq (f : ℝ → F) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in Icc (0 : ℝ) 1, ‖deriv (fun s => f (a + (b - a) * s)) t‖ ^ 2) =
      (b - a) * ∫ t in Icc a b, ‖deriv f t‖ ^ 2 := by
  have hder (t : ℝ) : deriv (fun s => f (a + (b - a) * s)) t =
      (b - a) • deriv f (a + (b - a) * t) := by
    change deriv (fun s => (fun x => f (a + x)) ((b - a) * s)) t = _
    rw [deriv_comp_mul_left (b - a) (fun x => f (a + x)) t, deriv_comp_const_add]
  simp_rw [hder, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul]
  have hint := intervalIntegral.smul_integral_comp_add_mul
    (a := (0 : ℝ)) (b := 1) (fun t => ‖deriv f t‖ ^ 2) (b - a) a
  have hright : a + (b - a) * 1 = b := by ring
  simp only [mul_zero, add_zero, hright, smul_eq_mul] at hint
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← integral_Icc_eq_integral_Ioc] at hint
  calc
    (b - a) ^ 2 * (∫ t in Icc (0 : ℝ) 1, ‖deriv f (a + (b - a) * t)‖ ^ 2) =
        (b - a) * ((b - a) * ∫ t in Icc (0 : ℝ) 1,
          ‖deriv f (a + (b - a) * t)‖ ^ 2) := by ring
    _ = _ := by rw [hint]

end DifferentialGeometry.Analysis

end
