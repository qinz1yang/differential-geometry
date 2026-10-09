/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.CurveAbsoluteContinuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def differenceQuotient (g : ℝ → E) (h t : ℝ) : E := h⁻¹ • (g (t + h) - g t)

omit [CompleteSpace E] in
theorem continuous_differenceQuotient {g : ℝ → E} (hg : Continuous g) (h : ℝ) :
    Continuous (differenceQuotient g h) :=
  (hg.comp (continuous_id.add continuous_const) |>.sub hg).const_smul _

theorem tendsto_integral_differenceQuotient {g : ℝ → E} (hg : Continuous g) (a b : ℝ) :
    Tendsto (fun h => ∫ t in a..b, differenceQuotient g h t)
      (𝓝[>] 0) (𝓝 (g b - g a)) := by
  have hprim (x : ℝ) :
      HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, g t) (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      (hg.stronglyMeasurableAtFilter volume _) hg.continuousAt
  have hlim := (hprim b).tendsto_slope_zero_right.sub (hprim a).tendsto_slope_zero_right
  convert hlim using 1
  ext h
  rw [← smul_sub]
  simp only [differenceQuotient, intervalIntegral.integral_smul]
  congr 1
  have hshift : Continuous (fun t : ℝ => g (t + h)) :=
    hg.comp (continuous_id.add continuous_const)
  rw [intervalIntegral.integral_sub
      (hshift.intervalIntegrable (μ := volume) a b)
      (hg.intervalIntegrable a b), intervalIntegral.integral_comp_add_right]
  rw [intervalIntegral.integral_interval_sub_left (hg.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _),
    intervalIntegral.integral_interval_sub_left (hg.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)]
  exact intervalIntegral.integral_interval_sub_interval_comm'
    (hg.intervalIntegrable (μ := volume) _ _) (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)

theorem le_mul_sq_add_inv (q : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    q ≤ κ * q ^ 2 + κ⁻¹ := by
  have hs := sq_nonneg (κ * q - 1)
  have hi : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ.ne'
  nlinarith [sq_nonneg (κ * q)]

omit [CompleteSpace E] in
theorem sum_norm_integral_le_energy {d : ℝ → E} (hd : Continuous d)
    {a b κ : ℝ} (hκ : 0 < κ) {J : ℕ × (ℕ → ℝ × ℝ)}
    (hJ : J ∈ AbsolutelyContinuousOnInterval.disjWithin a b) :
    (∑ i ∈ Finset.range J.1, ‖∫ t in (J.2 i).1..(J.2 i).2, d t‖) ≤
      κ * (∫ t in uIoc a b, ‖d t‖ ^ 2) +
        κ⁻¹ * (∑ i ∈ Finset.range J.1, dist (J.2 i).1 (J.2 i).2) := by
  have hsq : Continuous (fun t => ‖d t‖ ^ 2) := hd.norm.pow 2
  have hsum :
      (∑ i ∈ Finset.range J.1, ∫ t in uIoc (J.2 i).1 (J.2 i).2, ‖d t‖ ^ 2) ≤
        ∫ t in uIoc a b, ‖d t‖ ^ 2 := by
    rw [← integral_biUnion_finset (Finset.range J.1)
      (fun _ _ => measurableSet_uIoc) hJ.2
      (fun _ _ => (hsq.intervalIntegrable _ _).def')]
    apply setIntegral_mono_set (hsq.intervalIntegrable a b).def'
      (Eventually.of_forall (fun _ => sq_nonneg _))
    exact Eventually.of_forall
      (AbsolutelyContinuousOnInterval.biUnion_uIoc_subset_of_mem_disjWithin hJ)
  calc
    _ ≤ ∑ i ∈ Finset.range J.1,
        (κ * (∫ t in uIoc (J.2 i).1 (J.2 i).2, ‖d t‖ ^ 2) +
          κ⁻¹ * dist (J.2 i).1 (J.2 i).2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
      have hc : IntegrableOn (fun _ : ℝ => κ⁻¹) (uIoc (J.2 i).1 (J.2 i).2) volume :=
        integrableOn_const (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
      have hm := integral_mono_ae
        (hd.norm.intervalIntegrable (μ := volume) (J.2 i).1 (J.2 i).2).def'
        (((hsq.intervalIntegrable (J.2 i).1 (J.2 i).2).def'.const_mul κ).add
          hc)
        (Eventually.of_forall (fun t => le_mul_sq_add_inv ‖d t‖ hκ))
      simpa only [Pi.add_apply, integral_add
        ((hsq.intervalIntegrable (J.2 i).1 (J.2 i).2).def'.const_mul κ)
          hc,
        integral_const_mul, integral_const, smul_eq_mul, Measure.real,
        Measure.restrict_apply_univ,
        Real.volume_uIoc, ENNReal.toReal_ofReal (abs_nonneg _),
        Real.dist_eq, abs_sub_comm, mul_comm κ⁻¹] using hm
    _ = κ * (∑ i ∈ Finset.range J.1, ∫ t in uIoc (J.2 i).1 (J.2 i).2, ‖d t‖ ^ 2) +
        κ⁻¹ * (∑ i ∈ Finset.range J.1, dist (J.2 i).1 (J.2 i).2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hsum hκ.le) le_rfl

theorem absolutelyContinuousOnInterval_of_differenceQuotient_bound
    {g : ℝ → E} (hg : Continuous g) {a b C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ h in 𝓝[>] (0 : ℝ),
      (∫ t in uIoc a b, ‖differenceQuotient g h t‖ ^ 2) ≤ C) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  let κ := ε / (4 * (C + 1))
  have hκ : 0 < κ := div_pos hε (by positivity)
  have hκC : κ * C < ε / 2 := by
    have hval : κ * (4 * (C + 1)) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  refine ⟨κ * ε / 2, by positivity, fun J hJ hlen => ?_⟩
  have hlim : Tendsto
      (fun h => ∑ i ∈ Finset.range J.1,
        ‖∫ t in (J.2 i).1..(J.2 i).2, differenceQuotient g h t‖)
      (𝓝[>] 0) (𝓝 (∑ i ∈ Finset.range J.1, dist (g (J.2 i).1) (g (J.2 i).2))) := by
    convert tendsto_finsetSum (Finset.range J.1)
      (fun i _ => (tendsto_integral_differenceQuotient hg (J.2 i).1 (J.2 i).2).norm) using 1
    simp only [dist_eq_norm, norm_sub_rev]
  have hb :
      (∑ i ∈ Finset.range J.1, dist (g (J.2 i).1) (g (J.2 i).2)) ≤
        κ * C + κ⁻¹ * (∑ i ∈ Finset.range J.1, dist (J.2 i).1 (J.2 i).2) := by
    apply le_of_tendsto hlim
    filter_upwards [hbound] with h hh
    exact (sum_norm_integral_le_energy (continuous_differenceQuotient hg h) hκ hJ).trans
      (add_le_add (mul_le_mul_of_nonneg_left hh hκ.le) le_rfl)
  have hsmall :
      κ⁻¹ * (∑ i ∈ Finset.range J.1, dist (J.2 i).1 (J.2 i).2) < ε / 2 := by
    calc
      _ < κ⁻¹ * (κ * ε / 2) := mul_lt_mul_of_pos_left hlen (inv_pos.mpr hκ)
      _ = ε / 2 := by field_simp
  linarith

theorem absolutelyContinuousOnInterval_lipschitz_comp
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {g : ℝ → X} {a b : ℝ} (hg : AbsolutelyContinuousOnInterval g a b)
    {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    AbsolutelyContinuousOnInterval (fun t => f (g t)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  have hK : 0 < (K : ℝ) + 1 := by positivity
  obtain ⟨δ, hδ, hbound⟩ := hg (ε / ((K : ℝ) + 1)) (div_pos hε hK)
  refine ⟨δ, hδ, fun J hJ hlen => ?_⟩
  have hb := hbound J hJ hlen
  calc
    _ ≤ (K : ℝ) * (∑ i ∈ Finset.range J.1, dist (g (J.2 i).1) (g (J.2 i).2)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hf.dist_le_mul _ _
    _ ≤ ((K : ℝ) + 1) *
        (∑ i ∈ Finset.range J.1, dist (g (J.2 i).1) (g (J.2 i).2)) := by
      gcongr
      exact le_add_of_nonneg_right zero_le_one
    _ < ((K : ℝ) + 1) * (ε / ((K : ℝ) + 1)) := mul_lt_mul_of_pos_left hb hK
    _ = ε := mul_div_cancel₀ _ hK.ne'

omit [CompleteSpace E] in
theorem dist_le_lintegral_derivative {g g' : ℝ → E} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hd : ∀ᵐ t ∂volume, HasDerivAt g (g' t) t) :
    ENNReal.ofReal (dist (g a) (g b)) ≤
      ∫⁻ t in uIoc a b, ENNReal.ofReal ‖g' t‖ := by
  obtain ⟨ℓ, hℓnorm, hℓ⟩ := exists_dual_vector'' ℝ (g b - g a)
  have hac := absolutelyContinuousOnInterval_lipschitz_comp hg ℓ.lipschitzWith
  have hderiv : ∀ᵐ t ∂volume, deriv (fun u => ℓ (g u)) t = ℓ (g' t) :=
    hd.mono fun t ht => (ℓ.hasFDerivAt.comp_hasDerivAt t ht).deriv
  have hinc : dist (g a) (g b) ≤
      ∫ t in uIoc a b, ‖deriv (fun u => ℓ (g u)) t‖ := by
    calc
      _ = ∫ t in a..b, deriv (fun u => ℓ (g u)) t := by
        rw [hac.integral_deriv_eq_sub, ← map_sub, hℓ, dist_eq_norm, norm_sub_rev]
        rfl
      _ ≤ ‖∫ t in a..b, deriv (fun u => ℓ (g u)) t‖ := le_abs_self _
      _ ≤ _ := intervalIntegral.norm_integral_le_integral_norm_uIoc
  apply (ENNReal.ofReal_le_ofReal hinc).trans
  rw [ofReal_integral_eq_lintegral_ofReal hac.intervalIntegrable_deriv.def'.norm
    (Eventually.of_forall (fun _ => norm_nonneg _))]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_of_ae hderiv] with t ht
  rw [ht]
  apply ENNReal.ofReal_le_ofReal
  exact (ℓ.le_opNorm (g' t)).trans (mul_le_of_le_one_left (norm_nonneg _) hℓnorm)

theorem lintegral_pow_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {u : X → ℝ≥0∞} (hu : AEMeasurable u μ) {m : ℕ} (hm : 1 ≤ m) :
    (∫⁻ x, u x ∂μ) ^ m ≤ (∫⁻ x, (u x) ^ m ∂μ) * (μ univ) ^ (m - 1) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hp : 0 ≤ 1 / (m : ℝ) := by positivity
  have hq : 0 ≤ ((m : ℝ) - 1) / (m : ℝ) := by
    apply div_nonneg _ hm0.le
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hpq : 1 / (m : ℝ) + ((m : ℝ) - 1) / (m : ℝ) = 1 := by field_simp; ring
  have h1 : (1 / (m : ℝ)) * (m : ℝ) = 1 := by field_simp
  have h2 : (((m : ℝ) - 1) / (m : ℝ)) * (m : ℝ) = ((m - 1 : ℕ) : ℝ) := by
    rw [div_mul_cancel₀ _ hm0.ne', Nat.cast_sub hm, Nat.cast_one]
  have hh := ENNReal.lintegral_mul_norm_pow_le
    (hu.pow_const m) (aemeasurable_const (b := (1 : ℝ≥0∞))) hp hq hpq
  have hleft : (fun x => (u x ^ m) ^ (1 / (m : ℝ)) * (1 : ℝ≥0∞) ^
      (((m : ℝ) - 1) / (m : ℝ))) = u := by
    funext x
    rw [ENNReal.one_rpow, mul_one, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    have : (m : ℝ) * (1 / (m : ℝ)) = 1 := by field_simp
    rw [this, ENNReal.rpow_one]
  rw [hleft, lintegral_const] at hh
  simp only [one_mul] at hh
  have hpow :
      (∫⁻ x, u x ∂μ) ^ m ≤
        ((∫⁻ x, u x ^ m ∂μ) ^ (1 / (m : ℝ)) *
          (μ univ) ^ (((m : ℝ) - 1) / (m : ℝ))) ^ m := by
    gcongr
  simpa only [mul_pow, ← ENNReal.rpow_mul_natCast, h1, h2, ENNReal.rpow_one,
    ENNReal.rpow_natCast] using hpow

omit [CompleteSpace E] in
theorem dist_pow_le_lintegral_derivative_pow {g g' : ℝ → E} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hd : ∀ᵐ t ∂volume, HasDerivAt g (g' t) t)
    (hmderiv : Measurable (fun t => ‖g' t‖)) {m : ℕ} (hm : 1 ≤ m) :
    ENNReal.ofReal (dist (g a) (g b) ^ m) ≤
      ENNReal.ofReal (|b - a| ^ (m - 1)) *
        ∫⁻ t in uIoc a b, ENNReal.ofReal (‖g' t‖ ^ m) := by
  have hi := dist_le_lintegral_derivative hg hd
  have hh := lintegral_pow_le (volume.restrict (uIoc a b))
    hmderiv.ennreal_ofReal.aemeasurable hm
  rw [ENNReal.ofReal_pow dist_nonneg]
  calc
    _ ≤ (∫⁻ t in uIoc a b, ENNReal.ofReal ‖g' t‖) ^ m := by gcongr
    _ ≤ _ := by
      simpa only [← ENNReal.ofReal_pow (norm_nonneg _), Measure.restrict_apply_univ,
        Real.volume_uIoc, ← ENNReal.ofReal_pow (abs_nonneg _), mul_comm] using hh

end DifferentialGeometry.CurveAbsoluteContinuity
