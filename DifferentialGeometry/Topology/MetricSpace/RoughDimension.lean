import DifferentialGeometry.Analysis.SpecialFunctions.Pow.PolynomialDecay
import DifferentialGeometry.Topology.MetricSpace.FinitePacking
import Mathlib.Basic.Real.ENatENNReal
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open Set Filter Real
open scoped Topology ENNReal NNReal

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem tendsto_weighted_finitePackingNumber_of_polynomial_bound
    {S : Set X} {m : ℕ} {C b : ℝ} (hC : 0 ≤ C) (hb : (m : ℝ) < b)
    (hpack : ∀ ε : ℝ, 0 < ε →
      finitePackingNumber ε S ≤ (⌊(1 + C / ε) ^ m⌋₊ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ENNReal.ofReal (ε ^ b) * (finitePackingNumber ε S : ℝ≥0∞))
      (𝓝[>] 0) (𝓝 0) := by
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (Real.tendsto_rpow_mul_inv_polynomial (C := C) hb)
  simp only [ENNReal.ofReal_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0 < ε at hε
    have hpoly : 0 ≤ (1 + C / ε) ^ m := by positivity
    have hfloor := ENNReal.ofReal_le_ofReal (Nat.floor_le hpoly)
    simp only [ENNReal.ofReal_natCast] at hfloor
    have hbound : (finitePackingNumber ε S : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + C / ε) ^ m) :=
      (ENat.toENNReal_mono (hpack ε hε)).trans hfloor
    simp only [Function.comp_def]
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hε.le b)]
    exact mul_le_mul le_rfl hbound bot_le bot_le

noncomputable def roughVolume (a : ℝ) (S : Set X) : ℝ≥0∞ :=
  limsup (fun ε : ℝ => ENNReal.ofReal (ε ^ a) * (finitePackingNumber ε S : ℝ≥0∞)) (𝓝[>] 0)

noncomputable def roughDim (S : Set X) : ℝ≥0∞ :=
  ⨅ (a : ℝ≥0) (_ : roughVolume (a : ℝ) S = 0), (a : ℝ≥0∞)

theorem roughVolume_eq_zero_of_polynomial_bound
    {S : Set X} {m : ℕ} {C b : ℝ} (hC : 0 ≤ C) (hb : (m : ℝ) < b)
    (hpack : ∀ ε : ℝ, 0 < ε →
      finitePackingNumber ε S ≤ (⌊(1 + C / ε) ^ m⌋₊ : ℕ∞)) : roughVolume b S = 0 :=
  (tendsto_weighted_finitePackingNumber_of_polynomial_bound hC hb hpack).limsup_eq


theorem roughDim_le_of_polynomial_bound
    {S : Set X} {m : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (hpack : ∀ ε : ℝ, 0 < ε →
      finitePackingNumber ε S ≤ (⌊(1 + C / ε) ^ m⌋₊ : ℕ∞)) : roughDim S ≤ m := by
  apply le_of_forall_gt
  intro b hb
  obtain ⟨a, hma, hab⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hb
  have hma' : (m : ℝ) < (a : ℝ) := by exact_mod_cast hma
  have hv := roughVolume_eq_zero_of_polynomial_bound hC hma' hpack
  have hd : roughDim S ≤ (a : ℝ≥0∞) := by
    unfold roughDim
    exact iInf_le_of_le a (iInf_le_of_le hv le_rfl)
  exact hd.trans_lt hab


theorem finitePackingNumber_le_one_of_subsingleton {S : Set X} (hS : S.Subsingleton)
    (ε : ℝ) : finitePackingNumber ε S ≤ 1 := by
  apply finitePackingNumber_le_iff.mpr
  intro A hA _
  have hcard : A.card ≤ 1 := Finset.card_le_one.mpr (fun x hx y hy => hS (hA hx) (hA hy))
  exact_mod_cast hcard

theorem roughDim_eq_zero_of_subsingleton {S : Set X} (hS : S.Subsingleton) : roughDim S = 0 := by
  apply le_antisymm _ bot_le
  have hp (ε : ℝ) (_ : 0 < ε) :
      finitePackingNumber ε S ≤ (⌊(1 + (0 : ℝ) / ε) ^ (0 : ℕ)⌋₊ : ℕ∞) := by
    simpa using finitePackingNumber_le_one_of_subsingleton hS ε
  simpa using roughDim_le_of_polynomial_bound (m := 0) (C := 0) le_rfl hp

end Metric
