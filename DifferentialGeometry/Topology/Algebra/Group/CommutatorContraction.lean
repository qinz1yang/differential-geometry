/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

noncomputable section

open Set Filter
open scoped Topology commutatorElement

namespace DifferentialGeometry.Zassenhaus

section Generators

variable {G : Type*} [Group G]

theorem mem_upperCentralSeries_succ_of_generators (S : Set G)
    (hgen : Subgroup.closure S = ⊤) {x : G} {k : ℕ}
    (hx : ∀ s ∈ S, ⁅x, s⁆ ∈ Subgroup.upperCentralSeries G k) :
    x ∈ Subgroup.upperCentralSeries G (k + 1) := by
  apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
  intro y
  have hy : y ∈ Subgroup.closure S := by rw [hgen]; trivial
  refine Subgroup.closure_induction (fun s hs => hx s hs) ?_ ?_ ?_ hy
  · simp only [commutatorElement_one_right]
    exact Subgroup.one_mem _
  · intro a b _ _ ha hb
    rw [commutatorElement_mul_right_eq_mul_conj]
    simpa only [mul_assoc] using
      (Subgroup.upperCentralSeries G k).mul_mem ha
        ((inferInstance : (Subgroup.upperCentralSeries G k).Normal).conj_mem _ hb a)
  · intro a _ ha
    rw [commutatorElement_inv_right]
    simpa only [commutatorElement_inv, inv_inv] using
      (inferInstance : (Subgroup.upperCentralSeries G k).Normal).conj_mem
        ⁅x, a⁆⁻¹ ((Subgroup.upperCentralSeries G k).inv_mem ha) a⁻¹

theorem isNilpotent_of_contraction (d : G → ℝ) (S : Set G)
    (hgen : Subgroup.closure S = ⊤) {r : ℝ} (hr : 0 < r)
    (hS : ∀ s ∈ S, d s ≤ r)
    (hcomm : ∀ a b, d a ≤ r → d b ≤ r → d ⁅a, b⁆ ≤ (1 / 2) * d a)
    (hsep : ∃ ε : ℝ, 0 < ε ∧ ∀ a, d a < ε → a = 1) :
    Group.IsNilpotent G := by
  obtain ⟨ε, hε, hsep⟩ := hsep
  have hlim : Tendsto (fun N : ℕ => r * (1 / 2 : ℝ) ^ N) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul r
  obtain ⟨N, hN⟩ := (hlim.eventually (isOpen_Iio.mem_nhds hε)).exists
  have hdepth : ∀ j : ℕ, j ≤ N → ∀ a : G, d a ≤ r * (1 / 2 : ℝ) ^ (N - j) →
      a ∈ Subgroup.upperCentralSeries G j := by
    intro j
    induction j with
    | zero =>
      intro _ a ha
      apply Subgroup.mem_bot.mpr
      exact hsep a (ha.trans_lt (by simpa only [Nat.sub_zero] using hN))
    | succ j ih =>
      intro hj a ha
      apply mem_upperCentralSeries_succ_of_generators S hgen
      intro s hs
      apply ih (by omega)
      have haR : d a ≤ r := ha.trans (by
        calc
          r * (1 / 2 : ℝ) ^ (N - (j + 1)) ≤ r * 1 := by
            gcongr
            exact pow_le_one₀ (by norm_num) (by norm_num)
          _ = r := mul_one r)
      calc
        d ⁅a, s⁆ ≤ (1 / 2) * d a := hcomm a s haR (hS s hs)
        _ ≤ (1 / 2) * (r * (1 / 2 : ℝ) ^ (N - (j + 1))) :=
          mul_le_mul_of_nonneg_left ha (by norm_num)
        _ = r * (1 / 2 : ℝ) ^ (N - j) := by
          rw [show N - j = (N - (j + 1)) + 1 by omega, pow_succ]
          ring
  apply Group.IsNilpotent.mk
  refine ⟨N, top_unique ?_⟩
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro s hs
  exact hdepth N le_rfl s (by simpa only [Nat.sub_self, pow_zero, mul_one] using hS s hs)

end Generators

end DifferentialGeometry.Zassenhaus
