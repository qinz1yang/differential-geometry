import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace GC.LongTime.Ch12

/-- The numerical room in the KL82 volume transfer. The radius loss and the
volume growth are both charged to the actual elapsed time. The constant is
uniform in `w` and `r0`; only the endpoint Ricci coefficient `C` enters. -/
theorem exists_volume_transfer_margin_CX11 (C : ℝ) :
    ∃ τ₁ : ℝ, 0 < τ₁ ∧ τ₁ ≤ 1 ∧ ∀ τ : ℝ, 0 ≤ τ → τ ≤ τ₁ →
      0 < 1 / 4 - 16 * Real.sqrt (C / 3) * Real.sqrt τ ∧
      (1 / 4 : ℝ) ^ 3 / 10 ≤ Real.exp (-(2 + 6 * τ)) *
        (1 / 4 - 16 * Real.sqrt (C / 3) * Real.sqrt τ) ^ 3 := by
  let r : ℝ → ℝ := fun τ => 1 / 4 - 16 * Real.sqrt (C / 3) * Real.sqrt τ
  let f : ℝ → ℝ := fun τ => Real.exp (-(2 + 6 * τ)) * (r τ) ^ 3
  have hr : Continuous r := by dsimp [r]; fun_prop
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hE : Real.exp 2 < 10 := by
    have h1 := Real.exp_one_lt_three
    have hp := Real.exp_pos 1
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [he]
    nlinarith
  have hinv : Real.exp (-2) * Real.exp 2 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hneg : (1 / 10 : ℝ) < Real.exp (-2) := by
    nlinarith [mul_pos (Real.exp_pos (-2)) (sub_pos.mpr hE)]
  have hbase : (1 / 4 : ℝ) ^ 3 / 10 < f 0 := by
    norm_num [f, r]
    nlinarith
  have hevent : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 < r τ ∧ (1 / 4 : ℝ) ^ 3 / 10 < f τ :=
    (hr.continuousAt.eventually (Ioi_mem_nhds (by norm_num [r]))).and
      (hf.continuousAt.eventually (Ioi_mem_nhds hbase))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨min (ε / 2) 1, lt_min (by positivity) one_pos, min_le_right _ _, ?_⟩
  intro τ hτ hτ₁
  have hτε : dist τ 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hτ]
    have hh := hτ₁.trans (min_le_left (ε / 2) 1)
    linarith
  exact ⟨(hball hτε).1, (hball hτε).2.le⟩

end GC.LongTime.Ch12
