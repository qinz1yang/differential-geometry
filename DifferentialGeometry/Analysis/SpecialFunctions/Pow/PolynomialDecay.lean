import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set Filter Real
open scoped Topology ENNReal NNReal

namespace Real

theorem tendsto_rpow_mul_inv_polynomial {m : ℕ} {b C : ℝ} (hb : (m : ℝ) < b) :
    Tendsto (fun ε : ℝ => ε ^ b * (1 + C / ε) ^ m) (𝓝[>] 0) (𝓝 0) := by
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h := (hid.rpow_const_nhds_zero (sub_pos.mpr hb)).mul ((hid.add_const C).pow m)
  simp only [zero_add, zero_mul] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0 < ε at hε
  rw [Real.rpow_sub hε, Real.rpow_natCast]
  have he : 1 + C / ε = (ε + C) / ε := by field_simp
  rw [he, div_pow]
  ring

end Real
