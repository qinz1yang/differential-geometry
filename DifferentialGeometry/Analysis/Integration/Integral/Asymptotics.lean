import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

theorem Asymptotics.IsLittleO.integral_smul_comp_smul
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure E}
    {f : E → F} {κ : E → ℝ} {n : ℕ}
    (hf : f =o[𝓝 (0 : E)] (fun z => ‖z‖ ^ n))
    (hκ : Bornology.IsBounded (Function.support κ))
    (hi : Integrable (fun z => ‖κ z‖ * ‖z‖ ^ n) μ) :
    (fun t : ℝ => ∫ z, κ z • f (t • z) ∂μ) =o[𝓝 0] (fun t => t ^ n) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  let I := ∫ z, ‖κ z‖ * ‖z‖ ^ n ∂μ
  have hI : 0 ≤ I := integral_nonneg (fun z => by positivity)
  let η := c / (I + 1)
  have hη : 0 < η := div_pos hc (by positivity)
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhds_iff.mp (hf.bound hη)
  obtain ⟨R, hR, hbound⟩ := hκ.exists_pos_norm_le
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (div_pos hδ hR)] with t ht
  have ht' : ‖t‖ < δ / R := by simpa only [Metric.mem_ball, dist_zero_right] using ht
  have hnorm (z : E) : ‖κ z • f (t • z)‖ ≤ (η * ‖t‖ ^ n) * (‖κ z‖ * ‖z‖ ^ n) := by
    by_cases hz : κ z = 0
    · simp only [hz, zero_smul, norm_zero, zero_mul, mul_zero, le_refl]
    have htz : t • z ∈ Metric.ball (0 : E) δ := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul]
      exact (mul_le_mul_of_nonneg_left (hbound z hz) (norm_nonneg t)).trans_lt
        ((lt_div_iff₀ hR).mp ht')
    have h := hsmall htz
    change ‖f (t • z)‖ ≤ η * ‖‖t • z‖ ^ n‖ at h
    rw [norm_pow, _root_.norm_norm, norm_smul, mul_pow] at h
    rw [norm_smul]
    calc
      ‖κ z‖ * ‖f (t • z)‖ ≤ ‖κ z‖ * (η * (‖t‖ ^ n * ‖z‖ ^ n)) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = _ := by ring
  have hb := norm_integral_le_of_norm_le (hi.const_mul (η * ‖t‖ ^ n)) (ae_of_all μ hnorm)
  rw [integral_const_mul] at hb
  change ‖∫ z, κ z • f (t • z) ∂μ‖ ≤ c * ‖t ^ n‖
  rw [norm_pow]
  calc
    _ ≤ (η * ‖t‖ ^ n) * I := hb
    _ ≤ c * ‖t‖ ^ n := by
      have hηI : η * I ≤ c := by
        have heq : η * (I + 1) = c := div_mul_cancel₀ c (by positivity : I + 1 ≠ 0)
        nlinarith
      nlinarith [pow_nonneg (norm_nonneg t) n]
