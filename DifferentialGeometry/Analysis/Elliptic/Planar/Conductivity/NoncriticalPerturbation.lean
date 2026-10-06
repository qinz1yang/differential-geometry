import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)

/-- A fixed uniform half-Hölder bound turns a sufficiently small squared error
from a unit vector into nonvanishing at the center. -/
theorem exists_l2_threshold_for_nonzero_at_center_of_uniform_holder
    (R : ℝ) (hR : 0 < R) (H : ℝ≥0) (e : V) (he : ‖e‖ = 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ G : V → V,
      (∀ x ∈ Metric.ball (0 : V) R, ∀ y ∈ Metric.ball (0 : V) R,
        ‖G x - G y‖ ≤ (H : ℝ) * ‖x - y‖ ^ (1 / 2 : ℝ)) →
      IntegrableOn (fun x => ‖G x - e‖ ^ 2) (Metric.ball (0 : V) R) volume →
      (∫ x in Metric.ball (0 : V) R, ‖G x - e‖ ^ 2) < ε →
      G 0 ≠ 0 := by
  have hmod : Continuous (fun x : V => (H : ℝ) * ‖x‖ ^ (1 / 2 : ℝ)) :=
    continuous_const.mul (continuous_norm.rpow_const (fun _ => Or.inr (by norm_num)))
  have hcenter : (H : ℝ) * ‖(0 : V)‖ ^ (1 / 2 : ℝ) < 1 / 2 := by
    norm_num
  have hsmallN : ∀ᶠ x : V in 𝓝 0, (H : ℝ) * ‖x‖ ^ (1 / 2 : ℝ) < 1 / 2 :=
    hmod.continuousAt.eventually (gt_mem_nhds hcenter)
  obtain ⟨r, hr, hrsmall⟩ := Metric.mem_nhds_iff.mp hsmallN
  let δ : ℝ := min r R / 2
  have hδ : 0 < δ := half_pos (lt_min hr hR)
  have hδr : δ ≤ r := (half_le_self (le_of_lt (lt_min hr hR))).trans (min_le_left _ _)
  have hδR : δ ≤ R := (half_le_self (le_of_lt (lt_min hr hR))).trans (min_le_right _ _)
  have hsubset : ball (0 : V) δ ⊆ ball 0 R := ball_subset_ball hδR
  have hfinite : volume (ball (0 : V) δ) ≠ ∞ := measure_ball_lt_top.ne
  have hvolume : 0 < volume.real (ball (0 : V) δ) := by
    change 0 < (volume (ball (0 : V) δ)).toReal
    exact ENNReal.toReal_pos
      (isOpen_ball.measure_pos volume ⟨0, mem_ball_self hδ⟩).ne' hfinite
  refine ⟨(1 / 4 : ℝ) * volume.real (ball (0 : V) δ), by positivity, ?_⟩
  intro G hHolder hInt hError hzero
  have hlower : ∀ x ∈ ball (0 : V) δ, (1 / 4 : ℝ) ≤ ‖G x - e‖ ^ 2 := by
    intro x hx
    have hG := hHolder x (hsubset hx) 0 (mem_ball_self hR)
    simp only [hzero, sub_zero] at hG
    have hGsmall : ‖G x‖ < 1 / 2 :=
      lt_of_le_of_lt hG (hrsmall ((ball_subset_ball hδr) hx))
    have htriangle : ‖e‖ ≤ ‖G x - e‖ + ‖G x‖ := by
      calc
        ‖e‖ = ‖e - G x + G x‖ := by rw [sub_add_cancel]
        _ ≤ ‖e - G x‖ + ‖G x‖ := norm_add_le _ _
        _ = ‖G x - e‖ + ‖G x‖ := by rw [norm_sub_rev e (G x)]
    rw [he] at htriangle
    have herr : (1 / 2 : ℝ) ≤ ‖G x - e‖ := by linarith
    nlinarith [sq_nonneg (‖G x - e‖ - (1 / 2 : ℝ))]
  have hinner : (1 / 4 : ℝ) * volume.real (ball (0 : V) δ) ≤
      ∫ x in ball (0 : V) δ, ‖G x - e‖ ^ 2 :=
    setIntegral_ge_of_const_le_real measurableSet_ball hfinite hlower (hInt.mono_set hsubset)
  have hmono : (∫ x in ball (0 : V) δ, ‖G x - e‖ ^ 2) ≤
      ∫ x in ball (0 : V) R, ‖G x - e‖ ^ 2 :=
    setIntegral_mono_set hInt (Filter.Eventually.of_forall (fun x => sq_nonneg ‖G x - e‖))
      (Filter.Eventually.of_forall (fun _ hx => hsubset hx))
  exact (not_lt_of_ge (hinner.trans hmono)) hError

end DifferentialGeometry.Analysis
