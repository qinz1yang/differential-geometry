/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Conformal.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Normed.Module.RCLike.Real

noncomputable section

open Set Filter Metric
open scoped Topology

namespace DifferentialGeometry.Analysis

private theorem not_constant_of_conformalAt
    {f : ℂ → ℂ} {D : Set ℂ} {x : ℂ}
    (hD : IsOpen D) (hx : x ∈ D) (hconf : ConformalAt f x) :
    ¬ ∃ w, ∀ z ∈ D, f z = w := by
  rintro ⟨w, hw⟩
  have heq : f =ᶠ[𝓝 x] (fun _ : ℂ => w) := by
    filter_upwards [hD.mem_nhds hx] with z hz
    exact hw z hz
  have hne : fderiv ℝ f x ≠ 0 :=
    (conformalAt_iff_isConformalMap_fderiv.mp hconf).ne_zero
  apply hne
  simpa only [fderiv_const_apply] using heq.fderiv_eq (𝕜 := ℝ)

private theorem norm_lt_of_analyticOnNhd_of_not_constant_of_norm_le
    {f : ℂ → ℂ} {D : Set ℂ} {r : ℝ}
    (hD : IsOpen D) (hconn : IsPreconnected D) (han : AnalyticOnNhd ℂ f D)
    (hnc : ¬ ∃ w, ∀ z ∈ D, f z = w) (hbound : ∀ z ∈ D, ‖f z‖ ≤ r) :
    ∀ z ∈ D, ‖f z‖ < r := by
  rcases han.is_constant_or_isOpen hconn with hc | hopen
  · exact (hnc hc).elim
  · have hsubset : f '' D ⊆ closedBall (0 : ℂ) r := by
      rintro _ ⟨z, hz, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hbound z hz
    have hinside : f '' D ⊆ interior (closedBall (0 : ℂ) r) :=
      interior_maximal hsubset (hopen D Subset.rfl hD)
    intro z hz
    have hzinside := hinside ⟨z, hz, rfl⟩
    rw [interior_closedBall'] at hzinside
    simpa only [Metric.mem_ball, dist_zero_right] using hzinside

theorem norm_lt_of_analyticOnNhd_or_conj_of_conformalAt_of_norm_le
    {f : ℂ → ℂ} {D : Set ℂ} {x : ℂ} {r : ℝ}
    (hD : IsOpen D) (hconn : IsPreconnected D)
    (han : AnalyticOnNhd ℂ f D ∨
      AnalyticOnNhd ℂ (fun z => Complex.conjCLE (f z)) D)
    (hx : x ∈ D) (hconf : ConformalAt f x)
    (hbound : ∀ z ∈ D, ‖f z‖ ≤ r) :
    ∀ z ∈ D, ‖f z‖ < r := by
  have hnc := not_constant_of_conformalAt hD hx hconf
  rcases han with han | han
  · exact norm_lt_of_analyticOnNhd_of_not_constant_of_norm_le hD hconn han hnc hbound
  · have hncConj : ¬ ∃ w, ∀ z ∈ D, Complex.conjCLE (f z) = w := by
      rintro ⟨w, hw⟩
      apply hnc
      refine ⟨f x, ?_⟩
      intro z hz
      exact EquivLike.injective Complex.conjCLE ((hw z hz).trans (hw x hx).symm)
    have hboundConj : ∀ z ∈ D, ‖Complex.conjCLE (f z)‖ ≤ r := by
      intro z hz
      simpa only [Complex.conjCLE_apply, Complex.norm_conj] using hbound z hz
    have hstrict := norm_lt_of_analyticOnNhd_of_not_constant_of_norm_le
      hD hconn han hncConj hboundConj
    intro z hz
    simpa only [Complex.conjCLE_apply, Complex.norm_conj] using hstrict z hz

end DifferentialGeometry.Analysis
