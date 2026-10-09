import DifferentialGeometry.Geometry.Comparison.EndpointHingeComparison
import DifferentialGeometry.Topology.MetricSpace.SegmentExtension
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false


open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem cosh_sum_le_of_adjacent_germs
    {X : Type*} [MetricSpace X] {κ T L h : ℝ} (hκ : 0 < κ) (hL : 0 < L) (hh : 0 < h)
    {u z : X} {β γminus γplus : ℝ → X}
    (hcmp : endpointHingeComparison κ z T) (hsum : L + h < T) (hβend : β L = z)
    (hβrad : ∀ s ∈ Ioc (0 : ℝ) L, dist u (β s) = s)
    (hβmin : ∀ s ∈ Ioc (0 : ℝ) L, ∀ t ∈ Ioc (0 : ℝ) L,
      dist (β s) (β t) = |s - t|)
    (hmrad : ∀ s ∈ Ioc (0 : ℝ) h, dist u (γminus s) = s)
    (hpmin : ∀ s ∈ Ioc (0 : ℝ) h, ∀ t ∈ Ioc (0 : ℝ) h,
      dist (γplus s) (γplus t) = |s - t|)
    (hprad : ∀ s ∈ Ioc (0 : ℝ) h, dist u (γplus s) = s)
    (hmmin : ∀ s ∈ Ioc (0 : ℝ) h, ∀ t ∈ Ioc (0 : ℝ) h,
      dist (γminus s) (γminus t) = |s - t|)
    (hopp : ∀ s ∈ Ioc (0 : ℝ) h, ∀ t ∈ Ioc (0 : ℝ) h,
      dist (γplus s) (γminus t) = s + t)
    (hlocal : ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ u ∈ Ω) :
    cosh (sqrt κ * dist z (γminus h)) + cosh (sqrt κ * dist z (γplus h)) ≤
      2 * cosh (sqrt κ * h) * cosh (sqrt κ * L) := by
  let A : Fin 3 → ℝ := ![h, L, h]
  let γ : Fin 3 → ℝ → X := ![γminus, β, γplus]
  have hA : ∀ j, 0 < A j := by intro j; fin_cases j <;> assumption
  have hrad : ∀ j, ∀ s ∈ Ioc (0 : ℝ) (A j), dist u (γ j s) = s := by
    intro j; fin_cases j
    · exact hmrad
    · exact hβrad
    · exact hprad
  have hmin : ∀ j, ∀ s ∈ Ioc (0 : ℝ) (A j), ∀ t ∈ Ioc (0 : ℝ) (A j),
      dist (γ j s) (γ j t) = |s - t| := by
    intro j; fin_cases j
    · exact hmmin
    · exact hβmin
    · exact hpmin
  obtain ⟨Ω, hΩ, hcomp, hu⟩ := hlocal
  have hang := germComparisonAngle_adjacent_sum_le_pi_of_local_fourPointComparison
    hκ.le hA hΩ hcomp hu hrad hmin 0 1 2 hopp
  change germComparisonAngle κ γminus β + germComparisonAngle κ β γplus ≤ Real.pi at hang
  rw [germComparisonAngle_comm κ γminus β] at hang
  have hm := hcmp u L h β γminus hL hh hsum hβend hβrad hmrad hβmin hmmin
  have hp := hcmp u L h β γplus hL hh hsum hβend hβrad hprad hβmin hpmin
  have hcos : 0 ≤ cos (comparisonAngleNegCurvature κ L h (dist z (γminus h))) +
      cos (comparisonAngleNegCurvature κ L h (dist z (γplus h))) := by
    have h := cos_le_cos_of_nonneg_of_le_pi
      (comparisonAngleNegCurvature_mem_Icc κ L h (dist z (γplus h))).1
      (by linarith [(comparisonAngleNegCurvature_mem_Icc κ L h (dist z (γminus h))).1] :
        Real.pi - comparisonAngleNegCurvature κ L h (dist z (γminus h)) ≤ Real.pi)
      (by linarith : comparisonAngleNegCurvature κ L h (dist z (γplus h)) ≤
        Real.pi - comparisonAngleNegCurvature κ L h (dist z (γminus h)))
    rw [cos_pi_sub] at h
    linarith
  have huz : dist u z = L := by simpa only [hβend] using hβrad L ⟨hL, le_rfl⟩
  have hum : dist u (γminus h) = h := hmrad h ⟨hh, le_rfl⟩
  have hup : dist u (γplus h) = h := hprad h ⟨hh, le_rfl⟩
  have hlom : |L - h| ≤ dist z (γminus h) := by
    simpa only [dist_comm z u, dist_comm (γminus h) u, huz, hum] using abs_dist_sub_le z (γminus h) u
  have hlop : |L - h| ≤ dist z (γplus h) := by
    simpa only [dist_comm z u, dist_comm (γplus h) u, huz, hup] using abs_dist_sub_le z (γplus h) u
  have hhim : dist z (γminus h) ≤ L + h := by
    simpa only [dist_comm z u, huz, hum] using dist_triangle z u (γminus h)
  have hhip : dist z (γplus h) ≤ L + h := by
    simpa only [dist_comm z u, huz, hup] using dist_triangle z u (γplus h)
  rw [cos_comparisonAngleNegCurvature_of_pos hκ hL hh hlom hhim,
    cos_comparisonAngleNegCurvature_of_pos hκ hL hh hlop hhip, ← add_div] at hcos
  have hden : 0 < sinh (sqrt κ * L) * sinh (sqrt κ * h) :=
    mul_pos (sinh_pos_iff.mpr (mul_pos (sqrt_pos.mpr hκ) hL))
      (sinh_pos_iff.mpr (mul_pos (sqrt_pos.mpr hκ) hh))
  have hn := (le_div_iff₀ hden).mp hcos
  rw [zero_mul] at hn
  nlinarith

theorem cosh_midpoint_le_of_endpoint_comparison
    {X : Type*} [MetricSpace X] {κ A T t h : ℝ} (hκ : 0 < κ) (hA : 0 ≤ A)
    (σ : Icc (0 : ℝ) A → X) (hσ : Isometry σ) (ht : t ∈ Icc (0 : ℝ) A)
    (hh : 0 < h) (hleft : h ≤ t) (hright : t + h ≤ A) {z : X}
    (hcmp : endpointHingeComparison κ z T)
    (hsum : dist (σ ⟨t, ht⟩) z + h < T)
    (τ : Icc (0 : ℝ) (dist (σ ⟨t, ht⟩) z) → X) (hτ : Isometry τ)
    (hτ0 : τ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = σ ⟨t, ht⟩)
    (hτend : τ ⟨dist (σ ⟨t, ht⟩) z, ⟨dist_nonneg, le_rfl⟩⟩ = z)
    (hlocal : ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ σ ⟨t, ht⟩ ∈ Ω) :
    cosh (sqrt κ * dist z (IccExtend hA σ (t - h))) +
      cosh (sqrt κ * dist z (IccExtend hA σ (t + h))) ≤
      2 * cosh (sqrt κ * h) * cosh (sqrt κ * dist z (σ ⟨t, ht⟩)) := by
  let u := σ ⟨t, ht⟩
  let L := dist u z
  let β : ℝ → X := IccExtend dist_nonneg τ
  let γminus : ℝ → X := fun s => IccExtend hA σ (t - s)
  let γplus : ℝ → X := fun s => IccExtend hA σ (t + s)
  have hmrad : ∀ s ∈ Ioc (0 : ℝ) h, dist u (γminus s) = s := by
    intro s hs
    exact hσ.IccExtend_backward_radial ht ⟨hs.1.le, by linarith [hs.2]⟩
  have hprad : ∀ s ∈ Ioc (0 : ℝ) h, dist u (γplus s) = s := by
    intro s hs
    exact hσ.IccExtend_forward_radial ht ⟨hs.1.le, by linarith [hs.2]⟩
  by_cases hz : u = z
  · have hm := hmrad h ⟨hh, le_rfl⟩
    have hp := hprad h ⟨hh, le_rfl⟩
    change _ ≤ 2 * cosh (sqrt κ * h) * cosh (sqrt κ * dist z u)
    rw [hz, dist_self, mul_zero, cosh_zero, mul_one]
    change cosh (sqrt κ * dist z (γminus h)) + cosh (sqrt κ * dist z (γplus h)) ≤ _
    rw [hz] at hm hp
    rw [hm, hp]
    linarith
  have hL : 0 < L := dist_pos.mpr hz
  have hβrad : ∀ s ∈ Ioc (0 : ℝ) L, dist u (β s) = s := by
    intro s hs
    have h := hτ.IccExtend_forward_radial (h := 0) ⟨le_rfl, dist_nonneg⟩
      (s := s) (by simpa only [sub_zero] using (show s ∈ Icc (0 : ℝ) L from ⟨hs.1.le, hs.2⟩))
    simpa only [zero_add, hτ0] using h
  have hβmin : ∀ s ∈ Ioc (0 : ℝ) L, ∀ v ∈ Ioc (0 : ℝ) L,
      dist (β s) (β v) = |s - v| := by
    intro s hs v hv
    exact hτ.dist_IccExtend dist_nonneg ⟨hs.1.le, hs.2⟩ ⟨hv.1.le, hv.2⟩
  have hmmin : ∀ s ∈ Ioc (0 : ℝ) h, ∀ v ∈ Ioc (0 : ℝ) h,
      dist (γminus s) (γminus v) = |s - v| := by
    intro s hs v hv
    exact hσ.IccExtend_backward_dist ht ⟨hs.1.le, by linarith [hs.2]⟩
      ⟨hv.1.le, by linarith [hv.2]⟩
  have hpmin : ∀ s ∈ Ioc (0 : ℝ) h, ∀ v ∈ Ioc (0 : ℝ) h,
      dist (γplus s) (γplus v) = |s - v| := by
    intro s hs v hv
    exact hσ.IccExtend_forward_dist ht ⟨hs.1.le, by linarith [hs.2]⟩
      ⟨hv.1.le, by linarith [hv.2]⟩
  have hopp : ∀ s ∈ Ioc (0 : ℝ) h, ∀ v ∈ Ioc (0 : ℝ) h,
      dist (γplus s) (γminus v) = s + v := by
    intro s hs v hv
    exact hσ.IccExtend_opposite_dist ht ⟨hs.1.le, by linarith [hs.2]⟩
      ⟨hv.1.le, by linarith [hv.2]⟩
  have hbend : β L = z := by
    change IccExtend dist_nonneg τ (dist u z) = z
    rw [IccExtend_right, hτend]
  simpa only [u, L, γminus, γplus, dist_comm (σ ⟨t, ht⟩) z] using
    cosh_sum_le_of_adjacent_germs hκ hL hh hcmp hsum hbend hβrad hβmin
      hmrad hpmin hprad hmmin hopp hlocal

end DifferentialGeometry.Geometry.Comparison.Toponogov
