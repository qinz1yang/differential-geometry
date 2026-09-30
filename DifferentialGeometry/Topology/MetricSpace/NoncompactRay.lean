import DifferentialGeometry.Topology.MetricSpace.SegmentConcatenation
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace Metric

variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem exists_isometric_ray_of_not_isCompact
    (hsegments : ∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t)
    (hnot : ¬ IsCompact (univ : Set X)) (p : X) :
    ∃ r : Ici (0 : ℝ) → X, Isometry r ∧ r ⟨0, by simp⟩ = p := by
  classical
  have hfar (R : ℝ) : ∃ x : X, R < dist p x := by
    by_contra hn
    push Not at hn
    apply hnot
    apply (isCompact_closedBall p R).of_isClosed_subset isClosed_univ
    intro x _
    simpa only [mem_closedBall, dist_comm] using hn x
  choose e he using fun n : ℕ => hfar ((n : ℝ) + 1)
  choose g hgcont hg0 hg1 hgd using fun n => hsegments p (e n)
  choose σ hσ hσ0 hσend using fun n => exists_isometric_segment_of_dist_eq_mul (hg0 n) (hg1 n) (hgd n)
  let L (n : ℕ) := dist p (e n)
  let τ (n : ℕ) (t : Ici (0 : ℝ)) : Icc (0 : ℝ) (L n) :=
    ⟨min (t : ℝ) (L n), le_min t.property dist_nonneg, min_le_right _ _⟩
  let f (n : ℕ) (t : Ici (0 : ℝ)) := σ n (τ n t)
  have hball (n : ℕ) (t : Ici (0 : ℝ)) : f n t ∈ closedBall p (t : ℝ) := by
    change dist (σ n (τ n t)) p ≤ (t : ℝ)
    rw [← hσ0 n, (hσ n).dist_eq]
    change |(τ n t : ℝ) - 0| ≤ (t : ℝ)
    rw [sub_zero, abs_of_nonneg (τ n t).property.1]
    exact min_le_left _ _
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hτ (t : Ici (0 : ℝ)) : ∀ᶠ n : ℕ in atTop, (τ n t : ℝ) = (t : ℝ) := by
    filter_upwards [hnat.eventually (eventually_ge_atTop (t : ℝ))] with n hn
    exact min_eq_left (hn.trans (he n).le)
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hcompact (t : Ici (0 : ℝ)) : ∃ y ∈ closedBall p (t : ℝ),
      Tendsto (fun n => f n t) U (𝓝 y) := by
    apply (isCompact_closedBall p (t : ℝ)).ultrafilter_le_nhds
      (Ultrafilter.map (fun n => f n t) U)
    apply le_principal_iff.mpr
    change ∀ᶠ n in (U : Filter ℕ), f n t ∈ closedBall p (t : ℝ)
    exact Eventually.of_forall (fun n => hball n t)
  choose r hrball hr using hcompact
  refine ⟨r, ?_, ?_⟩
  · apply Isometry.of_dist_eq
    intro s t
    have hpair : ∀ᶠ n in atTop, dist (f n s) (f n t) = dist s t := by
      filter_upwards [hτ s, hτ t] with n hns hnt
      rw [(hσ n).dist_eq]
      change |(τ n s : ℝ) - (τ n t : ℝ)| = |(s : ℝ) - t|
      rw [hns, hnt]
    have hlim : Tendsto (fun n => dist (f n s) (f n t)) atTop (𝓝 (dist s t)) :=
      tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hpair)
    exact tendsto_nhds_unique ((hr s).dist (hr t)) (hlim.mono_left hU)
  · have hz := hrball ⟨0, by simp⟩
    simpa using hz

end Metric
