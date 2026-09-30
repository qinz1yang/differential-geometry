import DifferentialGeometry.Topology.MetricSpace.LocalHopfRinow
import DifferentialGeometry.Topology.MetricSpace.ShortCurvePrefix
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem exists_isometric_segment_of_compact_inner_balls
    {p a : X}
    (hcompact : ∀ r : ℝ, 0 ≤ r → r < dist p a → IsCompact (closedBall p r))
    (hcurves : ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = a ∧
        eVariationOn c univ < ENNReal.ofReal (dist p a + ε)) :
    ∃ γ : Icc (0 : ℝ) (dist p a) → X, Isometry γ ∧
      γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = p ∧
      γ ⟨dist p a, ⟨dist_nonneg, le_rfl⟩⟩ = a := by
  classical
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεzero : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose c hc hc0 hc1 hlen using fun n => hcurves (ε n) (hεpos n)
  choose q hq hq0 htail hrad hpair hmem using fun n =>
    exists_short_curve_prefix (hεpos n) (c n) (hc n) (hc0 n) (hc1 n) (hlen n)
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hend (t : Icc (0 : ℝ) (dist p a)) (ht : t.val = dist p a) :
      Tendsto (fun n => q n t) U (𝓝 a) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) (hεzero.mono_left hU)
    have hh := htail n t
    rw [ht] at hh
    linarith
  have hlimit (t : Icc (0 : ℝ) (dist p a)) :
      ∃ x : X, Tendsto (fun n => q n t) U (𝓝 x) := by
    by_cases ht : t.val < dist p a
    · obtain ⟨x, _, hx⟩ := (hcompact t.val t.property.1 ht).ultrafilter_le_nhds
        (Ultrafilter.map (fun n => q n t) U) (by
          apply le_principal_iff.mpr
          change ∀ᶠ n in (U : Filter ℕ), q n t ∈ closedBall p t.val
          exact Eventually.of_forall fun n => by
            rw [mem_closedBall, dist_comm]
            exact (hrad n t).2)
      exact ⟨x, hx⟩
    · exact ⟨a, hend t (le_antisymm t.property.2 (le_of_not_gt ht))⟩
  choose γ hconv using hlimit
  have hlower (n : ℕ) (s t : Icc (0 : ℝ) (dist p a)) :
      dist s t - ε n ≤ dist (q n s) (q n t) := by
    rcases le_total s t with hst | hts
    · have hh := (hpair n s t hst).1
      simpa only [Subtype.dist_eq, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr (show s.val ≤ t.val from hst)), neg_sub] using hh
    · have hh := (hpair n t s hts).1
      simpa only [Subtype.dist_eq, Real.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr (show t.val ≤ s.val from hts)),
        dist_comm (q n t) (q n s)] using hh
  have hγ : Isometry γ := by
    apply Isometry.of_dist_eq
    intro s t
    apply le_antisymm
    · apply le_of_tendsto ((hconv s).dist (hconv t))
      exact Eventually.of_forall fun n => by simpa only [NNReal.coe_one, one_mul] using (hq n).dist_le_mul s t
    · have hh := le_of_tendsto_of_tendsto
        (tendsto_const_nhds.sub (hεzero.mono_left hU))
        ((hconv s).dist (hconv t))
        (Eventually.of_forall fun n => hlower n s t)
      simpa only [sub_zero] using hh
  refine ⟨γ, hγ, ?_, ?_⟩
  · apply tendsto_nhds_unique (hconv ⟨0, ⟨le_rfl, dist_nonneg⟩⟩)
    simpa only [hq0] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => p) U (𝓝 p))
  · exact tendsto_nhds_unique (hconv ⟨dist p a, ⟨dist_nonneg, le_rfl⟩⟩)
      (hend ⟨dist p a, ⟨dist_nonneg, le_rfl⟩⟩ rfl)

theorem exists_isometric_segment_to_boundary_of_locallyCompact_ball
    [CompleteSpace X]
    (hcurves : ∀ x y : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + ε))
    (p : X) {L : ℝ} (hL : 0 < L) [LocallyCompactSpace (ball p L)]
    {a : X} (ha : dist p a = L) :
    ∃ γ : Icc (0 : ℝ) L → X, Isometry γ ∧
      γ ⟨0, ⟨le_rfl, hL.le⟩⟩ = p ∧ γ ⟨L, ⟨hL.le, le_rfl⟩⟩ = a := by
  subst L
  exact exists_isometric_segment_of_compact_inner_balls
    (fun r _ hr => isCompact_closedBall_of_locallyCompact_ball hcurves p hL hr)
    (hcurves p a)

end Metric
