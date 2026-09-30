import DifferentialGeometry.Topology.MetricSpace.CurveMidpoint
import DifferentialGeometry.Topology.MetricSpace.GeodesicCompactness
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem edist_add_edist_add_edist_le_eVariationOn (c : unitInterval → X)
    {s t : unitInterval} (hst : s ≤ t) :
    edist (c 0) (c s) + edist (c s) (c t) + edist (c t) (c 1) ≤
      eVariationOn c univ := by
  have h₁ := eVariationOn.edist_le c (s := Icc (0 : unitInterval) s)
    (show (0 : unitInterval) ∈ Icc 0 s from ⟨le_rfl, unitInterval.nonneg'⟩)
    (show s ∈ Icc 0 s from ⟨unitInterval.nonneg', le_rfl⟩)
  have h₂ := eVariationOn.edist_le c (s := Icc s t) ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩
  have h₃ := eVariationOn.edist_le c (s := Icc t (1 : unitInterval))
    (show t ∈ Icc t 1 from ⟨le_rfl, unitInterval.le_one'⟩)
    (show (1 : unitInterval) ∈ Icc t 1 from ⟨unitInterval.le_one', le_rfl⟩)
  have hleft := eVariationOn.Icc_add_Icc c (s := univ)
    (unitInterval.nonneg' : 0 ≤ s) hst (mem_univ s)
  have hfull := eVariationOn.Icc_add_Icc c (s := univ)
    (unitInterval.nonneg' : 0 ≤ t) unitInterval.le_one' (mem_univ t)
  have hall : Icc (0 : unitInterval) 1 = univ := Set.Icc_bot_top
  simp only [univ_inter] at hleft
  simp only [univ_inter, hall] at hfull
  exact (add_le_add (add_le_add h₁ h₂) h₃).trans_eq (by rw [hleft, hfull])

private theorem curve_dist_le_radial_difference {a b : X} {ε : ℝ} (hε : 0 < ε)
    (c : unitInterval → X) (ha : c 0 = a) (hb : c 1 = b)
    (hlen : eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (s t : unitInterval) :
    dist (c s) (c t) ≤ |dist a (c s) - dist a (c t)| + ε := by
  have hordered (u v : unitInterval) (huv : u ≤ v) :
      dist (c u) (c v) ≤ |dist a (c u) - dist a (c v)| + ε := by
    have hbound := (edist_add_edist_add_edist_le_eVariationOn c huv).trans_lt hlen
    rw [ha, hb, edist_dist, edist_dist, edist_dist,
      ← ENNReal.ofReal_add dist_nonneg dist_nonneg,
      ← ENNReal.ofReal_add (add_nonneg dist_nonneg dist_nonneg) dist_nonneg] at hbound
    have hreal := (ENNReal.ofReal_lt_ofReal_iff
      (add_pos_of_nonneg_of_pos dist_nonneg hε)).mp hbound
    have hab := dist_triangle a (c v) b
    have habs := neg_le_abs (dist a (c u) - dist a (c v))
    linarith
  rcases le_total s t with hst | hts
  · exact hordered s t hst
  · simpa only [dist_comm (c t) (c s), abs_sub_comm (dist a (c t)) (dist a (c s))]
      using hordered t s hts

private theorem exists_radial_curve_selection {a b : X} (c : unitInterval → X)
    (hc : Continuous c) (ha : c 0 = a) (hb : c 1 = b) :
    ∃ τ : unitInterval → unitInterval, τ 0 = 0 ∧ τ 1 = 1 ∧
      ∀ t, dist a (c (τ t)) = (t : ℝ) * dist a b := by
  classical
  have hex (t : unitInterval) : ∃ u : unitInterval,
      dist a (c u) = (t : ℝ) * dist a b := by
    apply intermediate_value_univ (0 : unitInterval) 1
      (continuous_const.dist hc : Continuous fun u => dist a (c u))
    rw [ha, hb, dist_self]
    exact ⟨mul_nonneg t.property.1 dist_nonneg,
      mul_le_of_le_one_left dist_nonneg t.property.2⟩
  choose τ hτ using hex
  refine ⟨fun t => if t = 0 then 0 else if t = 1 then 1 else τ t, by simp, by simp, ?_⟩
  intro t
  dsimp only
  split_ifs with hzero hone
  · subst t
    simp [ha]
  · subst t
    simp [hb]
  · exact hτ t

theorem exists_metric_segment_of_compact_arbitrarily_short_curves
    {K : Set X} (hK : IsCompact K) {a b : X}
    (hcurves : ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        (∀ t, c t ∈ K) ∧ eVariationOn c univ < ENNReal.ofReal (dist a b + ε)) :
    ∃ f : unitInterval → X, Continuous f ∧ f 0 = a ∧ f 1 = b ∧
      (∀ t, f t ∈ K) ∧ ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  classical
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  choose c hc hc0 hc1 hmem hlen using fun n => hcurves (ε n) (hεpos n)
  choose τ hτ0 hτ1 hτ using fun n => exists_radial_curve_selection (c n) (hc n) (hc0 n) (hc1 n)
  let g (n : ℕ) (t : unitInterval) := c n (τ n t)
  have hdist (n : ℕ) (s t : unitInterval) :
      dist (g n s) (g n t) ≤ dist a b * dist s t + ε n := by
    have h := curve_dist_le_radial_difference (hεpos n) (c n) (hc0 n) (hc1 n)
      (hlen n) (τ n s) (τ n t)
    rw [hτ n s, hτ n t, ← sub_mul, abs_mul, abs_of_nonneg dist_nonneg] at h
    change dist (g n s) (g n t) ≤ dist a b * |(s : ℝ) - (t : ℝ)| + ε n
    simpa only [mul_comm] using h
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hcompact (t : unitInterval) : ∃ x ∈ K,
      Tendsto (fun n => g n t) U (𝓝 x) := by
    apply hK.ultrafilter_le_nhds (Ultrafilter.map (fun n => g n t) U)
    apply le_principal_iff.mpr
    change ∀ᶠ n in (U : Filter ℕ), g n t ∈ K
    exact Eventually.of_forall (fun n => hmem n (τ n t))
  choose f hfK hconv using hcompact
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let D : ℝ≥0 := ⟨dist a b, dist_nonneg⟩
  have hLip : LipschitzWith D f := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have h := le_of_tendsto_of_tendsto ((hconv s).dist (hconv t))
      (tendsto_const_nhds.add (hεlim.mono_left hU))
      (Eventually.of_forall (fun n => hdist n s t))
    change dist (f s) (f t) ≤ dist a b * dist s t
    simpa only [add_zero] using h
  have hf0 : f 0 = a := tendsto_nhds_unique (hconv 0)
    (by simpa only [g, hτ0, hc0] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) U (𝓝 a)))
  have hf1 : f 1 = b := tendsto_nhds_unique (hconv 1)
    (by simpa only [g, hτ1, hc1] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => b) U (𝓝 b)))
  refine ⟨f, hLip.continuous, hf0, hf1, hfK, ?_⟩
  apply dist_eq_mul_of_lipschitz_interval f hLip
  change dist (f 0) (f 1) = dist a b
  rw [hf0, hf1]

end Metric
