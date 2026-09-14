import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornBarriersRadialNesting

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] FiniteHorn.ambient_metric
attribute [local instance] EndAngles.metric

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

omit [SigmaCompactSpace W] in
theorem hornRadialExitPositionAtEndChart_of_hornRadialOuterPosition
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hout : HornRadialOuterPosition g H ray d) :
    HornRadialExitPositionAtEndChart g H ray d := by
  intro e he he10
  filter_upwards [hout e he he10] with i hi hx x hxfar
  have htube : neckTube g H ray d i = (endChart g H (ray.point (d i)) hx).cross.tube := by
    rw [neckTube, dif_pos hx]
  rw [htube] at hi
  exact hi x hxfar

omit [SigmaCompactSpace W] in
theorem hornRadialExitPositionAtEndChart_iff_hornRadialOuterPosition
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0)) :
    HornRadialExitPositionAtEndChart g H ray d ↔ HornRadialOuterPosition g H ray d := by
  refine ⟨?_, fun hout =>
    hornRadialExitPositionAtEndChart_of_hornRadialOuterPosition H ray d hout⟩
  intro hexit e he he10
  filter_upwards [hexit e he he10, eventually_mem_tail g H ray d hd hzero] with i hi hgood
  intro x hxfar
  have htube : neckTube g H ray d i = (endChart g H (ray.point (d i)) hgood).cross.tube := by
    rw [neckTube, dif_pos hgood]
  rw [htube]
  exact hi hgood x hxfar

theorem hornRadialPosition_iff_hornRadialExitPositionAtEndChart
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop) :
    HornRadialPosition g H ray d ↔ HornRadialExitPositionAtEndChart g H ray d :=
  (hornRadialPosition_iff_hornRadialOuterPosition H ray d hd hzero hlarge).trans
    (hornRadialExitPositionAtEndChart_iff_hornRadialOuterPosition H ray d hd hzero).symm

theorem finite_horn_barriers_iff_without_endGeometry (g : SmoothRiemannianMetric I3 W) :
    (∀ (H : FiniteHorn g) (_endData : EndGeometry H) (ray : EndRay H.endpoint) (d : ℕ → ℝ),
        (∀ i, d i ∈ Set.Ioc 0 ray.length) → Filter.Tendsto d Filter.atTop (nhds 0) →
        Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
          Filter.atTop Filter.atTop →
        Nonempty (HornBarriers H ray d)) ↔
      (∀ (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ),
        (∀ i, d i ∈ Set.Ioc 0 ray.length) → Filter.Tendsto d Filter.atTop (nhds 0) →
        Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
          Filter.atTop Filter.atTop →
        Nonempty (HornBarriers H ray d)) := by
  constructor
  · intro h H ray d hd hzero hlarge
    exact h H (Classical.choice (finite_horn_end_rays H)) ray d hd hzero hlarge
  · intro h H _endData ray d hd hzero hlarge
    exact h H ray d hd hzero hlarge

private theorem tendsto_natCast_add_one_atTop :
    Filter.Tendsto (fun i : ℕ => (i : ℝ) + 1) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ : ∃ N : ℕ, b ≤ (N : ℝ) := exists_nat_ge b
  refine ⟨N, fun n hn => ?_⟩
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

private theorem tendsto_inv_natCast_add_one_atTop_nhds_zero :
    Filter.Tendsto (fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 1)) Filter.atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem exists_scaleSequence_mem_Ioc_tendsto_zero (L : ℝ) (hL : 0 < L) :
    ∃ d : ℕ → ℝ,
      (∀ i, d i ∈ Set.Ioc 0 L) ∧ Filter.Tendsto d Filter.atTop (nhds 0) := by
  refine ⟨fun i => L / ((i : ℝ) + 1), ?_, ?_⟩
  · intro i
    refine ⟨div_pos hL (by positivity), ?_⟩
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (i : ℝ) + 1)]
    nlinarith [hL, (show (0 : ℝ) ≤ (i : ℝ) from Nat.cast_nonneg i),
      (show (0 : ℝ) ≤ 1 from by norm_num)]
  · have h := tendsto_inv_natCast_add_one_atTop_nhds_zero.const_mul L
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using h

theorem exists_scaleSequence_scalar_mul_sq_tendsto_atTop (L : ℝ) (hL : 0 < L) :
    ∃ s d : ℕ → ℝ,
      (∀ i, d i ∈ Set.Ioc 0 L) ∧ Filter.Tendsto d Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun i => s i * d i ^ 2) Filter.atTop Filter.atTop := by
  refine ⟨fun i => ((i : ℝ) + 1) ^ 3 / L ^ 2, fun i => L / ((i : ℝ) + 1), ?_, ?_, ?_⟩
  · intro i
    refine ⟨div_pos hL (by positivity), ?_⟩
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (i : ℝ) + 1)]
    nlinarith [hL, (show (0 : ℝ) ≤ (i : ℝ) from Nat.cast_nonneg i),
      (show (0 : ℝ) ≤ 1 from by norm_num)]
  · have h := tendsto_inv_natCast_add_one_atTop_nhds_zero.const_mul L
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using h
  · have hfun : (fun i : ℕ => (((i : ℝ) + 1) ^ 3 / L ^ 2) * (L / ((i : ℝ) + 1)) ^ 2)
        = fun i : ℕ => (i : ℝ) + 1 := by
      funext i
      have hL0 : L ≠ 0 := ne_of_gt hL
      field_simp
    rw [hfun]
    exact tendsto_natCast_add_one_atTop

theorem exists_scaleSequence_not_scalar_mul_sq_tendsto_atTop (L : ℝ) (hL : 0 < L) :
    ∃ s d : ℕ → ℝ,
      (∀ i, d i ∈ Set.Ioc 0 L) ∧ Filter.Tendsto d Filter.atTop (nhds 0) ∧
      ¬ Filter.Tendsto (fun i => s i * d i ^ 2) Filter.atTop Filter.atTop := by
  refine ⟨fun _ => (1 : ℝ), fun i => L / ((i : ℝ) + 1), ?_, ?_, ?_⟩
  · intro i
    refine ⟨div_pos hL (by positivity), ?_⟩
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (i : ℝ) + 1)]
    nlinarith [hL, (show (0 : ℝ) ≤ (i : ℝ) from Nat.cast_nonneg i),
      (show (0 : ℝ) ≤ 1 from by norm_num)]
  · have h := tendsto_inv_natCast_add_one_atTop_nhds_zero.const_mul L
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using h
  · intro hcontra
    have hzero : Filter.Tendsto (fun i : ℕ => L / ((i : ℝ) + 1)) Filter.atTop (nhds 0) := by
      have h := tendsto_inv_natCast_add_one_atTop_nhds_zero.const_mul L
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using h
    have hsquare : Filter.Tendsto
        (fun i : ℕ => (L / ((i : ℝ) + 1)) ^ 2) Filter.atTop (nhds 0) := by
      simpa [pow_two] using hzero.mul hzero
    have hge : ∀ᶠ i : ℕ in Filter.atTop,
        (1 : ℝ) ≤ 1 * (L / ((i : ℝ) + 1)) ^ 2 :=
      hcontra.eventually_ge_atTop 1
    have hlt : ∀ᶠ i : ℕ in Filter.atTop, (L / ((i : ℝ) + 1)) ^ 2 < 1 :=
      hsquare.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    obtain ⟨i, hi₁, hi₂⟩ := (hge.and hlt).exists
    simp only [one_mul] at hi₁
    linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
