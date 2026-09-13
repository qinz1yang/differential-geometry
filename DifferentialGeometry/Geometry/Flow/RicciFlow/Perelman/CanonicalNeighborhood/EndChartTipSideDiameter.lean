import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W] [SigmaCompactSpace W]

def EndChartTipSideDiameterBound (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) : Prop :=
  ∃ L : ℝ, 0 < L ∧ ∀ᶠ i in Filter.atTop,
    ∀ (hx : ray.point (d i) ∈ H.subend (tailIndex g H))
      (E : EndChart g H (ray.point (d i)) hx), ∀ x y : W,
      E.cross.tube.height x ≤ 1 / 2 → E.cross.tube.height y ≤ 1 / 2 →
        dist x y ≤ L / Real.sqrt (metricScalarAt g (ray.point (d i)))

omit [SigmaCompactSpace W] in
theorem hornRadialExitPositionAtEndChart_of_endChartTipSideDiameterBound
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hdiam : EndChartTipSideDiameterBound g H ray d) :
    HornRadialExitPositionAtEndChart g H ray d := by
  refine (hornRadialExitPositionAtEndChart_iff_tipSide_closedBall g H ray d).mpr ?_
  obtain ⟨L, hL, hbound⟩ := hdiam
  intro e he he10
  filter_upwards [hbound, hlarge.eventually_ge_atTop (max 1 ((2 * L / e) ^ 2 + 1))]
    with i hD hbig
  intro hx x hxle
  have hdpos : 0 < d i := (hd i).1
  have hsmul : 1 ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 :=
    le_trans (le_max_left _ _) hbig
  have hs_pos : 0 < metricScalarAt g (ray.point (d i)) := by
    nlinarith [hsmul, sq_nonneg (d i), sq_pos_of_pos hdpos]
  have hspread : L / Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) < e := by
    have hpos : 0 < 2 * L / e := by positivity
    have hlt : 2 * L / e < Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) := by
      rw [Real.lt_sqrt hpos.le]
      have h2 : (2 * L / e) ^ 2 + 1 ≤
          metricScalarAt g (ray.point (d i)) * d i ^ 2 := le_trans (le_max_right _ _) hbig
      linarith
    have hdiv := div_lt_div_of_pos_left hL hpos hlt
    have heq : L / (2 * L / e) = e / 2 := by
      field_simp
    rw [heq] at hdiv
    linarith
  have hradius : L / Real.sqrt (metricScalarAt g (ray.point (d i))) < e * d i := by
    have hsqrt : Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) =
        Real.sqrt (metricScalarAt g (ray.point (d i))) * d i := by
      rw [Real.sqrt_mul hs_pos.le, Real.sqrt_sq hdpos.le]
    rw [hsqrt] at hspread
    have hne : Real.sqrt (metricScalarAt g (ray.point (d i))) ≠ 0 := by positivity
    have hsplit : L / Real.sqrt (metricScalarAt g (ray.point (d i))) =
        d i * (L / (Real.sqrt (metricScalarAt g (ray.point (d i))) * d i)) := by
      field_simp
    rw [hsplit, mul_comm e (d i)]
    exact mul_lt_mul_of_pos_left hspread hdpos
  set E := endChart g H (ray.point (d i)) hx with hE
  have hcenter : E.cross.tube.map (E.p, (1 / 2 : ℝ)) = ray.point (d i) := by
    rw [E.cross.center_eq, E.center]
  have hsrc : (E.p, (1 / 2 : ℝ)) ∈ E.cross.tube.map.source := by
    rw [E.cross.tube.source_eq]
    exact ⟨Set.mem_univ _, by norm_num⟩
  have hmemsec : ray.point (d i) ∈ E.cross.tube.sectionSet (1 / 2) :=
    ⟨(E.p, (1 / 2 : ℝ)), ⟨Set.mem_univ _, rfl⟩, hcenter⟩
  have hheight : E.cross.tube.height (ray.point (d i)) = 1 / 2 :=
    (GlobalNeckTube.mem_sectionSet_iff E.cross.tube (by norm_num) _).mp hmemsec
  have hdist : dist x (ray.point (d i)) ≤ L / Real.sqrt (metricScalarAt g (ray.point (d i))) :=
    hD hx E x (ray.point (d i)) hxle hheight.le
  have hlt : dist (x : UniformSpace.Completion W) H.endpoint < (1 + e) * d i :=
    calc dist (x : UniformSpace.Completion W) H.endpoint
      ≤ dist (x : UniformSpace.Completion W) (ray.point (d i) : UniformSpace.Completion W) +
        dist (ray.point (d i) : UniformSpace.Completion W) H.endpoint := dist_triangle _ _ _
    _ = dist x (ray.point (d i)) + d i := by
        rw [UniformSpace.Completion.dist_eq, ray.radial (d i) (hd i)]
    _ ≤ L / Real.sqrt (metricScalarAt g (ray.point (d i))) + d i := by linarith
    _ < e * d i + d i := by linarith
    _ = (1 + e) * d i := by ring
  exact hlt.le

theorem finite_horn_barriers_of_endChartTipSideDiameterBound
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (endData : EndGeometry H)
    (ray : EndRay H.endpoint) (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (hdiam : EndChartTipSideDiameterBound g H ray d) : Nonempty (HornBarriers H ray d) :=
  finite_horn_barriers_of_hornRadialExitPositionAtEndChart H endData ray d hd hzero hlarge
    (hornRadialExitPositionAtEndChart_of_endChartTipSideDiameterBound g H ray d hd hlarge hdiam)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
