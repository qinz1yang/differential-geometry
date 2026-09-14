import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EndChartTipSideDiameter

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

theorem endChart_tipSide_pair_height_and_dist {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (ray : EndRay H.endpoint) (d : ℕ → ℝ)
    (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop)
    (c : ℝ) (hc : 1 / 40 < c) (hc1 : c < 1) :
    ∀ᶠ i in Filter.atTop, ∀ (hx : ray.point (d i) ∈ H.subend (tailIndex g H))
      (E : EndChart g H (ray.point (d i)) hx),
      E.cross.tube.height (ray.point ((1 - c) * d i)) ≤ 1 / 2 ∧
        E.cross.tube.height (ray.point (d i)) = 1 / 2 ∧
        c * d i ≤ dist (ray.point ((1 - c) * d i)) (ray.point (d i)) := by
  filter_upwards [endChart_height_lt_half_of_dist_lt H ray d hd hzero hlarge
    (1 / 40) (by norm_num) (by norm_num)] with i htip
  intro hx E
  have hdpos : 0 < d i := (hd i).1
  have hmem : (1 - c) * d i ∈ Set.Ioc 0 ray.length := by
    have hcpos : 0 < 1 - c := by linarith
    have hle : (1 - c) * d i ≤ d i := by nlinarith only [hc, hdpos]
    exact ⟨mul_pos hcpos hdpos, le_trans hle (hd i).2⟩
  have hheight_x : E.cross.tube.height (ray.point ((1 - c) * d i)) < 1 / 2 := by
    refine htip hx E (ray.point ((1 - c) * d i)) ?_
    rw [ray.radial ((1 - c) * d i) hmem]
    nlinarith only [hc, hdpos]
  have hheight_y : E.cross.tube.height (ray.point (d i)) = 1 / 2 := by
    have hcenter : E.cross.tube.map (E.p, (1 / 2 : ℝ)) = ray.point (d i) := by
      rw [E.cross.center_eq, E.center]
    have hmemsec : ray.point (d i) ∈ E.cross.tube.sectionSet (1 / 2) :=
      ⟨(E.p, (1 / 2 : ℝ)), ⟨Set.mem_univ _, rfl⟩, hcenter⟩
    exact (GlobalNeckTube.mem_sectionSet_iff E.cross.tube (by norm_num) _).mp hmemsec
  have hdist : c * d i ≤ dist (ray.point ((1 - c) * d i)) (ray.point (d i)) := by
    have h := dist_triangle (ray.point (d i) : UniformSpace.Completion W)
      (ray.point ((1 - c) * d i) : UniformSpace.Completion W) H.endpoint
    rw [ray.radial (d i) (hd i), UniformSpace.Completion.dist_eq,
      dist_comm (ray.point (d i)) (ray.point ((1 - c) * d i)),
      ray.radial ((1 - c) * d i) hmem] at h
    linarith only [h]
  exact ⟨hheight_x.le, hheight_y, hdist⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
