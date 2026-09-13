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

theorem endChartTipSideDiameterBound_false_of_scalarDistance_diverges
    {g : SmoothRiemannianMetric I3 W} (H : FiniteHorn g) (ray : EndRay H.endpoint)
    (d : ℕ → ℝ) (hd : ∀ i, d i ∈ Set.Ioc 0 ray.length)
    (hzero : Filter.Tendsto d Filter.atTop (nhds 0))
    (hlarge : Filter.Tendsto (fun i => metricScalarAt g (ray.point (d i)) * d i ^ 2)
      Filter.atTop Filter.atTop) :
    ¬ EndChartTipSideDiameterBound g H ray d := by
  rintro ⟨L, hL, hD⟩
  have hdeep : ∀ᶠ i in Filter.atTop,
      ∀ (hx : ray.point (d i) ∈ H.subend (tailIndex g H))
        (E : EndChart g H (ray.point (d i)) hx), ∀ x : W,
        dist (x : UniformSpace.Completion W) H.endpoint < (1 - 1 / 40) * d i →
          E.cross.tube.height x < 1 / 2 :=
    endChart_height_lt_half_of_dist_lt H ray d hd hzero hlarge (1 / 40) (by norm_num) (by norm_num)
  have hbig : ∀ᶠ i in Filter.atTop,
      (20 * L) ^ 2 + 1 ≤ metricScalarAt g (ray.point (d i)) * d i ^ 2 :=
    hlarge.eventually_ge_atTop ((20 * L) ^ 2 + 1)
  obtain ⟨i, hDi, hdeepi, hbigi, htail⟩ :=
    (hD.and (hdeep.and (hbig.and (eventually_mem_tail g H ray d hd hzero)))).exists
  set E := endChart g H (ray.point (d i)) htail with hE
  have hdpos : 0 < d i := (hd i).1
  have hs_mem : (1 - 1 / 20) * d i ∈ Set.Ioc 0 ray.length :=
    ⟨by nlinarith, by nlinarith [(hd i).2]⟩
  have hxend : dist (ray.point ((1 - 1 / 20) * d i) : UniformSpace.Completion W) H.endpoint =
      (1 - 1 / 20) * d i := ray.radial ((1 - 1 / 20) * d i) hs_mem
  have hclose : dist (ray.point ((1 - 1 / 20) * d i) : UniformSpace.Completion W) H.endpoint <
      (1 - 1 / 40) * d i := by
    rw [hxend]
    nlinarith
  have htip : E.cross.tube.height (ray.point ((1 - 1 / 20) * d i)) < 1 / 2 :=
    hdeepi htail E _ hclose
  have hcenter : E.cross.tube.map (E.p, (1 / 2 : ℝ)) = ray.point (d i) := by
    rw [E.cross.center_eq, E.center]
  have hheight : E.cross.tube.height (ray.point (d i)) = 1 / 2 :=
    (GlobalNeckTube.mem_sectionSet_iff E.cross.tube (by norm_num) _).mp
      ⟨(E.p, (1 / 2 : ℝ)), ⟨Set.mem_univ _, rfl⟩, hcenter⟩
  have hdist := hDi htail E (ray.point ((1 - 1 / 20) * d i)) (ray.point (d i)) htip.le hheight.le
  rw [ray.minimizing ((1 - 1 / 20) * d i) hs_mem (d i) (hd i)] at hdist
  have hsep : (1 / 20 : ℝ) * d i ≤ L / Real.sqrt (metricScalarAt g (ray.point (d i))) := by
    have hdiff : d i - (1 - 1 / 20) * d i = (1 / 20) * d i := by ring
    have habs : |(1 - 1 / 20) * d i - d i| = (1 / 20) * d i := by
      rw [abs_sub_comm, hdiff, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 20) * d i)]
    linarith [habs]
  have hspos : 0 < metricScalarAt g (ray.point (d i)) := E.Q_pos
  have hsroot : 0 < Real.sqrt (metricScalarAt g (ray.point (d i))) := Real.sqrt_pos.mpr hspos
  have hmul : (1 / 20 : ℝ) * d i * Real.sqrt (metricScalarAt g (ray.point (d i))) ≤ L := by
    have h := (le_div_iff₀ hsroot).mp hsep
    linarith
  have hsqrt : Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) =
      Real.sqrt (metricScalarAt g (ray.point (d i))) * d i := by
    rw [Real.sqrt_mul hspos.le, Real.sqrt_sq hdpos.le]
  have hkey : (1 / 20 : ℝ) * Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) ≤ L := by
    rw [hsqrt]
    nlinarith [hmul]
  have hsq : 20 * L < Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) := by
    rw [Real.lt_sqrt (by positivity : (0 : ℝ) ≤ 20 * L)]
    linarith
  have hstep : (1 / 20 : ℝ) * (20 * L) <
      (1 / 20 : ℝ) * Real.sqrt (metricScalarAt g (ray.point (d i)) * d i ^ 2) :=
    mul_lt_mul_of_pos_left hsq (by norm_num)
  nlinarith [hkey, hstep]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
