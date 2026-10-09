import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk

noncomputable section

open Bundle Manifold DifferentialGeometry MeasureTheory Set
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem riemannianAreaDensity_le_diskMapEnergyDensity (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) :
    riemannianAreaDensity g U z ≤ diskMapEnergyDensity g U z := by
  have hspeeds := riemannianAreaDensity_le_mfderiv_speeds g U z
  have ha : 0 ≤ g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) :=
    metric_inner_self_nonneg g (U z) _
  have hb : 0 ≤ g.inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I) :=
    metric_inner_self_nonneg g (U z) _
  have hamgm :
      Real.sqrt (g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1)) *
        Real.sqrt (g.inner (U z) (diskMapPartial U z Complex.I)
          (diskMapPartial U z Complex.I)) ≤
      (g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) +
        g.inner (U z) (diskMapPartial U z Complex.I)
          (diskMapPartial U z Complex.I)) / 2 := by
    nlinarith [
      sq_nonneg (Real.sqrt (g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1)) -
        Real.sqrt (g.inner (U z) (diskMapPartial U z Complex.I)
          (diskMapPartial U z Complex.I))),
      Real.sq_sqrt ha, Real.sq_sqrt hb]
  exact hspeeds.trans (by
    simpa only [diskMapPartial, diskMapEnergyDensity] using hamgm)

theorem diskMapEnergyDensity_nonneg (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (z : ℂ) : 0 ≤ diskMapEnergyDensity g U z :=
  (riemannianAreaDensity_nonneg g U z).trans (riemannianAreaDensity_le_diskMapEnergyDensity g U z)

theorem riemannianAreaDensity_eq_diskMapEnergyDensity_iff (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) :
    riemannianAreaDensity g U z = diskMapEnergyDensity g U z ↔ DiskMapConformalAt g U z := by
  constructor
  · intro h
    set a : ℝ := g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) with ha
    set b : ℝ := g.inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I) with hb
    set c : ℝ := g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I) with hc
    have hsq : a * b - c ^ 2 = ((a + b) / 2) ^ 2 := by
      have h2 : riemannianAreaDensity g U z ^ 2 = diskMapEnergyDensity g U z ^ 2 := by rw [h]
      rw [ha, hb, hc]
      simpa only [riemannianAreaDensity, diskMapEnergyDensity, diskMapPartial,
        tangentTwoJacobian_sq] using h2
    have hdiff : (a - b) ^ 2 + 4 * c ^ 2 = 0 := by nlinarith [hsq]
    have hsquare : (a - b) ^ 2 = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg c]
    have hcsquare : c ^ 2 = 0 := by nlinarith [sq_nonneg (a - b), sq_nonneg c]
    have hab : a = b := sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
    have hc0 : c = 0 := sq_eq_zero_iff.mp hcsquare
    refine ⟨?_, ?_⟩
    · simpa only [hc] using hc0
    · simpa only [ha, hb] using hab
  · intro h
    exact h.areaDensity_eq_energy

theorem riemannianAreaDensity_lt_diskMapEnergyDensity_iff (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) :
    riemannianAreaDensity g U z < diskMapEnergyDensity g U z ↔ ¬ DiskMapConformalAt g U z := by
  have hle := riemannianAreaDensity_le_diskMapEnergyDensity g U z
  constructor
  · intro h hconf
    exact (ne_of_lt h) ((riemannianAreaDensity_eq_diskMapEnergyDensity_iff g U z).mpr hconf)
  · intro h
    exact lt_of_le_of_ne hle fun heq =>
      h ((riemannianAreaDensity_eq_diskMapEnergyDensity_iff g U z).mp heq)

theorem riemannianDiskArea_le_integral_diskMapEnergyDensity
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    (harea : IntegrableOn (riemannianAreaDensity g (diskExtension u)) (Metric.closedBall (0 : ℂ) 1))
    (henergy : IntegrableOn (diskMapEnergyDensity g (diskExtension u))
      (Metric.closedBall (0 : ℂ) 1)) :
    riemannianDiskArea g u ≤
      ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z := by
  rw [riemannianDiskArea, riemannianArea]
  exact setIntegral_mono_on harea henergy measurableSet_closedBall
    (fun z _ => riemannianAreaDensity_le_diskMapEnergyDensity g (diskExtension u) z)

variable [FiniteDimensional ℝ E] in
theorem IsMorreyDisk.riemannianDiskArea_eq_integral_diskMapEnergyDensity
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (h : IsMorreyDisk g γ u) :
    riemannianDiskArea g u =
      ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z :=
  riemannianDiskArea_eq_energy_of_conformal g u h.conformal

end DifferentialGeometry.Geometry
