import DifferentialGeometry.Geometry.Comparison.BonnetMyers.SectionalRicci
import DifferentialGeometry.Geometry.Curvature.Metric.Conditions
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import DifferentialGeometry.Geometry.Curvature.PositiveSectional

noncomputable section
open Manifold
open scoped ContDiff

namespace Poincare.Geometry

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [SigmaCompactSpace M] in
theorem HasPositiveSectionalCurvature.positive_ricci_metric
    {g : SmoothRiemannianMetric I M} (hsec : HasPositiveSectionalCurvature g)
    (hdim : 2 ≤ Module.finrank ℝ E) : positiveRicciMetric g := by
  intro x v hv
  rw [metricRicciAt_apply_eq_ricciTensor]
  apply DifferentialGeometry.Geometry.Riemannian.BonnetMyers.ricci_pos_of_sec g x (by omega)
    (fun a b ha hb hab ↦ ?_) hv
  apply hsec x a b
  rw [LinearIndependent.pair_iff' ha]
  intro r hr
  have hmul : r * g.inner x a a = 0 := by
    rw [← hr, map_smul, smul_eq_mul] at hab
    exact hab
  have hrzero : r = 0 := (mul_eq_zero.mp hmul).resolve_right (g.pos x a ha).ne'
  apply hb
  rw [← hr, hrzero, zero_smul]

end Poincare.Geometry
