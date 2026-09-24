import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedIntervalDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.QuadraticForm

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem abs_metric_inner_derivWithin_le_riemannNorm
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b t : ℝ} (hab : a < b) (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular) (ht : t ∈ Icc a b)
    (x : M) (v : TangentSpace I x) :
    |derivWithin (fun u => (S.base.metric u).inner x v v) (Icc a b) t| ≤
      2 * (Module.finrank ℝ E : ℝ) ^ 2 *
        Real.sqrt (normSq0S (S.base.metric t) x 4 (S.base.rm04 t x)) *
          (S.base.metric t).inner x v v := by
  have hd := (metric_inner_hasDerivWithinAt_on_closed_interval S hS hab hcarrier hregular ht x v v).derivWithin
    (uniqueDiffOn_Icc hab t ht)
  have hric := tensor02_quadForm_abs_le_of_unit_bound (S.base.metric t) (S.ricciAt t x)
    (fun u hu => ricci_quadratic_form_on_unit_vector_le_of_solution S x u hu) v
  change |S.ricciAt t x (vec2 v v)| ≤
    (Module.finrank ℝ E : ℝ) ^ 2 *
      Real.sqrt (normSq0S (S.base.metric t) x 4 (S.base.rm04 t x)) *
        (S.base.metric t).inner x v v at hric
  rw [hd, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
  calc
    _ ≤ 2 * ((Module.finrank ℝ E : ℝ) ^ 2 *
        Real.sqrt (normSq0S (S.base.metric t) x 4 (S.base.rm04 t x)) *
          (S.base.metric t).inner x v v) :=
      mul_le_mul_of_nonneg_left hric (by norm_num)
    _ = _ := by ring

end DifferentialGeometry.PDE.RicciFlow
