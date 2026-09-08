import DifferentialGeometry.Geometry.Metric.Family.DistanceRegularity
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.QuadraticForm
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

noncomputable section

open Manifold Set
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_lipschitzOnWith_riemannianEDistOf_toReal_of_abs_ricciTensor_le
    [PreconnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T a b K : ℝ} (hreg : Icc (T - b) (T - a) ⊆ D.regular)
    (hric : ∀ q ∈ Icc (T - b) (T - a), ∀ z : M, ∀ v : TangentSpace I z,
      |ricciTensor (S.base.metric q) z v v| ≤ K * (S.base.metric q).inner z v v)
    (x y : ℝ → M) (hx : ContMDiffOn 𝓘(ℝ, ℝ) I 1 x (Icc a b))
    (hy : ContMDiffOn 𝓘(ℝ, ℝ) I 1 y (Icc a b)) :
    ∃ L : NNReal, LipschitzOnWith L
      (fun u => (riemannianEDistOf (S.base.metric (T - u)) (x u) (y u)).toReal)
      (Icc a b) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hpde : ∀ q ∈ Icc (T - b) (T - a), ∀ z : M, ∀ v : TangentSpace I z,
      HasDerivWithinAt (fun u => (S.base.metric u).inner z v v)
        (-2 * ricciTensor (S.base.metric q) z v v) (Icc (T - b) (T - a)) q := by
    intro q hq z v
    have hraw := metricDerivAt S hS ⟨q, hreg hq⟩ z v v
    simpa [SolutionFamily.ricciAt, metricRicciAt_apply_eq_ricciTensor] using
      hraw.hasDerivWithinAt (s := Icc (T - b) (T - a))
  have htime (u : ℝ) (hu : u ∈ Icc a b) : T - u ∈ Icc (T - b) (T - a) :=
    ⟨sub_le_sub_left hu.2 T, sub_le_sub_left hu.1 T⟩
  apply exists_lipschitzOnWith_riemannianEDistOf_toReal_of_le_exp_mul_of_contMDiffOn
    (fun u => S.base.metric (T - u)) (K := K) _ x y hx hy
    (riemannianEDistOf_ne_top _ _ _)
  intro u hu v hv p q
  have hed := (riemannianEDistOf_exp_bounds_of_abs_ricciTensor_le
    (fun u => S.base.metric u) hpde hric (htime u hu) (htime v hv) p q).2
  simpa only [show (T - u) - (T - v) = v - u by ring, abs_sub_comm v u] using hed

theorem absolutelyContinuousOnInterval_riemannianEDistOf_toReal_of_abs_ricciTensor_le
    [PreconnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T a b K : ℝ} (hab : a ≤ b) (hreg : Icc (T - b) (T - a) ⊆ D.regular)
    (hric : ∀ q ∈ Icc (T - b) (T - a), ∀ z : M, ∀ v : TangentSpace I z,
      |ricciTensor (S.base.metric q) z v v| ≤ K * (S.base.metric q).inner z v v)
    (x y : ℝ → M) (hx : ContMDiffOn 𝓘(ℝ, ℝ) I 1 x (Icc a b))
    (hy : ContMDiffOn 𝓘(ℝ, ℝ) I 1 y (Icc a b)) :
    AbsolutelyContinuousOnInterval
      (fun u => (riemannianEDistOf (S.base.metric (T - u)) (x u) (y u)).toReal) a b := by
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_riemannianEDistOf_toReal_of_abs_ricciTensor_le
    S hS hreg hric x y hx hy
  have hLu : LipschitzOnWith L
      (fun u => (riemannianEDistOf (S.base.metric (T - u)) (x u) (y u)).toReal) (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hL
  exact hLu.absolutelyContinuousOnInterval

theorem absolutelyContinuousOnInterval_riemannianEDistOf_toReal_of_normSq0S_rm04_le
    [PreconnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T a b K : ℝ} (hab : a ≤ b) (hreg : Icc (T - b) (T - a) ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - b) (T - a), ∀ z : M,
      Tensor0SBundle.normSq0S (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x y : ℝ → M) (hx : ContMDiffOn 𝓘(ℝ, ℝ) I 1 x (Icc a b))
    (hy : ContMDiffOn 𝓘(ℝ, ℝ) I 1 y (Icc a b)) :
    AbsolutelyContinuousOnInterval
      (fun u => (riemannianEDistOf (S.base.metric (T - u)) (x u) (y u)).toReal) a b := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hquad := twoTensorQuadBound_of_solutions
    (fun _ : ℕ => S) Set.univ (T - b) (T - a) K (fun _ q hq z _ => hRm q hq z)
  apply absolutelyContinuousOnInterval_riemannianEDistOf_toReal_of_abs_ricciTensor_le
    S hS hab hreg (K := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K) _ x y hx hy
  intro q hq z v
  rw [← metricRicciAt_apply_eq_ricciTensor]
  exact hquad.2 0 q hq z (Set.mem_univ z) v

end DifferentialGeometry.PDE.RicciFlow
