import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Product
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Stationary
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Product
import DifferentialGeometry.Geometry.Metric.Euclidean
import DifferentialGeometry.Geometry.Metric.Scaling

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow

theorem metricRm04At_scaleMetric_euclideanMetric (c : ℝ) (hc : 0 < c) :
    ∀ (y : ℝ) (w : Fin 4 → TangentSpace 𝓘(ℝ, ℝ) y),
      metricRm04At (DifferentialGeometry.scaleMetric (I := 𝓘(ℝ, ℝ)) c hc
        (DifferentialGeometry.euclideanMetric (E := ℝ))) y w = 0 := by
  intro y w
  rw [← metricRm04_apply (I := 𝓘(ℝ, ℝ)) (M := ℝ)
    (g := DifferentialGeometry.scaleMetric (I := 𝓘(ℝ, ℝ)) c hc
      (DifferentialGeometry.euclideanMetric (E := ℝ))) (x := y),
    DifferentialGeometry.Geometry.Curvature.metricRm_scale (I := 𝓘(ℝ, ℝ)) (M := ℝ)
      (c := c) (hc := hc) (g := DifferentialGeometry.euclideanMetric (E := ℝ)) y,
    metricRm04_apply (I := 𝓘(ℝ, ℝ)) (M := ℝ)
      (g := DifferentialGeometry.euclideanMetric (E := ℝ)) (x := y),
    metricRm04At_eq_zero_of_finrank_le_one (I := 𝓘(ℝ, ℝ)) (M := ℝ)
      (g := DifferentialGeometry.euclideanMetric (E := ℝ)) (hE := by simp) y]
  simp

theorem metricRicciAt_scaleMetric_euclideanMetric (c : ℝ) (hc : 0 < c) :
    ∀ (y : ℝ) (w : Fin 2 → TangentSpace 𝓘(ℝ, ℝ) y),
      metricRicciAt (DifferentialGeometry.scaleMetric (I := 𝓘(ℝ, ℝ)) c hc
        (DifferentialGeometry.euclideanMetric (E := ℝ))) y w = 0 := by
  intro y w
  have hw : w = (vec2 (I := 𝓘(ℝ, ℝ)) (x := y) (w 0) (w 1) :
      Fin 2 → TangentSpace 𝓘(ℝ, ℝ) y) := by
    funext i
    fin_cases i <;> rfl
  conv_lhs => rw [hw]
  rw [DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor
      (g := DifferentialGeometry.scaleMetric (I := 𝓘(ℝ, ℝ)) c hc
        (DifferentialGeometry.euclideanMetric (E := ℝ))) y (w 0) (w 1),
    DifferentialGeometry.Geometry.Curvature.ricciTensor_apply_basisSum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [DifferentialGeometry.Geometry.Curvature.riemannOp_eq_zero_of_finrank_le_one
    (I := 𝓘(ℝ, ℝ)) (M := ℝ)
    (cov := DifferentialGeometry.Geometry.Connection.LeviCivita (I := 𝓘(ℝ, ℝ))
      (DifferentialGeometry.scaleMetric (I := 𝓘(ℝ, ℝ)) c hc
        (DifferentialGeometry.euclideanMetric (E := ℝ))))
    (by simp) y _ _ _]
  simp

theorem isSolutionOn_const_scaleMetric_euclideanMetric (c : ℝ) (hc : 0 < c)
    (D : RealTimeInterval) :
    IsSolutionOn (SolutionOn.const (DifferentialGeometry.scaleMetric (I := 𝓘(ℝ, ℝ)) c hc
      (DifferentialGeometry.euclideanMetric (E := ℝ))) D) := by
  refine isSolutionOn_const_of_ricciTensor_eq_zero (DifferentialGeometry.scaleMetric
    (I := 𝓘(ℝ, ℝ)) c hc (DifferentialGeometry.euclideanMetric (E := ℝ))) ?_ D
  intro y v w
  rw [← DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor
    (g := DifferentialGeometry.scaleMetric (I := 𝓘(ℝ, ℝ)) c hc
      (DifferentialGeometry.euclideanMetric (E := ℝ))) y v w]
  exact metricRicciAt_scaleMetric_euclideanMetric c hc y
    (vec2 (I := 𝓘(ℝ, ℝ)) (x := y) v w)

section Product

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem isSolutionOn_prod_scaleMetric_euclideanMetric [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (c : ℝ) (hc : 0 < c) :
    IsSolutionOn (S.prod (SolutionOn.const (DifferentialGeometry.scaleMetric
      (I := 𝓘(ℝ, ℝ)) c hc (DifferentialGeometry.euclideanMetric (E := ℝ))) D)) :=
  isSolutionOn_prod S hS _ (isSolutionOn_const_scaleMetric_euclideanMetric c hc D)

theorem normSq0S_iterCov_rm04_prod_of_flat [I.Boundaryless] [BoundarylessManifold I M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K} {N : Type*} [TopologicalSpace N]
    [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] [J.Boundaryless] [BoundarylessManifold J N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (hflat : ∀ (y : N) (w : Fin 4 → TangentSpace J y), metricRm04At h y w = 0)
    (m : ℕ) (p : M × N) :
    normSq0S (g.prod h) p (4 + m) (iterCov (g.prod h) 4 (metricRm04 (g.prod h)) m p) =
      normSq0S g p.1 (4 + m) (iterCov g 4 (metricRm04 g) m p.1) :=
  normSq0S_prod_of_forall_fst (I := I) (J := J) g h p (4 + m) _ _
    (fun slots => iterCov_prod_flat_apply (I := I) (J := J) g h hflat m p slots)

theorem normSq0S_iterCov_ricci_prod_of_ricciFlat [I.Boundaryless] [BoundarylessManifold I M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {K : Type*} [TopologicalSpace K] {J : ModelWithCorners ℝ F K} {N : Type*} [TopologicalSpace N]
    [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] [J.Boundaryless] [BoundarylessManifold J N]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (hflat : ∀ (y : N) (w : Fin 2 → TangentSpace J y), metricRicciAt h y w = 0)
    (m : ℕ) (p : M × N) :
    normSq0S (g.prod h) p (2 + m) (iterCov (g.prod h) 2 (metricRicci (g.prod h)) m p) =
      normSq0S g p.1 (2 + m) (iterCov g 2 (metricRicci g) m p.1) :=
  normSq0S_prod_of_forall_fst (I := I) (J := J) g h p (2 + m) _ _
    (fun slots => iterCov_ricci_prod_flat_apply (I := I) (J := J) g h hflat m p slots)

end Product

end DifferentialGeometry.PDE.RicciFlow
