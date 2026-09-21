import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Defs
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.OpenCover

noncomputable section

section

open Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {D : RealTimeInterval}

def SolutionOn.localPullback
    (S : SolutionOn (I := J) (M := N) D) (p : M → N)
    (hp : IsLocalDiffeomorph I J ∞ p) : SolutionOn (I := I) (M := M) D where
  base := { metric := fun t => localPullMetric (S.base.metric t) p hp }

omit [FiniteDimensional ℝ F] in
@[simp] theorem SolutionOn.localPullback_metric
    (S : SolutionOn (I := J) (M := N) D) (p : M → N)
    (hp : IsLocalDiffeomorph I J ∞ p) (t : ℝ) :
    (S.localPullback p hp).base.metric t = localPullMetric (S.base.metric t) p hp := rfl

variable [T2Space N] [I.Boundaryless] [J.Boundaryless]

theorem SolutionOn.localPullback_scalar
    (S : SolutionOn (I := J) (M := N) D) (p : M → N)
    (hp : IsLocalDiffeomorph I J ∞ p) (t : ℝ) (x : M) :
    (S.localPullback p hp).scalar t x = S.scalar t (p x) := by
  exact metricScalarAt_localPull (S.base.metric t) p hp x

end DifferentialGeometry.PDE.RicciFlow

end

section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature

variable {E H M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [SigmaCompactSpace N] {D : RealTimeInterval}

theorem IsSolutionOn.localPullback
    {S : SolutionOn (I := I) (M := N) D} (hS : IsSolutionOn S)
    (p : M → N) (hp : IsLocalDiffeomorph I I ∞ p) :
    IsSolutionOn (S.localPullback p hp) := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  choose Φ hΦmem hΦeq using fun x => hp x
  let U (x : M) : Opens M := ⟨(Φ x).source, (Φ x).open_source⟩
  apply isSolutionOn_of_open_cover (fun t => localPullMetric (S.base.metric t) p hp) U
    (fun x => ⟨x, hΦmem x⟩)
  intro x
  let : SigmaCompactSpace ((Φ x).toOpenPartialHomeomorph.target) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I (Φ x).open_target)
  let : SigmaCompactSpace (U x) :=
    (Φ x).toOpenPartialHomeomorph.toHomeomorphSourceTarget.isClosedEmbedding.sigmaCompactSpace
  have hmet (t : ℝ) (y : M) (hy : y ∈ U x) (v w : TangentSpace I y) :
      (localPullMetric (S.base.metric t) p hp).inner y v w =
        (S.family.metric t).inner (Φ x y)
          (mfderiv I I (Φ x) y v) (mfderiv I I (Φ x) y w) := by
    have hgerm : p =ᶠ[𝓝 y] (Φ x : M → N) :=
      Filter.eventuallyEq_of_mem ((Φ x).open_source.mem_nhds hy) (hΦeq x)
    rw [localPullMetric_inner, hgerm.mfderiv_eq, hgerm.eq_of_nhds]
    rfl
  obtain ⟨S', hS', heq⟩ := Perelman.KappaSolutions.exists_local_solution_of_pullback
    S hS (Φ x) (U x) Subset.rfl (fun t => localPullMetric (S.base.metric t) p hp) hmet
  exact hS'.congr_metric (fun t _ => heq t)

end DifferentialGeometry.PDE.RicciFlow

end
