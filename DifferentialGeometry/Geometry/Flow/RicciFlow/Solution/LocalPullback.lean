import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
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

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  [SigmaCompactSpace N]

theorem IsSolutionOn.localPullback
    {D : RealTimeInterval} {S : SolutionOn (I := J) (M := N) D}
    (hS : IsSolutionOn S) (p : M → N) (hp : IsLocalDiffeomorph I J ∞ p) :
    IsSolutionOn (S.localPullback p hp) := by
  classical
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  choose Φ hΦmem hΦeq using fun x => hp x
  let U (x : M) : Opens M := ⟨(Φ x).source,(Φ x).open_source⟩
  apply isSolutionOn_of_open_cover (fun t => localPullMetric (S.base.metric t) p hp) U
    (fun x => ⟨x,hΦmem x⟩)
  intro x
  let e := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo (Φ x) (U := U x) (show (U x : Set M) ⊆ (Φ x).source from Subset.rfl)
  let V' : Opens N := ⟨(Φ x) '' (U x : Set M),
    DifferentialGeometry.image_opens_isOpen (Φ x) (show (U x : Set M) ⊆ (Φ x).source from Subset.rfl)⟩
  let : SigmaCompactSpace V' := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen J V'.isOpen)
  have heq (t : ℝ) : ((solutionOnRestrictOpen S V').pullback e).base.metric t =
      (localPullMetric (S.base.metric t) p hp).restrictOpen (U x) := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    change (Diffeomorph.pullbackMetricCross ((S.base.metric t).restrictOpen V') e).inner y v w = _
    rw [Diffeomorph.pullbackMetricCross_inner]
    change (S.base.metric t).inner ((Φ x) (y : M))
      (mfderiv I J (e : U x → V') y v) (mfderiv I J (e : U x → V') y w) =
      (localPullMetric (S.base.metric t) p hp).inner (y : M) v w
    have hgerm : p =ᶠ[𝓝 (y : M)] (Φ x : M → N) :=
      Filter.eventuallyEq_of_mem ((Φ x).open_source.mem_nhds y.property) (hΦeq x)
    have hdv := DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo (Φ x)
      (show (U x : Set M) ⊆ (Φ x).source from Subset.rfl) y v
    have hdw := DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo (Φ x)
      (show (U x : Set M) ⊆ (Φ x).source from Subset.rfl) y w
    calc
      _ = (S.base.metric t).inner ((Φ x) (y : M))
          (mfderiv I J (Φ x : M → N) (y : M) v)
          (mfderiv I J (Φ x : M → N) (y : M) w) :=
        congrArg₂ (fun V W => (S.base.metric t).inner ((Φ x) (y : M)) V W) hdv hdw
      _ = (S.base.metric t).inner (p (y : M))
          (mfderiv I J p (y : M) v) (mfderiv I J p (y : M) w) := by
        rw [hgerm.eq_of_nhds, hgerm.mfderiv_eq]
      _ = _ := (localPullMetric_inner (S.base.metric t) p hp (y : M) v w).symm
  exact (IsSolutionOn.pullback (solutionOnRestrictOpen S V')
    (isSolutionOn_restrictOpen S hS V') e).congr_metric (fun t _ => heq t)

end DifferentialGeometry.PDE.RicciFlow

end

set_option autoImplicit false
noncomputable section

open Bundle Set Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {D : RealTimeInterval}

theorem SolutionOn.localPullback_chartGramMatrix_joint_contMDiffOn
    (S : SolutionOn (I := J) (M := N) D) (p : M → N)
    (hp : IsLocalDiffeomorph I J ∞ p) (A : Set ℝ)
    (hg : ∀ (y₀ : N) (i j : Fin (Module.finrank ℝ F)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod J) 𝓘(ℝ) ∞
        (fun q : ℝ × N => chartGramMatrix (S.base.metric q.1) y₀ q.2 i j)
        (A ×ˢ (trivializationAt F (TangentSpace J) y₀).baseSet))
    (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun q : ℝ × M => chartGramMatrix
        ((S.localPullback p hp).base.metric q.1) x₀ q.2 i j)
      (A ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold J 1 N := IsManifold.of_le (n := ∞) (by decide)
  have hj := metricCLMSection_jointContMDiffOn_of_chartGram_on S.base.metric A hg
  exact chartGramMatrix_joint_contMDiffOn_of_pullback S.base.metric A hj
    (fun t => (S.localPullback p hp).base.metric t) p hp.contMDiff
    (fun _ _ x v w => localPullMetric_inner _ p hp x v w) x₀ i j

end DifferentialGeometry.PDE.RicciFlow
