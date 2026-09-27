import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ClosedIntervalExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.Naturality

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]
  {D : RealTimeInterval}

theorem lRegularizedAccel_localPullback
    (S : SolutionOn (I := J) (M := N) D) (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    (T s : ℝ) (x : M) (A : TangentSpace I x) :
    mfderiv I J f x (lRegularizedAccel (S.localPullback f hf) T s x A) =
      lRegularizedAccel S T s (f x) (mfderiv I J f x A) := by
  exact mfderiv_lRegularizedAccel_of_localPullMetric (S.localPullback f hf) S hf rfl x A

theorem lRegularizedCurve_eqOn_comp_of_localPullMetric
    {D' : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (Q : SolutionOn (I := J) (M := N) D') (hQ : IsSolutionOn Q)
    (f : M → N) (hf : IsLocalDiffeomorph I J ∞ f)
    {T : ℝ} {α : ℝ → M} {K : Set ℝ} (hK : IsOpen K) (hconn : IsPreconnected K)
    (hzero : (0 : ℝ) ∈ K)
    (hmetric : ∀ r ∈ K, S.base.metric (T - r ^ 2) = localPullMetric (Q.base.metric (T - r ^ 2)) f hf)
    (hclock : ∀ r ∈ K, T - r ^ 2 ∈ D'.regular)
    {x : M} {Z : TangentSpace I x} (hα : IsLRegularizedCurveOn S T α K x Z) :
    K ⊆ lRegularizedDomain Q T (f x) (mfderiv I J f x Z) ∧
      EqOn (lRegularizedCurve Q T (f x) (mfderiv I J f x Z)) (f ∘ α) K := by
  have hmap := hα.comp_of_localPullMetric (S' := Q) hf hK hzero hmetric
    (fun r hr _ => hclock r hr)
  refine ⟨fun r hr => ⟨f ∘ α, K, hK, hconn, hzero, hr, hmap⟩, ?_⟩
  exact lRegularizedCurve_eqOn Q hQ T hK hconn hzero hmap

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology
variable {A E F H G X Y : Type*}
 [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
 [TopologicalSpace H] [TopologicalSpace G]
 {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} [I.Boundaryless] [J.Boundaryless]
 [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
 [TopologicalSpace Y] [ChartedSpace G Y] [IsManifold J ∞ Y] [T2Space Y]
 {D D' : RealTimeInterval}

theorem lRegularizedGeodesicFamily_eqOn_of_localPullMetric
    (S : SolutionOn (I := I) (M := X) D)
    (Q : SolutionOn (I := J) (M := Y) D') (hQ : IsSolutionOn Q)
    (f : X → Y) (hf : IsLocalDiffeomorph I J ∞ f) (T : ℝ)
    {α : A × ℝ → Y} {β : A × ℝ → X} {U : Set A} {K : Set ℝ} {t0 : ℝ}
    (hK : IsOpen K) (hconn : IsPreconnected K) (ht0 : t0 ∈ K)
    (hβ : ∀ a ∈ U, IsLRegularizedGeodesicOn S T (fun r => β (a, r)) K)
    (hα : ∀ a ∈ U, IsLRegularizedGeodesicOn Q T (fun r => α (a, r)) K)
    (hmetric : ∀ r ∈ K, S.base.metric (T - r ^ 2) = localPullMetric (Q.base.metric (T - r ^ 2)) f hf)
    (hclock : ∀ r ∈ K, T - r ^ 2 ∈ D'.regular)
    (hpos : ∀ a ∈ U, f (β (a, t0)) = α (a, t0))
    (hvel : ∀ a ∈ U, mfderiv I J f (β (a, t0))
      (lVelocity (I := I) (fun r => β (a, r)) t0) = lVelocity (I := J) (fun r => α (a, r)) t0) :
    EqOn (fun p : A × ℝ => f (β p)) α (U ×ˢ K) := by
  rintro ⟨a, r⟩ ⟨ha, hr⟩
  have hmap := (hβ a ha).comp_of_localPullMetric (S' := Q) hf hmetric
    (fun s hs _ => hclock s hs) (fun s hs => by
      filter_upwards [hK.mem_nhds hs] with r hr
      exact (hβ a ha r hr).2.1)
  have hphase : lVelocity (I := J) (f ∘ (fun r => β (a, r))) t0 =
      lVelocity (I := J) (fun r => α (a, r)) t0 := by
    unfold lVelocity
    rw [mfderiv_comp t0 ((hf _).contMDiffAt.mdifferentiableAt (by simp)) (hβ a ha t0 ht0).2.1]
    exact hvel a ha
  have heq := lRegularizedSolution_eqOn Q hQ T hK hconn ht0 hK hconn ht0 hmap
    (hα a ha) (hpos a ha) hphase
  exact heq ⟨hr, hr⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
