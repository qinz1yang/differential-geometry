import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Shi.CurvatureDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureWindow

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

theorem exists_highCurvatureArcSeq_window_movingShi_bounds [CompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I3 M)] {T theta A : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hmax : ∀ i s, s ∈ Icc 0 (t i) → ∀ y : M,
      S.scalar s y ≤ S.scalar (t i) (x i))
    (htheta : 0 < theta) (htlower : ∀ᶠ i in atTop, theta ≤ t i)
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop) (hA : 0 < A) :
    ∃ N : ℕ, ∃ hcov : ∀ k,
        A ≤ ((highCurvatureArcSeq hT S hS x t htmem htpos hpos).tail N).horizon k,
      Nonempty (WindowCompactnessEstimates
        ((highCurvatureArcSeq hT S hS x t htmem htpos hpos).tail N) A hA hcov) ∧
      (∀ k m : ℕ, ∀ s ∈ Icc (-A) 0,
        ∀ y : ((((highCurvatureArcSeq hT S hS x t htmem htpos hpos).tail N).window
            A hA hcov).term k).M,
          curvDerivNorm (I := I3) m
            (((((highCurvatureArcSeq hT S hS x t htmem htpos hpos).tail N).window
              A hA hcov).term k).S.base.metric s) y ≤
            shiLocalUniformBound 3 m 16 4 * 16) ∧
      ∀ n : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ,
        MovingShiBoundOn univ (-A) 0
          (fun _ s => ((((highCurvatureArcSeq hT S hS x t htmem htpos hpos).tail N).window
            A hA hcov).term k).S.base.metric s) n K := by
  obtain ⟨N, hcov, hest, hspatial⟩ := exists_highCurvatureArcSeq_window_estimates
    hT S hS x t htmem htpos hpos hmax htheta htlower hscalar hA
  refine ⟨N, hcov, hest, hspatial, fun n => ?_⟩
  apply movingShiBoundOn_of_curvDerivNorm_on_closed_interval
    (((highCurvatureArcSeq hT S hS x t htmem htpos hpos).tail N).window A hA hcov)
    n (fun m => shiLocalUniformBound 3 m 16 4 * 16)
  exact fun k m _ s hs y => hspatial k m s hs y

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
