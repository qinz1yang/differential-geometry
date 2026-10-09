import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureBackwardLimits
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.AncientGluing

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [CompactSpace M]
theorem exists_highCurvatureFlowSequence_ancient_metric_limit
    {T theta : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (hmax : ∀ i s, s ∈ Icc 0 (t i) → ∀ y : M,
      S.scalar s y ≤ S.scalar (t i) (x i))
    (htheta : 0 < theta) (htlower : ∀ᶠ i in atTop, theta ≤ t i)
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop)
    (P : MetricCompactLimit
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0))
    (hcanonical : ∀ i, P.convergence.metrics.domain i =
      CanonicalMetricCompactness.canonicalSourceData P.maps i)
    (hcompact : ∀ n, IsCompact (closure (P.maps.source n))) :
    let U := metricSourceOpenSubset P.maps
    ∃ N : ℕ → ℕ,
      ∃ F : ∀ n, ℕ → SolutionOn (I := I3) (M := U n)
          (RealTimeInterval.closed (-(((n + 1 : ℕ) : ℝ) + 1)) 0 (by
            have := Nat.cast_nonneg (α := ℝ) (n + 1); linarith)),
        (∀ n i, IsSolutionOn (F n i)) ∧
        (∀ n i, (U n : Set P.limit.M) ⊆ (P.maps.partialDiffeomorph (i + N n)).source) ∧
        (∀ n i s (y : U n) (v w : TangentSpace I3 y),
          ((F n i).base.metric s).inner y v w =
            (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term
              (P.subseq (i + N n))).S.base.metric s).inner
              (P.maps.partialDiffeomorph (i + N n) y)
              (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) y v)
              (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) y w)) ∧
        ∃ rho : ℕ → ℕ, StrictMono rho ∧ ∃ G : ℝ → SmoothRiemannianMetric I3 P.limit.M,
          G 0 = P.limit.metric ∧
          IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.limit.M)
            (RealTimeInterval.infiniteClosed 0 0 le_rfl)) ∧
          ∀ n, ∀ K : Set (U n), IsCompact K → ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
            ∃ j : ℕ, ∀ i ≥ j, ∀ s ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0,
              metricDerivNormSupOn K p ((F n (rho i - N n)).base.metric s)
                ((G s).restrictOpen (U n)) (P.limit.metric.restrictOpen (U n)) < epsilon := by
  let U := metricSourceOpenSubset P.maps
  have hcover : ∀ y : P.limit.M, ∃ n, y ∈ U n := by
    intro y
    obtain ⟨n, hn⟩ := P.maps.source_exhausts.subset {y} isCompact_singleton
    exact ⟨n, hn n le_rfl (mem_singleton y)⟩
  have hmono : Monotone U := P.maps.source_exhausts.monotone
  obtain ⟨N, F, hF, hsource, hmetric, rho, hrho, g, hg0, hgsol, hconv, hoverlap⟩ :=
    exists_highCurvatureFlowSequence_compatible_local_backward_flows
      hT S hS x t htmem htpos hpos hmax htheta htlower hscalar P hcanonical U
      (fun n => P.maps.base_mem n) hcompact (fun n => ((n + 1 : ℕ) : ℝ))
      (fun n => Nat.cast_pos.mpr (Nat.succ_pos n))
  obtain ⟨G, hGsol, hG⟩ := exists_ancient_solution_of_compatible_open_cover
    U hmono hcover g hgsol (fun n m s hn hm =>
      hoverlap n m (U n ⊓ U m) inf_le_left inf_le_right s hn hm)
  refine ⟨N, F, hF, hsource, hmetric, rho, hrho, G, ?_, hGsol, ?_⟩
  · apply SmoothRiemannianMetric.ext_inner
    intro y v w
    obtain ⟨n, hyn⟩ := hcover y
    have heq := (hG n 0 ⟨neg_nonpos.mpr (Nat.cast_nonneg _), le_rfl⟩).trans (hg0 n)
    exact congrArg (fun k : SmoothRiemannianMetric I3 (U n) => k.inner ⟨y, hyn⟩ v w) heq
  · intro n K hK p epsilon hepsilon
    obtain ⟨j, hj⟩ := hconv n K hK p epsilon hepsilon
    refine ⟨j, fun i hi s hs => ?_⟩
    rw [hG n s hs]
    exact hj i hi s hs

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
