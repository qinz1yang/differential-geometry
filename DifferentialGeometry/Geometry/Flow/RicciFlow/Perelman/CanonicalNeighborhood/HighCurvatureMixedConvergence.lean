import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactTimeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

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
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem highCurvatureFlowSequence_ancient_limit_mixed_convergence
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (P : MetricCompactLimit
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0))
    (N : ℕ → ℕ)
    (F : ∀ n, ℕ → SolutionOn (I := I3) (M := metricSourceOpenSubset P.maps n)
      (RealTimeInterval.closed (-(((n + 1 : ℕ) : ℝ) + 1)) 0 (by
        have := Nat.cast_nonneg (α := ℝ) (n + 1); linarith)))
    (hF : ∀ n i, IsSolutionOn (F n i))
    (hsource : ∀ n i, (metricSourceOpenSubset P.maps n : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (i + N n)).source)
    (hmetric : ∀ n i s (y : metricSourceOpenSubset P.maps n) (v w : TangentSpace I3 y),
      ((F n i).base.metric s).inner y v w =
        (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term
          (P.subseq (i + N n))).S.base.metric s).inner
          (P.maps.partialDiffeomorph (i + N n) y)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) y v)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) y w))
    (rho : ℕ → ℕ) (hrho : StrictMono rho)
    (G : ℝ → SmoothRiemannianMetric I3 P.limit.M)
    (hG : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.limit.M)
      (RealTimeInterval.infiniteClosed 0 0 le_rfl)))
    (hconv : ∀ n, ∀ K : Set (metricSourceOpenSubset P.maps n), IsCompact K →
      ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ j : ℕ, ∀ i ≥ j,
        ∀ s ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0,
          metricDerivNormSupOn K p ((F n (rho i - N n)).base.metric s)
            ((G s).restrictOpen (metricSourceOpenSubset P.maps n))
            (P.limit.metric.restrictOpen (metricSourceOpenSubset P.maps n)) < epsilon) :
    ∀ K : Set P.limit.M, IsCompact K → ∀ A : ℝ, 0 < A →
      ∀ order : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ i in atTop,
        K ⊆ (P.maps.partialDiffeomorph (rho i)).source ∧
        Nonempty (MetricComparisonOn G
          (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term
            (P.subseq (rho i))).S.base.metric)
          (P.maps.partialDiffeomorph (rho i)) K (Icc (-A) 0) order epsilon) := by
  intro K hK A hA order epsilon hepsilon
  let U := metricSourceOpenSubset P.maps
  obtain ⟨nk, hnk⟩ := P.maps.source_exhausts.subset K hK
  obtain ⟨nt, hnt⟩ := exists_nat_ge A
  let n := max nk nt
  have hKn : K ⊆ U n := hnk n (le_max_left _ _)
  have hnpos : (0 : ℝ) < (n + 1 : ℕ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have htimes : Icc (-A) 0 ⊆ Icc (-((n + 1 : ℕ) : ℝ)) 0 := by
    intro s hs
    have hntn : (nt : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (le_max_right _ _)
    rw [Nat.cast_add, Nat.cast_one]
    exact ⟨by linarith [hs.1], hs.2⟩
  let D := RealTimeInterval.closed (-(((n + 1 : ℕ) : ℝ) + 1)) 0 (by linarith)
  let L : SolutionOn (I := I3) (M := P.limit.M)
      (RealTimeInterval.infiniteClosed 0 0 le_rfl) := { base.metric := G }
  let L' := L.timeRestrict D
  have hL' : IsSolutionOn L' := isSolutionOn_timeRestrict hG
    (fun _ hs => hs.2) (fun _ hs => hs.2)
  have hcompare := eventually_metricComparisonOn_of_local_flow_convergence
    (U n) (fun i => F n (rho i - N n)) (fun i => hF n (rho i - N n)) L' hL'
    (show -(((n + 1 : ℕ) : ℝ) + 1) < -((n + 1 : ℕ) : ℝ) by linarith)
    (neg_neg_of_pos hnpos) rfl Subset.rfl (P.limit.metric.restrictOpen (U n))
    (hconv n)
    (fun i => ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term
      (P.subseq (rho i - N n + N n))).S.base.metric)
    (fun i => P.maps.partialDiffeomorph (rho i - N n + N n))
    (fun i => hmetric n (rho i - N n)) (uniqueDiffOn_Icc (neg_neg_of_pos hA)) htimes
    hK hKn order hepsilon
  filter_upwards [hcompare, eventually_ge_atTop (N n)] with i hi hiN
  have heq : rho i - N n + N n = rho i := Nat.sub_add_cancel (hiN.trans (hrho.id_le i))
  have hsrc := hsource n (rho i - N n)
  rw [heq] at hi hsrc
  exact ⟨hKn.trans hsrc, hi⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
