import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureSequence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange

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

theorem highCurvatureFlowSequence_ancient_limit_pointed_convergence
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : ℕ → M) (t : ℕ → ℝ)
    (htmem : ∀ i, t i ∈ Ico (0 : ℝ) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (P : MetricCompactLimit
      ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime 0))
    (N : ℕ → ℕ)
    (F : ∀ n, ℕ → ℝ → SmoothRiemannianMetric I3 (metricSourceOpenSubset P.maps n))
    (hsource : ∀ n i, (metricSourceOpenSubset P.maps n : Set P.limit.M) ⊆
      (P.maps.partialDiffeomorph (i + N n)).source)
    (hmetric : ∀ n i s (y : metricSourceOpenSubset P.maps n) (v w : TangentSpace I3 y),
      (F n i s).inner y v w =
        (((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).term
          (P.subseq (i + N n))).S.base.metric s).inner
          (P.maps.partialDiffeomorph (i + N n) y)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) y v)
          (mfderiv I3 I3 (P.maps.partialDiffeomorph (i + N n)) y w))
    (rho : ℕ → ℕ) (hrho : StrictMono rho)
    (G : ℝ → SmoothRiemannianMetric I3 P.limit.M)
    (hconv : ∀ n, ∀ K : Set (metricSourceOpenSubset P.maps n), IsCompact K →
      ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon → ∃ j : ℕ, ∀ i ≥ j,
        ∀ s ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0,
          metricDerivNormSupOn K p (F n (rho i - N n) s)
            ((G s).restrictOpen (metricSourceOpenSubset P.maps n))
            (P.limit.metric.restrictOpen (metricSourceOpenSubset P.maps n)) < epsilon) :
    ∀ s ≤ 0,
      let Q : PointedRiemannianManifold I3 := { P.limit with metric := G s }
      ∃ Psi : PointedRiemannianConvergenceMaps
          ((highCurvatureFlowSequence hT S hS x t htmem htpos hpos).atTime s) Q (P.subseq ∘ rho),
        (∀ i, Psi.partialDiffeomorph i = P.maps.partialDiffeomorph (rho i)) ∧
        ∃ C : MetricConvergenceData Psi,
          ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData Psi i := by
  intro s hs
  let U := metricSourceOpenSubset P.maps
  let Q : PointedRiemannianManifold I3 := { P.limit with metric := G s }
  let X := highCurvatureFlowSequence hT S hS x t htmem htpos hpos
  let Psi : PointedRiemannianConvergenceMaps (X.atTime s) Q (P.subseq ∘ rho) := {
    partialDiffeomorph := fun i => P.maps.partialDiffeomorph (rho i)
    source_exhausts := P.maps.source_exhausts.comp_subseq hrho
    base_mem := fun i => P.maps.base_mem (rho i)
    basepoint_map := fun i => P.maps.basepoint_map (rho i) }
  refine ⟨Psi, fun _ => rfl, ?_⟩
  apply exists_canonicalMetricConvergenceData_of_local_pullback Psi
  intro K hK
  obtain ⟨nk, hnk⟩ := P.maps.source_exhausts.subset K hK
  obtain ⟨nt, hnt⟩ := exists_nat_ge (-s)
  let n := max nk nt
  have hKn : K ⊆ U n := hnk n (le_max_left _ _)
  have hsn : s ∈ Icc (-((n + 1 : ℕ) : ℝ)) 0 := by
    have hntn : (nt : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (le_max_right _ _)
    rw [Nat.cast_add, Nat.cast_one]
    exact ⟨by linarith, hs⟩
  let A : ℕ → SmoothRiemannianMetric I3 (U n) := fun i => F n (rho i - N n) s
  have hc : MetricCInfConvergenceOnCompacts A ((G s).restrictOpen (U n))
      (P.limit.metric.restrictOpen (U n)) := by
    intro L hL p epsilon hepsilon
    obtain ⟨j, hj⟩ := hconv n L hL p epsilon hepsilon
    exact ⟨j, fun i hi => hj i hi s hsn⟩
  refine ⟨U n, hKn, A, hc.change_reference ((G s).restrictOpen (U n)), ?_⟩
  filter_upwards [eventually_ge_atTop (N n)] with i hi
  have heq : rho i - N n + N n = rho i := Nat.sub_add_cancel (hi.trans (hrho.id_le i))
  constructor
  · have h := hsource n (rho i - N n)
    rw [heq] at h
    exact h
  · intro y v w
    have h := hmetric n (rho i - N n) s y v w
    rw [heq] at h
    exact h

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
