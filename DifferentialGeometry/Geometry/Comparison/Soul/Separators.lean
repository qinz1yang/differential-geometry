import DifferentialGeometry.Geometry.Comparison.Soul.ShavingChain
import DifferentialGeometry.Geometry.Comparison.Soul.BusemannLevels

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem exists_soul_set_with_convex_separators [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvex (I := I) g S ∧
      relBoundary I S = ∅ ∧ maxSliceDim I S < Module.finrank ℝ E ∧
      ∀ r ∉ S, ∃ C : Set M, IsCompact C ∧ IsPreconnected C ∧
        IsTotallyConvex (I := I) g C ∧ r ∈ relBoundary I C ∧ S ⊆ maxSliceLocus I C := by
  obtain ⟨n, _, hSne, hScomp, hSconv, hSB, hSdim⟩ := exists_soul_shavingSequence g hEnorm hsec p
  let S := shavingSequence I (rayBusemannSublevel p 1) n
  refine ⟨S, hSne, hScomp, hSconv, hSB, hSdim, ?_⟩
  intro r hr
  have hsep : ∃ C : Set M, IsCompact C ∧ IsTotallyConvex (I := I) g C ∧
      r ∈ relBoundary I C ∧ S ⊆ maxSliceLocus I C := by
    by_cases hrC : r ∈ rayBusemannSublevel p 1
    · obtain ⟨k, _, hcomp, hconv, hrB, hSN⟩ := shavingSequence_separator g hEnorm
        (shavingConcavity_of_sec_nonneg' g hEnorm hsec)
        (isCompact_rayBusemannSublevel g hEnorm hsec p 1)
        ⟨p, self_mem_rayBusemannSublevel p zero_le_one⟩
        (isTotallyConvex_rayBusemannSublevel g hEnorm hsec p 1) hrC hr
      exact ⟨_, hcomp, hconv, hrB, hSN⟩
    · obtain ⟨hcomp, hconv, hrB, hcore⟩ := rayExhaustion_separator g hEnorm hsec p r hrC
      exact ⟨_, hcomp, hconv, hrB, (shavingSequence_subset I _ n).trans hcore⟩
  obtain ⟨C, hcomp, hconv, hrB, hSN⟩ := hsep
  exact ⟨C, hcomp,
    (IsTotallyConvex.isPathConnected g hEnorm hconv ⟨r, relBoundary_subset hrB⟩).isConnected.isPreconnected,
    hconv, hrB, hSN⟩

end DifferentialGeometry.Geometry.Topology
