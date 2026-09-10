import DifferentialGeometry.Geometry.Comparison.Soul.SoulDiffeomorph
import DifferentialGeometry.Geometry.Comparison.Soul.SoulIsometricEmbedding
import DifferentialGeometry.Geometry.Comparison.Soul.SoulGeodesicPreservation

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M] [NoncompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem exists_soul_diffeomorphism
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ (S : Set M) (hconv : IsTotallyConvex g S) (hB : relBoundary I S = ∅),
      S.Nonempty ∧ IsCompact S ∧ PathConnectedSpace S ∧
      maxSliceDim I S < Module.finrank ℝ E ∧
      let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
      let _ := embeddedSliceChartedSpace hS
      let _ := embeddedSlice_isManifold hS
      IsSmoothEmbedding 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) I ∞ (Subtype.val : S → M) ∧
      Poincare.Geometry.IsRiemannianIsometricImmersion
        (inducedSliceMetric g hS) g (Subtype.val : S → M) ∧
      Poincare.Geometry.PreservesGeodesics
        (inducedSliceMetric g hS) g (Subtype.val : S → M) ∧
      let a := normalBundlePrebundle g hEnorm hconv hB
      let _ := a.totalSpaceTopology
      let _ := a.toFiberBundle
      let _ := a.toVectorBundle
      ∃ e : TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
          (normalBundleFiber g S) ≃ₘ⟮
            (𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod
              𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ), I⟯ M,
        ∀ q : S, e ⟨q, 0⟩ = q.1 := by
  obtain ⟨S, hconv, hB, hne, hcompact, hconnected, hdim, _hgeodesic, hdata⟩ :=
    exists_soul_normal_diffeomorph g hEnorm hsec p
  refine ⟨S, hconv, hB, hne, hcompact, hconnected, hdim, ?_⟩
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  obtain ⟨hembedding, hbundle⟩ := hdata
  exact ⟨hembedding,
    embeddedSlice_inclusion_isRiemannianIsometricImmersion g hEnorm hconv hB,
    embeddedSlice_inclusion_preservesGeodesics g hEnorm hconv hcompact.isClosed hB,
    hbundle⟩

end DifferentialGeometry.Geometry.Topology

end
