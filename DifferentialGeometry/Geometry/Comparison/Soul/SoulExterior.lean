import DifferentialGeometry.Geometry.Comparison.Soul.NoncriticalDistance
import DifferentialGeometry.Geometry.Comparison.Soul.DistanceLevelProduct

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

theorem exists_soul_set_with_exterior_products [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (hsec : ∀ x : M, metricRm04At (I := I) g x ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvex g S ∧
      relBoundary I S = ∅ ∧ maxSliceDim I S < Module.finrank ℝ E ∧
      ∀ b : ℝ, 0 < b →
        ∃ e : {q : M | b ≤ Metric.infDist q S} ≃ₜ
            {q : M | Metric.infDist q S = b} × Ici b,
          (∀ q, (e q).2.1 = Metric.infDist q.1 S) ∧
          ∀ q : {q : M | Metric.infDist q S = b},
            (e.symm (q, ⟨b, by change b ≤ b; exact le_rfl⟩)).1 = q.1 := by
  obtain ⟨S, hSne, hScomp, hSconv, hSB, hSdim, hfields⟩ :=
    exists_soul_set_with_smooth_outward_fields g hEnorm hsec p
  refine ⟨S, hSne, hScomp, hSconv, hSB, hSdim, ?_⟩
  intro b hb
  obtain ⟨V, hbound, _, hout⟩ := hfields (b / 2) b (half_pos hb) (half_lt_self hb)
  refine exists_infDist_exteriorProduct g hEnorm hScomp hSne V 2 (by norm_num) ?_ hb ?_
  · intro q
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using (hbound q).le
  · intro q hq u hu hend
    exact hout q hq u ⟨hu, hend⟩

end DifferentialGeometry.Geometry.Topology
