import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.LocalInverse
import DifferentialGeometry.Geometry.Metric.OpenSubtype
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Topology.Manifold.ConnectedComponent

open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Bundle Manifold Set TopologicalSpace
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential
namespace LocalAddition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

noncomputable def connectedComponentMetric
    (g : SmoothRiemannianMetric I M) (p : M) :
    SmoothRiemannianMetric I (connectedComponentOpen (I := I) p) := by
  letI : CompactSpace (connectedComponentOpen (I := I) p) := connectedComponentOpen_compactSpace (I := I) p
  exact g.restrictOpen (I := I) (connectedComponentOpen (I := I) p)

section

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

@[reducible] private noncomputable def connectedComponentRiemannianBundle
    (g : SmoothRiemannianMetric I M) (p : M) :
    RiemannianBundle
      (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
  ⟨(connectedComponentMetric (I := I) g p).toRiemannianMetric⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
private theorem connectedComponentContinuousRiemannianBundle
    (g : SmoothRiemannianMetric I M) (p : M) :
    letI : RiemannianBundle
        (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
      connectedComponentRiemannianBundle (I := I) g p
    IsContinuousRiemannianBundle E
      (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) := by
  let : RiemannianBundle
      (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
    connectedComponentRiemannianBundle (I := I) g p
  exact
    ⟨(connectedComponentMetric (I := I) g p).inner,
      (connectedComponentMetric (I := I) g p).contMDiff.continuous,
      fun _ _ _ => rfl⟩

@[reducible] private noncomputable def connectedComponentPseudoEMetricSpace
    (g : SmoothRiemannianMetric I M) (p : M) :
    letI : RiemannianBundle
        (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
      connectedComponentRiemannianBundle (I := I) g p
    PseudoEMetricSpace (connectedComponentOpen (I := I) p) := by
  letI : CompactSpace (connectedComponentOpen (I := I) p) := connectedComponentOpen_compactSpace (I := I) p
  letI : RiemannianBundle
      (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
    connectedComponentRiemannianBundle (I := I) g p
  letI : IsContinuousRiemannianBundle E
      (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
    connectedComponentContinuousRiemannianBundle (I := I) g p
  exact PseudoEMetricSpace.ofRiemannianMetric I (connectedComponentOpen (I := I) p)

omit [NeZero (Module.finrank ℝ E)] in
private theorem connectedComponentIsRiemannianManifold
    (g : SmoothRiemannianMetric I M) (p : M) :
    letI : RiemannianBundle
        (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
      connectedComponentRiemannianBundle (I := I) g p
    letI : PseudoEMetricSpace (connectedComponentOpen (I := I) p) :=
      connectedComponentPseudoEMetricSpace (I := I) g p
    IsRiemannianManifold I (connectedComponentOpen (I := I) p) := by
  let : RiemannianBundle
      (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
    connectedComponentRiemannianBundle (I := I) g p
  let : PseudoEMetricSpace (connectedComponentOpen (I := I) p) :=
    connectedComponentPseudoEMetricSpace (I := I) g p
  exact ⟨fun _ _ => rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] in
private theorem connectedComponent_isMetricNorm
    (g : SmoothRiemannianMetric I M) (p : M) :
    letI : RiemannianBundle
        (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
      connectedComponentRiemannianBundle (I := I) g p
    IsMetricNorm (I := I) (M := connectedComponentOpen (I := I) p)
      (connectedComponentMetric (I := I) g p) := by
  let : RiemannianBundle
      (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
    connectedComponentRiemannianBundle (I := I) g p
  intro x v
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

noncomputable def connectedComponentDiagonalExponential
    (g : SmoothRiemannianMetric I M) (p : M) :
    TangentBundle I (connectedComponentOpen (I := I) p) →
      connectedComponentOpen (I := I) p × connectedComponentOpen (I := I) p := by
  letI : ConnectedSpace (connectedComponentOpen (I := I) p) := connectedComponentOpen_connectedSpace (I := I) p
  letI : CompactSpace (connectedComponentOpen (I := I) p) := connectedComponentOpen_compactSpace (I := I) p
  letI : RiemannianBundle
      (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
    connectedComponentRiemannianBundle (I := I) g p
  letI : IsContinuousRiemannianBundle E
      (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
    connectedComponentContinuousRiemannianBundle (I := I) g p
  letI : PseudoEMetricSpace (connectedComponentOpen (I := I) p) :=
    connectedComponentPseudoEMetricSpace (I := I) g p
  letI : IsRiemannianManifold I (connectedComponentOpen (I := I) p) :=
    connectedComponentIsRiemannianManifold (I := I) g p
  exact diagExp (I := I) (connectedComponentMetric (I := I) g p)
    (connectedComponent_isMetricNorm (I := I) g p)

end

noncomputable def localAdditionCoordinateMap
    (g : SmoothRiemannianMetric I M) (p : M) : E × E → E × E :=
  let z : TangentBundle I (connectedComponentOpen (I := I) p) :=
    (⟨connectedComponentPoint (I := I) p, (0 : E)⟩ :
      TangentBundle I (connectedComponentOpen (I := I) p))
  extChartAt (I.prod I) (connectedComponentDiagonalExponential (I := I) g p z) ∘
    connectedComponentDiagonalExponential (I := I) g p ∘
    (extChartAt I.tangent z).symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
@[simp] theorem connectedComponentDiagonalExponential_zero
    (g : SmoothRiemannianMetric I M) (p : M) :
    connectedComponentDiagonalExponential (I := I) g p
        (⟨connectedComponentPoint (I := I) p, (0 : E)⟩ :
          TangentBundle I (connectedComponentOpen (I := I) p)) =
      (connectedComponentPoint (I := I) p, connectedComponentPoint (I := I) p) := by
  classical
  let : ConnectedSpace (connectedComponentOpen (I := I) p) := connectedComponentOpen_connectedSpace (I := I) p
  let : CompactSpace (connectedComponentOpen (I := I) p) := connectedComponentOpen_compactSpace (I := I) p
  let : RiemannianBundle
      (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
    connectedComponentRiemannianBundle (I := I) g p
  let : IsContinuousRiemannianBundle E
      (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
    connectedComponentContinuousRiemannianBundle (I := I) g p
  let : PseudoEMetricSpace (connectedComponentOpen (I := I) p) :=
    connectedComponentPseudoEMetricSpace (I := I) g p
  let : IsRiemannianManifold I (connectedComponentOpen (I := I) p) :=
    connectedComponentIsRiemannianManifold (I := I) g p
  change diagExp (I := I) (connectedComponentMetric (I := I) g p)
      (connectedComponent_isMetricNorm (I := I) g p)
      (⟨connectedComponentPoint (I := I) p, (0 : E)⟩ :
        TangentBundle I (connectedComponentOpen (I := I) p)) = _
  rw [diagExp_apply]
  exact Prod.ext rfl
    (expMapIntrinsic_zero (I := I) (connectedComponentMetric (I := I) g p)
      (connectedComponent_isMetricNorm (I := I) g p) (connectedComponentPoint (I := I) p))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem connectedComponentDiagonalExponential_contMDiffAt_zero
    (g : SmoothRiemannianMetric I M) (p : M) (n : ℕ) :
    ContMDiffAt I.tangent (I.prod I) (n : ℕ∞)
      (connectedComponentDiagonalExponential (I := I) g p)
      (⟨connectedComponentPoint (I := I) p, (0 : E)⟩ :
        TangentBundle I (connectedComponentOpen (I := I) p)) := by
  classical
  let : ConnectedSpace (connectedComponentOpen (I := I) p) := connectedComponentOpen_connectedSpace (I := I) p
  let : CompactSpace (connectedComponentOpen (I := I) p) := connectedComponentOpen_compactSpace (I := I) p
  let : RiemannianBundle
      (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
    connectedComponentRiemannianBundle (I := I) g p
  let : IsContinuousRiemannianBundle E
      (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
    connectedComponentContinuousRiemannianBundle (I := I) g p
  let : PseudoEMetricSpace (connectedComponentOpen (I := I) p) :=
    connectedComponentPseudoEMetricSpace (I := I) g p
  let : IsRiemannianManifold I (connectedComponentOpen (I := I) p) :=
    connectedComponentIsRiemannianManifold (I := I) g p
  change ContMDiffAt I.tangent (I.prod I) (n : ℕ∞)
    (diagExp (I := I) (connectedComponentMetric (I := I) g p)
      (connectedComponent_isMetricNorm (I := I) g p))
    (⟨connectedComponentPoint (I := I) p, (0 : E)⟩ :
      TangentBundle I (connectedComponentOpen (I := I) p))
  exact diagExp_contMDiffAt_zero (I := I)
    (connectedComponentMetric (I := I) g p) (connectedComponent_isMetricNorm (I := I) g p)
    (connectedComponentPoint (I := I) p) n

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem localAdditionCoordinateMap_hasFDerivAt
    (g : SmoothRiemannianMetric I M) (p : M) (n : ℕ) (hn : 1 ≤ n) :
    HasFDerivAt (localAdditionCoordinateMap (I := I) g p)
      (DifferentialGeometry.PhaseFlow.freeDiagCLE (E := E) : (E × E) →L[ℝ] (E × E))
      (extChartAt I.tangent
        (⟨connectedComponentPoint (I := I) p, (0 : E)⟩ :
          TangentBundle I (connectedComponentOpen (I := I) p))
        (⟨connectedComponentPoint (I := I) p, (0 : E)⟩ :
          TangentBundle I (connectedComponentOpen (I := I) p))) := by
  classical
  let : ConnectedSpace (connectedComponentOpen (I := I) p) := connectedComponentOpen_connectedSpace (I := I) p
  let : CompactSpace (connectedComponentOpen (I := I) p) := connectedComponentOpen_compactSpace (I := I) p
  let : RiemannianBundle
      (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
    connectedComponentRiemannianBundle (I := I) g p
  let : IsContinuousRiemannianBundle E
      (fun x : connectedComponentOpen (I := I) p ↦ TangentSpace I x) :=
    connectedComponentContinuousRiemannianBundle (I := I) g p
  let : PseudoEMetricSpace (connectedComponentOpen (I := I) p) :=
    connectedComponentPseudoEMetricSpace (I := I) g p
  let : IsRiemannianManifold I (connectedComponentOpen (I := I) p) :=
    connectedComponentIsRiemannianManifold (I := I) g p
  have h := diagExp_hasFDerivAt_zero_linearEquiv (I := I)
    (connectedComponentMetric (I := I) g p) (connectedComponent_isMetricNorm (I := I) g p)
    (connectedComponentPoint (I := I) p) n hn
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ ↦ rfl)

end LocalAddition
end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
