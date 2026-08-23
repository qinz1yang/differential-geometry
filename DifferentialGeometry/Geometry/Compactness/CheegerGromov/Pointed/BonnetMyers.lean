import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Defs
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Headlines
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentNormDiamond

open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold Topology

set_option autoImplicit false

noncomputable section

universe u

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

namespace PointedRiemannianManifold

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem compact_of_ricci
    [NeZero (Module.finrank Real E)]
    [I.Boundaryless]
    {P : PointedRiemannianManifold.{u} (I := I)}
    (hconn :
      letI : TopologicalSpace P.M := P.topology
      ConnectedSpace P.M)
    (hdim : 2 <= Module.finrank Real E)
    {K : Real} (hK : 0 < K)
    (hRic :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      letI : SigmaCompactSpace P.M := P.sigmaCompact
      letI : T2Space P.M := P.t2
      DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
        (I := I) P.metric (((Module.finrank Real E : Real) - 1) * K))
    (hcomplete : MetricComplete (I := I) P) :
    letI : TopologicalSpace P.M := P.topology
    CompactSpace P.M := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : T2Space P.M := P.t2
  letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
  letI : ConnectedSpace P.M := hconn
  let g := P.metric
  letI cg : Bundle.ContinuousRiemannianMetric E (TangentSpace I : P.M → Type _) :=
    g.toContinuousRiemannianMetric
  letI rb : Bundle.RiemannianBundle (TangentSpace I : P.M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  letI : TopologicalSpace.MetrizableSpace P.M :=
    Manifold.metrizableSpace I P.M
  letI : T3Space P.M := inferInstance
  have hComplete :
      letI : EMetricSpace P.M := EMetricSpace.ofRiemannianMetric I P.M
      CompleteSpace P.M := by
    simpa [MetricComplete] using hcomplete
  letI : EMetricSpace P.M := EMetricSpace.ofRiemannianMetric I P.M
  letI : IsRiemannianManifold I P.M := inferInstance
  letI : CompleteSpace P.M := hComplete
  exact
    DifferentialGeometry.Geometry.Riemannian.BonnetMyers.bonnet_myers_compactSpace_of_ricci_bound
      (E := E) g hdim hK hRic (fun x v =>
        DifferentialGeometry.Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) g x v)

end PointedRiemannianManifold

end HCGCompactness
end DifferentialGeometry
