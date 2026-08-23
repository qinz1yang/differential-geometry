import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.BoundedGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.Defs

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold Topology

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

def HasSpacetimeCurvBound
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (C : Real) : Prop :=
  forall t : Real, t ∈ D.carrier ->
    forall x : F.M, F.rmNormSq (I := I) t x <= C

def HasSpacetimeCurvDerivBound
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (k : Nat) (C : Real) : Prop :=
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : IsManifold I (∞ + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  forall t : Real, t ∈ D.carrier ->
    forall x : F.M, curvDerivNorm (I := I) k (F.S.family.metric t) x <= C

structure SpacetimeCurvBound
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  C : Real
  nonneg : 0 <= C
  bound : forall i : Nat, HasSpacetimeCurvBound (I := I) (X.term i) C

structure FlowDerivBounds
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  C : Nat -> Real
  nonneg : forall k : Nat, 0 <= C k
  bound : forall i k : Nat, HasSpacetimeCurvDerivBound (I := I) (X.term i) k (C k)

namespace FlowDerivBounds

def at_time
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    (h : FlowDerivBounds (I := I) X) {t : Real} (ht : t ∈ X.D.carrier) :
    SeqBoundedGeometry (I := I) (X.atTime (I := I) t) where
  C := h.C
  nonneg := h.nonneg
  bound := by
    intro i k
    simpa [HasSpacetimeCurvDerivBound, HasCurvDerivBound,
      PointedFlowSeq.atTime, PointedFlowData.atTime] using h.bound i k t ht

end FlowDerivBounds

structure FlowDerivativeInput
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) where
  spacetime : FlowDerivBounds (I := I) X
  at_zero_geom : SeqBoundedGeometry (I := I) (X.atZero (I := I))


end HCGCompactness
end DifferentialGeometry
