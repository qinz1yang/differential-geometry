import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.NormalBranchHessian



set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle Manifold Set TopologicalSpace
open scoped ContDiff Manifold NNReal Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

def HasChartCmSol
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) Y)
    (hconn : letI : TopologicalSpace Y.M := Y.topology; ConnectedSpace Y.M)
    (p : Y.M) (c : NormalChartAt (I := I) Y p)
    {q : NNReal} {delta : Real}
    {ι : Type} [Fintype ι]
    (mu : ι → Real) (pts : ι → Y.M)
    (join : Y.M → Y.M → Real → Y.M) (x : Y.M) (rad : Real)
    (hcm :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : IsManifold I 1 Y.M := IsManifold.of_le
        (I := I) (M := Y.M) (n := ∞) (by decide)
      letI : SigmaCompactSpace Y.M := Y.sigmaCompact
      letI : T2Space Y.M := Y.t2
      letI : ConnectedSpace Y.M := hconn
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      letI : TopologicalSpace.MetrizableSpace Y.M :=
        Manifold.metrizableSpace I Y.M
      letI : T3Space Y.M := inferInstance
      letI : RiemannianBundle
          (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle (I := I)
      letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
        Y.riemInner (I := I)
      letI : IsContinuousRiemannianBundle E
          (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
      letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
      letI : CompleteSpace Y.M :=
        MetricComplete.complete (I := I) Y hcomplete
      letI : MetricSpace Y.M :=
        HopfRinow.riemMetricSpace (I := I) (M := Y.M)
      CenterInput (I := I) Y.metric mu pts join x rad) : Prop :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : IsManifold I 1 Y.M := IsManifold.of_le
    (I := I) (M := Y.M) (n := ∞) (by decide)
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : ConnectedSpace Y.M := hconn
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : TopologicalSpace.MetrizableSpace Y.M :=
    Manifold.metrizableSpace I Y.M
  letI : T3Space Y.M := inferInstance
  letI : RiemannianBundle
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle (I := I)
  letI : (y : Y.M) → InnerProductSpace Real (TangentSpace I y) :=
    Y.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun y : Y.M ↦ TangentSpace I y) := Y.riemBundle_cont (I := I)
  letI : EMetricSpace Y.M := Y.emetricSpace (I := I)
  letI : CompleteSpace Y.M :=
    MetricComplete.complete (I := I) Y hcomplete
  letI : MetricSpace Y.M :=
    HopfRinow.riemMetricSpace (I := I) (M := Y.M)
  ∃ (hq : 0 < q)
      (e : OpenPartialHomeomorph (E × E) (E × E))
      (he : IsNormalDiag (I := I) Y hcomplete hconn p q delta e (c := c)),
    NormalDiagFence (I := I) Y p q e (c := c) ∧
      let B := IsNormalDiag.toBranch (I := I) Y hcomplete hconn p hq he
      let y := centerOfMass (I := I) Y.metric mu pts join x rad hcm
      let z := c.inv y
      let xi : ι → E := fun i ↦ c.inv (pts i)
      y ∈ c.restrictBall.target ∧
        HasCmSolC (I := I) Y.metric (normal_enorm (I := I) Y)
          p c B z (mu, xi)

end HCGCompactness
end DifferentialGeometry
