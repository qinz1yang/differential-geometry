import DifferentialGeometry.Topology.ThreeManifold.Surgery.TubeSystem.Empty
import DifferentialGeometry.Topology.ThreeManifold.Surgery.TubeSystem.SphereModel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalTransitionBridge

noncomputable section

open Metric Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] threeBallChartedSpace threeBall_isManifold

structure CutCapTransitionData (P Q D N : OrientedThreeStage.{u}) where
  trace : CutCapTopology P.Carrier Q.Carrier D.Carrier N.Carrier
  source_nonempty : Nonempty P.Carrier
  tube_smooth :
    letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
    ∀ a : trace.tubes.Index,
      IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (trace.tubes.tube a)
  [coreCharts : ChartedSpace (EuclideanHalfSpace 3) trace.tubes.core]
  [coreSmooth : IsManifold (𝓡∂ 3) ∞ trace.tubes.core]
  core_induced : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
    (Subtype.val : trace.tubes.core → P.Carrier)
  core_boundary : (𝓡∂ 3).boundary trace.tubes.core =
    ⋃ b : trace.tubes.Boundary, Set.range (trace.tubes.coreBoundarySphere b)
  core_inclusion_smooth : IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ trace.capping.coreInclusion
  cap_smooth : ∀ b, IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (trace.capping.cap b)
  attaching : ∀ _b : trace.tubes.Boundary, Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2
  attaching_eq : ∀ b, (attaching b : Sphere 2 → Sphere 2) = trace.capping.attaching b
  core_positive : ∀ x : trace.tubes.core, (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
        (Subtype.val : trace.tubes.core → P.Carrier) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel trace.capping.coreInclusion x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : trace.tubes.core → P.Carrier) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective
            (mfderiv (𝓡∂ 3) ThreeModel trace.capping.coreInclusion x).toLinearMap hj))
        (P.orientation.orientation x.1) =
          N.orientation.orientation (trace.capping.coreInclusion x)
  cap_positive : ∀ b, ∀ x : ThreeBall, (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
        (Subtype.val : ThreeBall → ThreeSpace) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel (trace.capping.cap b) x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : ThreeBall → ThreeSpace) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective
            (mfderiv (𝓡∂ 3) ThreeModel (trace.capping.cap b) x).toLinearMap hj))
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
          (if b.2 then (1 : ℝˣ) else -1) • N.orientation.orientation (trace.capping.cap b x)
  presentation : N.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ (Q.Carrier ⊕ D.Carrier)
  presentation_eq : (presentation : N.Carrier → Q.Carrier ⊕ D.Carrier) = trace.presentation
  presentation_positive : ∀ x : N.Carrier,
    ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel presentation x),
      Orientation.map (Fin 3)
        (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel presentation x).toLinearMap hf)
        (N.orientation.orientation x) =
          match presentation x with
          | Sum.inl q => Q.orientation.orientation q
          | Sum.inr d => D.orientation.orientation d

def CutCapTransitionData.toSmoothCutCapTransition {P Q D N : OrientedThreeStage.{u}}
    (S : CutCapTransitionData P Q D N) : SmoothCutCapTransition P Q D N where
  trace := S.trace
  source_nonempty := S.source_nonempty
  tube_smooth := S.tube_smooth
  coreCharts := S.coreCharts
  coreSmooth := S.coreSmooth
  core_induced := S.core_induced
  core_boundary := S.core_boundary
  core_inclusion_smooth := S.core_inclusion_smooth
  ballCharts := threeBallChartedSpace
  ballSmooth := threeBall_isManifold
  ball_induced := isSmoothEmbedding_threeBall_inclusion
  ball_boundary := threeBall_boundary_eq_sphere
  cap_smooth := S.cap_smooth
  attaching := S.attaching
  attaching_eq := S.attaching_eq
  core_positive := S.core_positive
  cap_positive := S.cap_positive
  presentation := S.presentation
  presentation_eq := S.presentation_eq
  presentation_positive := S.presentation_positive

theorem nonempty_smoothCutCapTransition_of_data {P Q D N : OrientedThreeStage.{u}}
    (S : CutCapTransitionData P Q D N) : Nonempty (SmoothCutCapTransition P Q D N) :=
  ⟨S.toSmoothCutCapTransition⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
