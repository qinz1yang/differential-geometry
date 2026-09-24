import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingRestriction
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace SmoothCutCapTransition

theorem coreInclusion_isSmoothEmbedding_of_diffeomorph {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N)
    {old : Type u} [TopologicalSpace old] [ChartedSpace (EuclideanHalfSpace 3) old]
    [IsManifold (𝓡∂ 3) ∞ old] (ι : old → X.trace.tubes.core) :
    letI : ChartedSpace (EuclideanHalfSpace 3) X.trace.tubes.core := X.coreCharts
    letI : IsManifold (𝓡∂ 3) ∞ X.trace.tubes.core := X.coreSmooth
    ∀ (U : TopologicalSpace.Opens X.trace.tubes.core)
      (Ψ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) old U ∞),
      (∀ x : old, (Ψ x : X.trace.tubes.core) = ι x) →
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : old => X.trace.capping.coreInclusion (ι x)) := by
  let coreCharts : ChartedSpace (EuclideanHalfSpace 3) X.trace.tubes.core := X.coreCharts
  let coreSmooth : IsManifold (𝓡∂ 3) ∞ X.trace.tubes.core := X.coreSmooth
  intro U Ψ hΨ
  have hcomp := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp
    (I := 𝓡∂ 3) (J := ThreeModel) (M := U) (N := N.Carrier) (P := old)
    (fun y : U => X.trace.capping.coreInclusion y.1)
    (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_restrictOpen (𝓡∂ 3) ThreeModel
      (fun y : X.trace.tubes.core => X.trace.capping.coreInclusion y) X.core_inclusion_smooth U)
    Ψ
  have hfun : ((fun y : U => X.trace.capping.coreInclusion y.1) ∘ ⇑Ψ) =
      (fun x : old => X.trace.capping.coreInclusion (ι x)) := by
    funext x
    simp only [Function.comp_apply]
    rw [hΨ x]
  rwa [hfun] at hcomp

theorem coreInclusion_isSmoothEmbedding_of_opens {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N)
    (U : TopologicalSpace.Opens X.trace.tubes.core) :
    letI : ChartedSpace (EuclideanHalfSpace 3) X.trace.tubes.core := X.coreCharts
    letI : IsManifold (𝓡∂ 3) ∞ X.trace.tubes.core := X.coreSmooth
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
      (fun x : U => X.trace.capping.coreInclusion x.1) := by
  let coreCharts : ChartedSpace (EuclideanHalfSpace 3) X.trace.tubes.core := X.coreCharts
  let coreSmooth : IsManifold (𝓡∂ 3) ∞ X.trace.tubes.core := X.coreSmooth
  exact X.coreInclusion_isSmoothEmbedding_of_diffeomorph (old := U) (fun x : U => x.1) U
    (Diffeomorph.refl (𝓡∂ 3) U ∞) (fun _ => rfl)

theorem coreInclusion_isSmoothEmbedding_of_diffeomorph_opens {P Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N)
    (old : Set X.trace.tubes.core) [oldCharts : ChartedSpace (EuclideanHalfSpace 3) old]
    [oldSmooth : IsManifold (𝓡∂ 3) ∞ old] :
    letI : ChartedSpace (EuclideanHalfSpace 3) X.trace.tubes.core := X.coreCharts
    letI : IsManifold (𝓡∂ 3) ∞ X.trace.tubes.core := X.coreSmooth
    ∀ (U : TopologicalSpace.Opens X.trace.tubes.core)
      (Ψ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) old U ∞),
      (∀ x : old, ((Ψ x : U) : X.trace.tubes.core) = x.1) →
      IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞
        (fun x : old => X.trace.capping.coreInclusion x.1) :=
  X.coreInclusion_isSmoothEmbedding_of_diffeomorph (old := old) (fun x : old => x.1)

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
