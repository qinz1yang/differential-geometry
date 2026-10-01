import DifferentialGeometry.Topology.ThreeManifold.Surgery.SphereModel.Defs
import DifferentialGeometry.Topology.ThreeManifold.Surgery.SphereModel.TubeEmbedding
import DifferentialGeometry.Topology.ThreeManifold.Surgery.SphereModel.CapEmbedding
import DifferentialGeometry.Topology.ThreeManifold.Surgery.CutCap.PresentationOrientation
import DifferentialGeometry.Topology.ThreeManifold.Surgery.Capping.BoundaryOrientation
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportSource

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure StandardNeckCutCapInputs where
  [coreChartsModel : ChartedSpace
    DifferentialGeometry.Manifold.EuclideanHalfSpaceProdModel standardNeckTubeSystem.core]
  [coreSmoothModel : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ standardNeckTubeSystem.core]
  core_induced_model : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞
    (Subtype.val : standardNeckTubeSystem.core → Sphere 3)
  core_boundary_model : ((𝓡 2).prod (𝓡∂ 1)).boundary standardNeckTubeSystem.core =
    ⋃ b : standardNeckTubeSystem.Boundary, Set.range (standardNeckTubeSystem.coreBoundarySphere b)
  core_inclusion_model : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞
    standardNeckCapping.coreInclusion
  core_positive :
    letI : ChartedSpace (EuclideanHalfSpace 3) standardNeckTubeSystem.core :=
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdChartedSpace standardNeckTubeSystem.core
    letI : IsManifold (𝓡∂ 3) ∞ standardNeckTubeSystem.core :=
      DifferentialGeometry.Manifold.euclideanHalfSpaceProd_isManifold standardNeckTubeSystem.core
    ∀ x : standardNeckTubeSystem.core, (𝓡∂ 3).IsInteriorPoint x →
      ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : standardNeckTubeSystem.core → Sphere 3) x),
      ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
          standardNeckCapping.coreInclusion x),
        Orientation.map (Fin 3)
          ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
            (Subtype.val : standardNeckTubeSystem.core → Sphere 3) x).toLinearMap hi).symm.trans
            (LinearEquiv.ofBijective
              (mfderiv (𝓡∂ 3) ThreeModel standardNeckCapping.coreInclusion x).toLinearMap hj))
          (sphereThreeStage.orientation.orientation x.1) =
            (sphereThreeStage.sum sphereThreeStage).orientation.orientation
              (standardNeckCapping.coreInclusion x)
  cap_positive :
    letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := threeBallChartedSpace
    letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := threeBall_isManifold
    ∀ b, ∀ x : ThreeBall, (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
        (Subtype.val : ThreeBall → ThreeSpace) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel (standardNeckCapping.cap b) x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : ThreeBall → ThreeSpace) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective
            (mfderiv (𝓡∂ 3) ThreeModel (standardNeckCapping.cap b) x).toLinearMap hj))
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
          (if b.2 then (1 : ℝˣ) else -1) •
            (sphereThreeStage.sum sphereThreeStage).orientation.orientation
              (standardNeckCapping.cap b x)

def standardNeckCutCapTransition (h : StandardNeckCutCapInputs) :
    SmoothCutCapTransition sphereThreeStage sphereThreeStage sphereThreeStage
      (sphereThreeStage.sum sphereThreeStage) := by
  letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
  letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := threeBallChartedSpace
  letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := threeBall_isManifold
  letI : ChartedSpace DifferentialGeometry.Manifold.EuclideanHalfSpaceProdModel
      standardNeckCutCap.tubes.core := h.coreChartsModel
  letI : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ standardNeckCutCap.tubes.core := h.coreSmoothModel
  let coreCharts3 : ChartedSpace (EuclideanHalfSpace 3) standardNeckCutCap.tubes.core :=
    @DifferentialGeometry.Manifold.euclideanHalfSpaceProdChartedSpace
      standardNeckCutCap.tubes.core _ h.coreChartsModel
  letI : ChartedSpace (EuclideanHalfSpace 3) standardNeckCutCap.tubes.core := coreCharts3
  let coreSmooth3 : IsManifold (𝓡∂ 3) ∞ standardNeckCutCap.tubes.core :=
    @DifferentialGeometry.Manifold.euclideanHalfSpaceProd_isManifold
      standardNeckCutCap.tubes.core _ h.coreChartsModel h.coreSmoothModel
  letI : IsManifold (𝓡∂ 3) ∞ standardNeckCutCap.tubes.core := coreSmooth3
  exact SmoothCutCapTransition.mk
    (trace := standardNeckCutCap)
    (source_nonempty := sphereThreeStage_nonempty)
    (tube_smooth := standardNeckTubeSystem_tube_isSmoothEmbedding)
    (coreCharts := coreCharts3)
    (coreSmooth := coreSmooth3)
    (core_induced :=
      @DifferentialGeometry.Manifold.isSmoothEmbedding_coreSubtype_of_euclideanHalfSpaceProd
        (Sphere 3) _ _ (standardNeckCutCap.tubes.core) h.coreChartsModel
        h.core_induced_model)
    (core_boundary :=
      (@DifferentialGeometry.Manifold.euclideanHalfSpaceProd_boundary
        standardNeckCutCap.tubes.core _ h.coreChartsModel).trans h.core_boundary_model)
    (core_inclusion_smooth :=
      @DifferentialGeometry.Manifold.isSmoothEmbedding_coreInclusion_of_euclideanHalfSpaceProd
        (standardNeckCutCap.tubes.core) (Sphere 3 ⊕ Sphere 3) _ h.coreChartsModel
        _ _
        standardNeckCapping.coreInclusion h.core_inclusion_model)
    (ballCharts := threeBallChartedSpace)
    (ballSmooth := threeBall_isManifold)
    (ball_induced := isSmoothEmbedding_threeBall_inclusion)
    (ball_boundary := threeBall_boundary_eq_sphere)
    (cap_smooth := standardNeckCapping_cap_isSmoothEmbedding)
    (attaching := fun _ => Diffeomorph.refl (𝓡 2) (Sphere 2) ∞)
    (attaching_eq := fun _ => rfl)
    (core_positive := h.core_positive)
    (cap_positive := h.cap_positive)
    (presentation := Diffeomorph.refl ThreeModel (Sphere 3 ⊕ Sphere 3) ∞)
    (presentation_eq := rfl)
    (presentation_positive := fun x => by
      obtain ⟨hf, hfx⟩ := presentation_positive_refl_sum sphereThreeStage sphereThreeStage x
      refine ⟨hf, ?_⟩
      convert hfx using 2
      all_goals cases x <;> rfl)

theorem nonempty_smoothCutCapTransition_of_standardNeckInputs
    (h : StandardNeckCutCapInputs) :
    Nonempty (SmoothCutCapTransition sphereThreeStage sphereThreeStage sphereThreeStage
      (sphereThreeStage.sum sphereThreeStage)) :=
  ⟨standardNeckCutCapTransition h⟩

theorem nonempty_smoothCutCapCompletion_standardNeckCutCapTransition
    (h : StandardNeckCutCapInputs)
    (hout : (SphericalTubeSystem.ofSmoothCutCapTransition
      (standardNeckCutCapTransition h))
        |>.outwardNormalFirstIsStandardSphereOrientation) :
    Nonempty (SmoothCutCapCompletion
      (standardNeckCutCapTransition h)) :=
  SmoothCutCapTransition.nonempty_smoothCutCapCompletion_of_attaching_eq_refl _
    (fun _ => rfl) hout

theorem standardNeckCutCapTransition_nondegenerate (h : StandardNeckCutCapInputs) :
    Nonempty (standardNeckCutCapTransition h).trace.tubes.Index ∧
      (standardNeckCutCapTransition h).trace.tubes.core ≠ Set.univ ∧
      (standardNeckTubeSystem.removedBand PUnit.unit).Nonempty ∧
      (standardNeckCutCapTransition h).trace.tubes.boundarySphere (PUnit.unit, false) ≠
        (standardNeckCutCapTransition h).trace.tubes.boundarySphere (PUnit.unit, true) :=
  standardNeckCutCap_nondegenerate

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
