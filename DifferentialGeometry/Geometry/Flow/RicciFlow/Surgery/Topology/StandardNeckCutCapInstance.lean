import DifferentialGeometry.Topology.ThreeManifold.Surgery.SphereModel.Capping
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapPresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckRegularity
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportSource

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

structure StandardNeckCutCapInputs where
  cylinderEmbedding : ∃ g : Sphere 2 × ℝ → Sphere 3,
    IsSmoothEmbedding ((𝓡 2).prod 𝓘(ℝ)) ThreeModel ∞ g ∧
      ∀ z : TubeDomain, g (z.1, (z.2 : ℝ)) = standardNeckTubeFun z
  [coreChartsModel : ChartedSpace
    DifferentialGeometry.Manifold.EuclideanHalfSpaceProdModel standardNeckTubeSystem.core]
  [coreSmoothModel : IsManifold ((𝓡 2).prod (𝓡∂ 1)) ∞ standardNeckTubeSystem.core]
  core_induced_model : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞
    (Subtype.val : standardNeckTubeSystem.core → Sphere 3)
  core_boundary_model : ((𝓡 2).prod (𝓡∂ 1)).boundary standardNeckTubeSystem.core =
    ⋃ b : standardNeckTubeSystem.Boundary, Set.range (standardNeckTubeSystem.coreBoundarySphere b)
  core_inclusion_model : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞
    standardNeckCapping.coreInclusion
  cap_smooth :
    letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := threeBallChartedSpace
    ∀ b, IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (standardNeckCapping.cap b)
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
  presentation_positive : ∀ x : Sphere 3 ⊕ Sphere 3,
    ∃ hf : Function.Bijective (mfderiv ThreeModel ThreeModel
        (Diffeomorph.refl ThreeModel (Sphere 3 ⊕ Sphere 3) ∞) x),
      Orientation.map (Fin 3)
        (LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel
          (Diffeomorph.refl ThreeModel (Sphere 3 ⊕ Sphere 3) ∞) x).toLinearMap hf)
        ((sphereThreeStage.sum sphereThreeStage).orientation.orientation x) =
          Sum.elim (fun q => sphereThreeStage.orientation.orientation q)
            (fun d => sphereThreeStage.orientation.orientation d) x :=
    fun x => presentation_positive_refl_sum sphereThreeStage sphereThreeStage x

private theorem standardNeckTubeIsSmoothEmbedding_of_inputs (h : StandardNeckCutCapInputs) :
    standardNeckTubeIsSmoothEmbedding := by
  obtain ⟨g, hg, hsub⟩ := h.cylinderEmbedding
  exact standardNeckTubeIsSmoothEmbedding_of_cylinder_isSmoothEmbedding g hg hsub

def standardNeckCutCapTransition (h : StandardNeckCutCapInputs) :
    CutCapTransitionData sphereThreeStage sphereThreeStage sphereThreeStage
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
  exact CutCapTransitionData.mk
    (trace := standardNeckCutCap)
    (source_nonempty := sphereThreeStage_nonempty)
    (tube_smooth := standardNeckTubeSystem_tube_smooth
      (standardNeckTubeIsSmoothEmbedding_of_inputs h))
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
    (cap_smooth := h.cap_smooth)
    (attaching := fun _ => Diffeomorph.refl (𝓡 2) (Sphere 2) ∞)
    (attaching_eq := fun _ => rfl)
    (core_positive := h.core_positive)
    (cap_positive := h.cap_positive)
    (presentation := Diffeomorph.refl ThreeModel (Sphere 3 ⊕ Sphere 3) ∞)
    (presentation_eq := rfl)
    (presentation_positive := fun x => by
      obtain ⟨hf, hfx⟩ := h.presentation_positive x
      refine ⟨hf, ?_⟩
      convert hfx using 2
      all_goals cases x <;> rfl)

theorem nonempty_cutCapTransitionData_of_standardNeckInputs (h : StandardNeckCutCapInputs) :
    Nonempty (CutCapTransitionData sphereThreeStage sphereThreeStage sphereThreeStage
      (sphereThreeStage.sum sphereThreeStage)) :=
  ⟨standardNeckCutCapTransition h⟩

theorem nonempty_smoothCutCapTransition_of_standardNeckInputs
    (h : StandardNeckCutCapInputs) :
    Nonempty (SmoothCutCapTransition sphereThreeStage sphereThreeStage sphereThreeStage
      (sphereThreeStage.sum sphereThreeStage)) := by
  obtain ⟨S⟩ := nonempty_cutCapTransitionData_of_standardNeckInputs h
  exact ⟨S.toSmoothCutCapTransition⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
