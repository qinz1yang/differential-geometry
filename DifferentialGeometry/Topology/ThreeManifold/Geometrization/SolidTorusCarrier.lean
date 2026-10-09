import DifferentialGeometry.Topology.Manifold.ClosedSolidTorusOrientation
import DifferentialGeometry.Topology.Manifold.ClosedSolidTorusCollar
import DifferentialGeometry.Topology.Manifold.ClosedSolidTorusIntrinsicBoundary
import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpaceProdLeft
import DifferentialGeometry.Topology.Manifold.ModelTransportDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff

namespace GC.Endpoint

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

private abbrev Solid := ClosedCell 2 × Circle
private abbrev ProdI := (𝓡∂ 2).prod (𝓡 1)

@[instance_reducible]
def closedSolidTorusHalfSpaceChartedSpace :
    ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 2 × Circle) :=
  DifferentialGeometry.Manifold.euclideanHalfSpaceProdLeftChartedSpace 1 1 Solid

theorem closedSolidTorusHalfSpace_isManifold :
    letI := closedSolidTorusHalfSpaceChartedSpace
    IsManifold (𝓡∂ 3) ∞ (ClosedCell 2 × Circle) :=
  DifferentialGeometry.Manifold.euclideanHalfSpaceProdLeft_isManifold 1 1 Solid

private def modelDiffeomorph :
    letI := closedSolidTorusHalfSpaceChartedSpace
    Solid ≃ₘ⟮ProdI, 𝓡∂ 3⟯ Solid :=
  DifferentialGeometry.Manifold.diffeomorphTransHomeomorph ProdI (𝓡∂ 3)
    (DifferentialGeometry.Manifold.euclideanHalfSpaceProdLeftHomeomorph 1 1)
    (DifferentialGeometry.Manifold.euclideanHalfSpaceProdLeftCoordinates 1 1)
    (DifferentialGeometry.Manifold.euclideanHalfSpaceProdLeftHomeomorph_model 1 1) ∞

private def productSmoothOrientation : SmoothOrientation ProdI Solid :=
  smoothOrientationOfManifoldOrientation ProdI
    (OrientationAssembly.reindexManifoldOrientation ProdI
      (finCongr (by simp : 3 = Module.finrank ℝ
        (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))))
      closedSolidTorusProductOrientation)

private def halfSpaceSmoothOrientation :
    letI := closedSolidTorusHalfSpaceChartedSpace
    letI := closedSolidTorusHalfSpace_isManifold
    SmoothOrientation (𝓡∂ 3) Solid := by
  letI := closedSolidTorusHalfSpaceChartedSpace
  letI := closedSolidTorusHalfSpace_isManifold
  exact pullbackSmoothOrientation (𝓡∂ 3) ProdI modelDiffeomorph.symm
    modelDiffeomorph.symm.contMDiff
    (fun x => (modelDiffeomorph.symm.mfderivToContinuousLinearEquiv (by simp) x).bijective)
    productSmoothOrientation

private def halfSpaceOrientation :
    letI := closedSolidTorusHalfSpaceChartedSpace
    letI := closedSolidTorusHalfSpace_isManifold
    ManifoldOrientation (𝓡∂ 3) Solid 3 := by
  letI := closedSolidTorusHalfSpaceChartedSpace
  letI := closedSolidTorusHalfSpace_isManifold
  exact OrientationAssembly.reindexManifoldOrientation (𝓡∂ 3)
    (finCongr (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3))
    (Classical.choose (exists_manifoldOrientation_eq_of_smoothOrientation (𝓡∂ 3)
      halfSpaceSmoothOrientation))

def closedSolidTorusCarrier : CompactCarrier where
  kind := .withBoundary
  Carrier := ClosedCell 2 × Circle
  charts := closedSolidTorusHalfSpaceChartedSpace
  smooth := closedSolidTorusHalfSpace_isManifold
  orientation := halfSpaceOrientation

def closedSolidTorusCarrierDiffeomorph :
    (ClosedCell 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), closedSolidTorusCarrier.model⟯
      closedSolidTorusCarrier.Carrier := modelDiffeomorph

theorem closedSolidTorusCarrierDiffeomorph_apply (x : ClosedCell 2 × Circle) :
    closedSolidTorusCarrierDiffeomorph x = x := rfl

theorem closedSolidTorusCarrierDiffeomorph_symm_apply
    (x : closedSolidTorusCarrier.Carrier) :
    closedSolidTorusCarrierDiffeomorph.symm x = x := rfl

theorem closedSolidTorusCarrierDiffeomorph_symm_preservesOrientation :
    closedSolidTorusCarrierDiffeomorph.symm.preservesOrientation
      closedSolidTorusCarrier.orientation closedSolidTorusProductOrientation := by
  let _ := closedSolidTorusHalfSpaceChartedSpace
  let _ := closedSolidTorusHalfSpace_isManifold
  apply Diffeomorph.preservesOrientation_of_pullbackSmoothOrientation
    modelDiffeomorph.symm modelDiffeomorph.symm.contMDiff
    (fun x => (modelDiffeomorph.symm.mfderivToContinuousLinearEquiv (by simp) x).bijective)
    productSmoothOrientation
  · intro y
    rfl
  · intro x
    change Orientation.reindex ℝ _ _
      ((Classical.choose (exists_manifoldOrientation_eq_of_smoothOrientation (𝓡∂ 3)
        halfSpaceSmoothOrientation)).orientation x) = _
    rw [Classical.choose_spec (exists_manifoldOrientation_eq_of_smoothOrientation (𝓡∂ 3)
      halfSpaceSmoothOrientation)]
    rfl

theorem closedSolidTorusCarrierDiffeomorph_preservesOrientation :
    closedSolidTorusCarrierDiffeomorph.preservesOrientation
      closedSolidTorusProductOrientation closedSolidTorusCarrier.orientation :=
  Diffeomorph.preservesOrientation_symm (f := closedSolidTorusCarrierDiffeomorph.symm)
    (oM := closedSolidTorusCarrier.orientation) (oN := closedSolidTorusProductOrientation)
    closedSolidTorusCarrierDiffeomorph_symm_preservesOrientation

theorem closedSolidTorusCarrier_boundary :
    closedSolidTorusCarrier.model.boundary closedSolidTorusCarrier.Carrier =
      {x | ‖x.1.val‖ = 1} := by
  let _ := closedSolidTorusHalfSpaceChartedSpace
  change (𝓡∂ 3).boundary Solid = _
  exact (DifferentialGeometry.Manifold.euclideanHalfSpaceProdLeft_boundary 1 1 Solid).trans
    closedSolidTorus_boundary

def closedSolidTorusCarrierBoundaryParam :
    Torus ≃ₜ (closedSolidTorusCarrier.model.boundary closedSolidTorusCarrier.Carrier) := by
  let f : Torus → (closedSolidTorusCarrier.model.boundary closedSolidTorusCarrier.Carrier) :=
    fun z => ⟨closedSolidTorusBoundary z, by
      rw [closedSolidTorusCarrier_boundary]
      exact closedDiskBoundary_norm z.1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro z w h
      exact closedSolidTorusBoundary_isClosedEmbedding.isEmbedding.injective
        (congrArg Subtype.val h)
    · intro x
      have hx : x.val ∈ Set.range closedSolidTorusBoundary := by
        rw [range_closedSolidTorusBoundary]
        exact (Set.ext_iff.mp closedSolidTorusCarrier_boundary x.val).mp x.property
      obtain ⟨z, hz⟩ := hx
      exact ⟨z, Subtype.ext hz⟩
  have hc : Continuous f := closedSolidTorusBoundary_contMDiff.continuous.subtype_mk _
  exact (Equiv.ofBijective f hf).toHomeomorphOfContinuousClosed hc hc.isClosedMap

theorem closedSolidTorusCarrierBoundaryParam_apply (z : Torus) :
    (closedSolidTorusCarrierBoundaryParam z).val = closedSolidTorusBoundary z := rfl

def closedSolidTorusCarrierCollar :
    PartialDiffeomorph halfCollarModel closedSolidTorusCarrier.model
      (Torus × EuclideanHalfSpace 1) closedSolidTorusCarrier.Carrier ∞ :=
  closedSolidTorusRadialCollar.trans closedSolidTorusCarrierDiffeomorph.toPartialDiffeomorph

theorem closedSolidTorusCarrierCollar_apply (p : Torus × EuclideanHalfSpace 1) :
    closedSolidTorusCarrierCollar p = closedSolidTorusRadialCollar p := rfl

theorem closedSolidTorusCarrierCollar_source :
    closedSolidTorusCarrierCollar.source = halfCollarSource := by
  change closedSolidTorusRadialCollar.source ∩
    closedSolidTorusRadialCollar ⁻¹' Set.univ = _
  simpa only [Set.preimage_univ, Set.inter_univ, halfCollarSource] using
    closedSolidTorusRadialCollar_source

theorem closedSolidTorusCarrierCollar_target :
    closedSolidTorusCarrierCollar.target = {x | 1 / 2 < ‖x.1.val‖} := by
  calc
    _ = closedSolidTorusRadialCollar.target := by
      have hcarrier : closedSolidTorusCarrierCollar '' closedSolidTorusCarrierCollar.source =
          closedSolidTorusCarrierCollar.target :=
        closedSolidTorusCarrierCollar.toOpenPartialHomeomorph.image_source_eq_target
      have hradial : closedSolidTorusRadialCollar '' closedSolidTorusRadialCollar.source =
          closedSolidTorusRadialCollar.target :=
        closedSolidTorusRadialCollar.toOpenPartialHomeomorph.image_source_eq_target
      rw [← hcarrier, ← hradial,
        closedSolidTorusCarrierCollar_source, closedSolidTorusRadialCollar_source]
      rfl
    _ = _ := closedSolidTorusRadialCollar_target

theorem closedSolidTorusCarrierCollar_zero (z : Torus) :
    closedSolidTorusCarrierCollar (z, halfZero) = closedSolidTorusBoundary z :=
  closedSolidTorusRadialCollar_zero z halfZero rfl

end GC.Endpoint
