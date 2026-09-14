import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HextBoundaryFrameReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckCutCapInstance

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open private standardNeckCapSum_false_apply
  from DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StandardNeckCutCapInstance

attribute [local instance] threeBallChartedSpace threeBall_isManifold

theorem SmoothCutCapTransition.attachingFrameReversing_of_attaching_eq_refl
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : ∀ b, X.attaching b = Diffeomorph.refl (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞) :
    X.attachingFrameReversing := by
  intro b z v w
  have hz : X.attaching b z = z := by rw [h b, Diffeomorph.coe_refl]; rfl
  have hA : mfderiv (𝓡 2) (𝓡 2) (⇑(X.attaching b)) z =
      ContinuousLinearMap.id ℝ (TangentSpace (𝓡 2) z) := by
    rw [h b, Diffeomorph.coe_refl]
    exact mfderiv_id
  rw [hA, hz]
  simp only [ContinuousLinearMap.id_apply]

theorem SmoothCutCapTransition.boundaryFrameReversing_of_attaching_eq_refl
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : ∀ b, X.attaching b = Diffeomorph.refl (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (hout : (SphericalTubeSystem.ofSmoothCutCapTransition X)
      |>.outwardNormalFirstIsStandardSphereOrientation) :
    X.boundaryFrameReversing :=
  (X.boundaryFrameReversing_iff_attachingFrameReversing hout).mpr
    (X.attachingFrameReversing_of_attaching_eq_refl h)

theorem SmoothCutCapTransition.outwardNormalFirst_iff_boundaryFrameReversing_of_attaching_eq_refl
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : ∀ b, X.attaching b = Diffeomorph.refl (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞) :
    ((SphericalTubeSystem.ofSmoothCutCapTransition X)
        |>.outwardNormalFirstIsStandardSphereOrientation) ↔ X.boundaryFrameReversing := by
  refine ⟨fun hout => X.boundaryFrameReversing_of_attaching_eq_refl h hout, fun hb => ?_⟩
  intro b z v w
  have hb' := hb b z v w
  simp only [Function.comp_apply] at hb'
  rw [h b] at hb'
  simp only [Diffeomorph.coe_refl, id_eq, Function.comp_id] at hb'
  exact hb'

theorem SmoothCutCapTransition.nonempty_sphericalCappingCompletion_of_attaching_eq_refl
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : ∀ b, X.attaching b = Diffeomorph.refl (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (hout : (SphericalTubeSystem.ofSmoothCutCapTransition X)
      |>.outwardNormalFirstIsStandardSphereOrientation) :
    Nonempty (SphericalCappingCompletion X) :=
  ⟨X.toSphericalCappingCompletion (X.boundaryFrameReversing_of_attaching_eq_refl h hout)⟩

theorem SmoothCutCapTransition.nonempty_smoothCutCapCompletion_of_attaching_eq_refl
    {P Q D N : OrientedThreeStage.{u}} (X : SmoothCutCapTransition P Q D N)
    (h : ∀ b, X.attaching b = Diffeomorph.refl (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (hout : (SphericalTubeSystem.ofSmoothCutCapTransition X)
      |>.outwardNormalFirstIsStandardSphereOrientation) :
    Nonempty (SmoothCutCapCompletion X) :=
  ⟨X.toSmoothCutCapCompletion (X.boundaryFrameReversing_of_attaching_eq_refl h hout)⟩

theorem MetricCutCapEvent.hasCutCapCompletion_of_attaching_eq_refl
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (h : ∀ b, E.transition.attaching b = Diffeomorph.refl (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (hout : (SphericalTubeSystem.ofSmoothCutCapTransition E.transition)
      |>.outwardNormalFirstIsStandardSphereOrientation) :
    E.hasCutCapCompletion :=
  E.transition.nonempty_smoothCutCapCompletion_of_attaching_eq_refl h hout

theorem RetainedCoreEvent.toMetricCutCapEvent_hasCutCapCompletion_of_attaching_eq_refl
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : RetainedCoreEvent P Q a s)
    (h : ∀ b, E.transition.attaching b = Diffeomorph.refl (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (hout : (SphericalTubeSystem.ofSmoothCutCapTransition E.transition)
      |>.outwardNormalFirstIsStandardSphereOrientation) :
    E.toMetricCutCapEvent.hasCutCapCompletion :=
  E.transition.nonempty_smoothCutCapCompletion_of_attaching_eq_refl h hout

theorem RetainedCoreHistory.boundaryFrameReversing_of_attaching_eq_refl
    {P : OrientedThreeStage.{u}} (H : RetainedCoreHistory P)
    (h : ∀ (i : Fin H.eventCount) (b : (H.coreEvent i).transition.trace.tubes.Boundary),
      (H.coreEvent i).transition.attaching b = Diffeomorph.refl (𝓡 2)
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞)
    (hout : ∀ i : Fin H.eventCount,
      (SphericalTubeSystem.ofSmoothCutCapTransition (H.coreEvent i).transition)
        |>.outwardNormalFirstIsStandardSphereOrientation) :
    ∀ i : Fin H.eventCount, (H.coreEvent i).transition.boundaryFrameReversing :=
  fun i => (H.coreEvent i).transition.boundaryFrameReversing_of_attaching_eq_refl (h i) (hout i)

theorem nonempty_smoothCutCapCompletion_standardNeckCutCapTransition
    (h : StandardNeckCutCapInputs)
    (hout : (SphericalTubeSystem.ofSmoothCutCapTransition
      (standardNeckCutCapTransition h).toSmoothCutCapTransition)
        |>.outwardNormalFirstIsStandardSphereOrientation) :
    Nonempty (SmoothCutCapCompletion
      (standardNeckCutCapTransition h).toSmoothCutCapTransition) :=
  SmoothCutCapTransition.nonempty_smoothCutCapCompletion_of_attaching_eq_refl _
    (fun _ => rfl) hout

theorem standardNeckCutCapTransition_nondegenerate (h : StandardNeckCutCapInputs) :
    Nonempty (standardNeckCutCapTransition h).trace.tubes.Index ∧
      (standardNeckCutCapTransition h).trace.tubes.core ≠ Set.univ ∧
      (standardNeckTubeSystem.removedBand PUnit.unit).Nonempty ∧
      (standardNeckCutCapTransition h).trace.tubes.boundarySphere (PUnit.unit, false) ≠
        (standardNeckCutCapTransition h).trace.tubes.boundarySphere (PUnit.unit, true) :=
  standardNeckCutCap_nondegenerate

theorem standardNeckCapping_cap_false_apply (y : ThreeBall) :
    standardNeckCapping.cap (PUnit.unit, false) y = Sum.inl (standardNeckCapFun false y) := by
  rw [← standardNeckCapSum_false_apply y]
  rfl

theorem not_orientation_map_eq_of_sphereOutwardDeterminant_not_pos
    (L : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hframe : ¬ 0 < sphereOutwardDeterminant 3 (standardNeckCapFun false 0)
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map L)) :
    ¬ (Orientation.map (Fin 3) L
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation =
      (sphereThreeStage.sum sphereThreeStage).orientation.orientation
        (standardNeckCapping.cap (PUnit.unit, false) 0)) := by
  intro heq
  have htarget : (sphereThreeStage.sum sphereThreeStage).orientation.orientation
      (standardNeckCapping.cap (PUnit.unit, false) 0) =
      (sphereOrientation 3 (by decide)).orientation (standardNeckCapFun false 0) := by
    rw [standardNeckCapping_cap_false_apply 0]
    exact (OrientedThreeStage.sum_orientation_inl sphereThreeStage sphereThreeStage
      (standardNeckCapFun false 0)).trans rfl
  have hb : ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map L).orientation =
      (sphereOrientation 3 (by decide)).orientation (standardNeckCapFun false 0) := by
    rw [Module.Basis.orientation_map, ← htarget]
    exact heq
  exact hframe ((sphereOrientation_characterization 3 (by decide) _ _).mp hb)

theorem threeBall_isInteriorPoint_zero : (𝓡∂ 3).IsInteriorPoint (0 : ThreeBall) := by
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
  intro h
  have hb : (0 : ThreeBall) ∈ (𝓡∂ 3).boundary ThreeBall := h
  rw [threeBall_boundary_eq_sphere] at hb
  obtain ⟨y, hy⟩ := hb
  have hy1 : (y : ThreeSpace) = 0 := by
    have h2 := congrArg (fun z : ThreeBall => (z : ThreeSpace)) hy
    simp only [sphereToThreeBall, ContinuousMap.coe_mk] at h2
    simpa using h2
  have hy2 : ‖(y : ThreeSpace)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using y.2
  rw [hy1, norm_zero] at hy2
  exact absurd hy2.symm (by norm_num)

theorem not_standardNeckCutCapInputs_of_capFrameDeterminant_not_pos
    (hframe : ∀ (hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : ThreeBall → ThreeSpace) 0))
        (hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
          (standardNeckCapping.cap (PUnit.unit, false)) 0)),
      ¬ 0 < sphereOutwardDeterminant 3 (standardNeckCapFun false 0)
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
          ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
              (Subtype.val : ThreeBall → ThreeSpace) 0).toLinearMap hi).symm.trans
            (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
              (standardNeckCapping.cap (PUnit.unit, false)) 0).toLinearMap hj))))
    (h : StandardNeckCutCapInputs) : False :=
  let ⟨hi, hj, heq⟩ := h.cap_positive (PUnit.unit, false) 0 threeBall_isInteriorPoint_zero
  not_orientation_map_eq_of_sphereOutwardDeterminant_not_pos _
    (hframe hi hj) heq

theorem not_nonempty_standardNeckCutCapInputs_of_capFrameDeterminant_not_pos
    (hframe : ∀ (hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : ThreeBall → ThreeSpace) 0))
        (hj : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
          (standardNeckCapping.cap (PUnit.unit, false)) 0)),
      ¬ 0 < sphereOutwardDeterminant 3 (standardNeckCapFun false 0)
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map
          ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
              (Subtype.val : ThreeBall → ThreeSpace) 0).toLinearMap hi).symm.trans
            (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
              (standardNeckCapping.cap (PUnit.unit, false)) 0).toLinearMap hj)))) :
    ¬ Nonempty StandardNeckCutCapInputs :=
  fun ⟨h⟩ => not_standardNeckCutCapInputs_of_capFrameDeterminant_not_pos hframe h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
