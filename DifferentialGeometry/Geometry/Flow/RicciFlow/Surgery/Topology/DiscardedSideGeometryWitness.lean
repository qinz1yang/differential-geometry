import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.DiscardedSideGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SmoothCutCapTransitionInstance
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SpaceFormCovering
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardComponentwise

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Topology

@[instance_reducible]
noncomputable instance emptyChartedSpacePEmptyULift :
    ChartedSpace ThreeSpace (PEmpty.{u + 1}) :=
  ChartedSpace.empty ThreeSpace (PEmpty.{u + 1})

noncomputable def emptyStageULift : OrientedThreeStage.{u} where
  Carrier := PEmpty.{u + 1}
  orientation :=
    { orientation := fun x => PEmpty.elim x
      locally_constant := fun p _ _ => PEmpty.elim p }

@[simp] theorem emptyStageULift_carrier :
    (emptyStageULift.{u}).Carrier = PEmpty.{u + 1} := rfl

noncomputable def discardedOnlyStage (D : OrientedThreeStage.{u}) : OrientedThreeStage.{u} :=
  emptyStageULift.sum D

@[simp] theorem discardedOnlyStage_carrier (D : OrientedThreeStage.{u}) :
    (discardedOnlyStage D).Carrier = (PEmpty.{u + 1} ⊕ D.Carrier) := rfl

noncomputable def discardedOnlyTubes (D : OrientedThreeStage.{u}) :
    @TubeSystem (discardedOnlyStage D).Carrier (discardedOnlyStage D).topology :=
  @emptyTubeSystem (discardedOnlyStage D).Carrier (discardedOnlyStage D).topology

theorem discardedOnlyTubes_core (D : OrientedThreeStage.{u}) :
    (discardedOnlyTubes D).core = univ :=
  @emptyTubeSystem_core (discardedOnlyStage D).Carrier (discardedOnlyStage D).topology

theorem discardedOnlyTubes_index_isEmpty (D : OrientedThreeStage.{u}) :
    IsEmpty (discardedOnlyTubes D).Index :=
  ⟨fun a => PEmpty.elim a⟩

theorem discardedOnlyTubes_boundary_isEmpty (D : OrientedThreeStage.{u}) :
    IsEmpty (discardedOnlyTubes D).Boundary :=
  ⟨fun b => PEmpty.elim b.1⟩

noncomputable def discardedOnlyTrace (D : OrientedThreeStage.{u}) (hd : Nonempty D.Carrier) :
    @CutCapTopology (discardedOnlyStage D).Carrier emptyStageULift.Carrier D.Carrier
      (discardedOnlyStage D).Carrier (discardedOnlyStage D).topology emptyStageULift.topology
      D.topology (discardedOnlyStage D).topology where
  tubes := discardedOnlyTubes D
  capping := @emptyTubeCapping (discardedOnlyStage D).Carrier (discardedOnlyStage D).topology
  presentation := Homeomorph.refl _
  nontrivial := Or.inr hd

theorem discardedOnlyTrace_core (D : OrientedThreeStage.{u}) (hd : Nonempty D.Carrier) :
    (discardedOnlyTrace D hd).tubes.core = univ :=
  discardedOnlyTubes_core D

theorem discardedOnlyTrace_boundary_isEmpty (D : OrientedThreeStage.{u})
    (hd : Nonempty D.Carrier) :
    IsEmpty (discardedOnlyTrace D hd).tubes.Boundary :=
  ⟨fun b => PEmpty.elim b.1⟩

theorem isOpen_discardedOnlyTrace_core (D : OrientedThreeStage.{u}) (hd : Nonempty D.Carrier) :
    IsOpen (discardedOnlyTrace D hd).tubes.core :=
  (discardedOnlyTrace_core D hd).symm ▸ isOpen_univ

theorem discardedOnlyTrace_coreInclusion_eq (D : OrientedThreeStage.{u}) (hd : Nonempty D.Carrier) :
    (⇑(discardedOnlyTrace D hd).capping.coreInclusion :
      (discardedOnlyTrace D hd).tubes.core → (discardedOnlyStage D).Carrier) = Subtype.val := rfl

noncomputable def smoothCutCapTransitionOfDiscarded (D : OrientedThreeStage.{u})
    (hd : Nonempty D.Carrier) :
    SmoothCutCapTransition (discardedOnlyStage D) emptyStageULift D
      (discardedOnlyStage D) := by
  letI : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩
  letI : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := threeBallChartedSpace
  letI : IsManifold (𝓡∂ 3) ∞ ThreeBall := threeBall_isManifold
  letI : ChartedSpace (EuclideanHalfSpace 3) (discardedOnlyTrace D hd).tubes.core :=
    subsetChartedSpace (discardedOnlyTrace D hd).tubes.core (isOpen_discardedOnlyTrace_core D hd)
  letI : IsManifold (𝓡∂ 3) ∞ (discardedOnlyTrace D hd).tubes.core :=
    subsetIsManifold (discardedOnlyTrace D hd).tubes.core (isOpen_discardedOnlyTrace_core D hd)
  refine
    { trace := discardedOnlyTrace D hd
      source_nonempty := ⟨Sum.inr hd.some⟩
      tube_smooth := fun a => PEmpty.elim a
      coreCharts := subsetChartedSpace (discardedOnlyTrace D hd).tubes.core
        (isOpen_discardedOnlyTrace_core D hd)
      coreSmooth := subsetIsManifold (discardedOnlyTrace D hd).tubes.core
        (isOpen_discardedOnlyTrace_core D hd)
      core_induced := subset_inclusion_isSmoothEmbedding (discardedOnlyTrace D hd).tubes.core
        (isOpen_discardedOnlyTrace_core D hd)
      core_boundary := ?_
      core_inclusion_smooth := subset_inclusion_isSmoothEmbedding
        (discardedOnlyTrace D hd).tubes.core (isOpen_discardedOnlyTrace_core D hd)
      ballCharts := threeBallChartedSpace
      ballSmooth := threeBall_isManifold
      ball_induced := isSmoothEmbedding_threeBall_inclusion
      ball_boundary := threeBall_boundary_eq_sphere
      cap_smooth := fun b => ((discardedOnlyTrace_boundary_isEmpty D hd).false b).elim
      attaching := fun b => ((discardedOnlyTrace_boundary_isEmpty D hd).false b).elim
      attaching_eq := fun b => ((discardedOnlyTrace_boundary_isEmpty D hd).false b).elim
      core_positive := ?_
      cap_positive := fun b => ((discardedOnlyTrace_boundary_isEmpty D hd).false b).elim
      presentation := Diffeomorph.refl ThreeModel (discardedOnlyStage D).Carrier ∞
      presentation_eq := rfl
      presentation_positive := ?_ }
  · rw [subset_boundary_eq_empty (discardedOnlyTrace D hd).tubes.core
      (isOpen_discardedOnlyTrace_core D hd)]
    exact (Set.iUnion_eq_empty.mpr fun b =>
      ((discardedOnlyTrace_boundary_isEmpty D hd).false b).elim).symm
  · intro x hx
    have hi : Function.Bijective (mfderiv (𝓡∂ 3) ThreeModel
        (Subtype.val : (discardedOnlyTrace D hd).tubes.core →
          (discardedOnlyStage D).Carrier) x) :=
      bijective_mfderiv_subtype_val (discardedOnlyTrace D hd).tubes.core
        (isOpen_discardedOnlyTrace_core D hd) x hx
    rw [discardedOnlyTrace_coreInclusion_eq D hd]
    refine ⟨hi, hi, ?_⟩
    have hcomp : (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : (discardedOnlyTrace D hd).tubes.core →
            (discardedOnlyStage D).Carrier) x).toLinearMap hi).symm.trans
        (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) ThreeModel
          (Subtype.val : (discardedOnlyTrace D hd).tubes.core →
            (discardedOnlyStage D).Carrier) x).toLinearMap hi) =
        LinearEquiv.refl ℝ ThreeSpace := by
      apply LinearEquiv.ext
      intro v
      simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      rfl
    rw [hcomp]
    erw [Orientation.map_refl]
    rfl
  · intro x
    have hbij : Function.Bijective (mfderiv ThreeModel ThreeModel
        (Diffeomorph.refl ThreeModel (discardedOnlyStage D).Carrier ∞) x) := by
      rw [Diffeomorph.coe_refl, mfderiv_id]
      exact ⟨fun _ _ hab => hab, fun y => ⟨y, rfl⟩⟩
    refine ⟨hbij, ?_⟩
    have hlin : LinearEquiv.ofBijective (mfderiv ThreeModel ThreeModel
        (Diffeomorph.refl ThreeModel (discardedOnlyStage D).Carrier ∞) x).toLinearMap hbij =
        LinearEquiv.refl ℝ (TangentSpace ThreeModel x) := by
      apply LinearEquiv.ext
      intro v
      rw [LinearEquiv.ofBijective_apply, Diffeomorph.coe_refl, mfderiv_id]
      rfl
    erw [hlin]
    erw [Orientation.map_refl]
    cases x <;> rfl

theorem nonempty_smoothCutCapTransition_of_discarded (D : OrientedThreeStage.{u})
    (hd : Nonempty D.Carrier) :
    Nonempty (SmoothCutCapTransition (discardedOnlyStage D) emptyStageULift D
      (discardedOnlyStage D)) :=
  ⟨smoothCutCapTransitionOfDiscarded D hd⟩

theorem nonempty_smoothCutCapTransition_of_discarded_sphereStage :
    Nonempty (SmoothCutCapTransition (discardedOnlyStage sphereStage) emptyStageULift sphereStage
      (discardedOnlyStage sphereStage)) :=
  nonempty_smoothCutCapTransition_of_discarded sphereStage
    ⟨(⟨EuclideanSpace.single 0 1, by simp⟩ : Sphere 3)⟩

theorem discardedComponentsRoundOrSphereProduct_of_isEmpty
    (D : ClosedOrientedManifold.{u} 3) [IsEmpty D.Carrier] :
    DiscardedComponentsRoundOrSphereProduct D := by
  have hEmpty : IsEmpty (ConnectedComponents D.Carrier) :=
    ConnectedComponents.isEmpty_iff_isEmpty.mpr inferInstance
  exact fun C => (hEmpty.false C).elim

noncomputable def sphereStageConnected : ConnectedClosedOrientedManifold.{0} 3 where
  toClosedOrientedManifold := sphereStage.toClosedOrientedManifold
  connected := isConnected_iff_connectedSpace.mp (by
    simpa using (isConnected_sphere (E := EuclideanSpace ℝ (Fin 4))
      (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 (r := 1) (by norm_num) :
        IsConnected (Sphere 3)))

theorem discardedComponentsRoundOrSphereProduct_sphereStage :
    DiscardedComponentsRoundOrSphereProduct sphereStage.toClosedOrientedManifold := by
  intro C
  exact Or.inl (isPositiveSpaceFormModel_of_diffeomorph_sphereThree _
    (sphereStageConnected.componentOrientedDiffeomorph C).1)

theorem nonempty_connectedComponents_sphereStage :
    Nonempty (ConnectedComponents sphereStage.toClosedOrientedManifold.Carrier) :=
  ⟨ConnectedComponents.mk (⟨EuclideanSpace.single 0 1, by simp⟩ : Sphere 3)⟩

theorem componentwiseStandardFactor_of_forall_discardedComponentsRoundOrSphereProduct
    (h : ∀ D : OrientedThreeStage.{u},
      DiscardedComponentsRoundOrSphereProduct D.toClosedOrientedManifold)
    (D : ClosedOrientedManifold.{u} 3) : D.componentwiseStandardFactor := by
  intro C
  have hstage := h (OrientedThreeStage.ofClosedOrientedManifold D)
  rw [OrientedThreeStage.ofClosedOrientedManifold_toClosedOrientedManifold] at hstage
  rcases hstage C with hp | hs
  · exact ⟨D.component C,
      isStandardFactor_of_isPositiveSpaceFormModel sphericalSpaceFormCovering_holds hp,
      ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩
  · exact ⟨D.component C, isStandardFactor_of_isSphereTwoTimesCircleFactor hs,
      ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩

theorem isPoincareStandard_of_forall_discardedComponentsRoundOrSphereProduct
    (h : ∀ D : OrientedThreeStage.{u},
      DiscardedComponentsRoundOrSphereProduct D.toClosedOrientedManifold)
    (D : ClosedOrientedManifold.{u} 3) (C : ConnectedComponents D.Carrier) :
    isPoincareStandard (D.component C).Carrier :=
  componentwise_isPoincareStandard_of_componentwiseStandardFactor D
    (componentwiseStandardFactor_of_forall_discardedComponentsRoundOrSphereProduct h D) C

theorem smoothPoincareConjecture_of_forall_discardedComponentsRoundOrSphereProduct
    (h : ∀ D : OrientedThreeStage.{u},
      DiscardedComponentsRoundOrSphereProduct D.toClosedOrientedManifold) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.smoothPoincareConjecture.{u} := by
  intro M _ _ _ _ _ _ _
  obtain ⟨o⟩ := Manifold.exists_manifoldOrientation_of_simply_connected
    (E := EuclideanSpace ℝ (Fin 3)) (M := M) (n := 3) (by simp)
  let D : ClosedOrientedManifold.{u} 3 := { Carrier := M, orientation := o }
  exact exists_diffeomorph_standardThreeSphere_of_isPoincareStandard
    (ClosedOrientedManifold.isPoincareStandard_of_component D
      (ConnectedComponents.mk (Classical.choice (inferInstance : Nonempty M)))
      (isPoincareStandard_of_forall_discardedComponentsRoundOrSphereProduct h D
        (ConnectedComponents.mk (Classical.choice (inferInstance : Nonempty M)))))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.Topology

universe u

variable {M Q : ClosedOrientedManifold.{u} 3}

theorem SphericalCutCapTransition.not_isEmpty_discarded_of_isEmpty_index
    (E : SphericalCutCapTransition M Q) [IsEmpty E.tubes.Index] :
    ¬ IsEmpty E.discarded.Carrier := by
  intro h
  rcases E.nontrivial with hindex | hdiscarded
  · exact IsEmpty.false hindex.some
  · exact h.false hdiscarded.some

theorem SphericalCutCapTransition.nonempty_connectedComponents_discarded_of_isEmpty_index
    (E : SphericalCutCapTransition M Q) [IsEmpty E.tubes.Index] :
    Nonempty (ConnectedComponents E.discarded.Carrier) := by
  have hd := E.not_isEmpty_discarded_of_isEmpty_index
  exact ⟨ConnectedComponents.mk (Classical.choice (not_isEmpty_iff.mp hd))⟩

end DifferentialGeometry.Topology
