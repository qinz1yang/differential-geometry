import DifferentialGeometry.Topology.ThreeManifold.CutCap
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandard
import DifferentialGeometry.Topology.ThreeManifold.SphericalSpaceFormTrivial

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

def ClosedOrientedManifold.componentwiseStandardFactor (D : ClosedOrientedManifold.{u} 3) : Prop :=
  ∀ C : ConnectedComponents D.Carrier, ∃ N : ConnectedClosedOrientedManifold.{u} 3,
    isStandardFactor N ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (D.component C).toClosedOrientedManifold N.toClosedOrientedManifold)

def ClosedOrientedManifold.componentwiseConnectedSumStandardFactor
    (D : ClosedOrientedManifold.{u} 3) : Prop :=
  ∀ C : ConnectedComponents D.Carrier, ∃ L : List (ConnectedClosedOrientedManifold.{u} 3),
    (∀ F ∈ L, isStandardFactor F) ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (D.component C).toClosedOrientedManifold (finiteConnectedSum L).toClosedOrientedManifold)

theorem componentwise_isPoincareStandard_of_componentwiseConnectedSumStandardFactor
    (D : ClosedOrientedManifold.{u} 3) (h : D.componentwiseConnectedSumStandardFactor) :
    ∀ C : ConnectedComponents D.Carrier, isPoincareStandard (D.component C).Carrier := by
  intro C
  obtain ⟨L, hL, ⟨ρ⟩⟩ := h C
  exact isPoincareStandard_of_diffeomorph ρ.1 (isPoincareStandard_finite_sum L hL)

theorem componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactor
    (D : ClosedOrientedManifold.{u} 3) (h : D.componentwiseStandardFactor) :
    D.componentwiseConnectedSumStandardFactor := by
  intro C
  obtain ⟨N, hN, ⟨ρ⟩⟩ := h C
  exact ⟨[N], by simpa using hN, ⟨ρ⟩⟩

theorem componentwise_isPoincareStandard_of_componentwiseStandardFactor
    (D : ClosedOrientedManifold.{u} 3) (h : D.componentwiseStandardFactor) :
    ∀ C : ConnectedComponents D.Carrier, isPoincareStandard (D.component C).Carrier :=
  componentwise_isPoincareStandard_of_componentwiseConnectedSumStandardFactor D
    (componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactor D h)

theorem componentwiseStandardFactor_of_isEmpty (D : ClosedOrientedManifold.{u} 3)
    [IsEmpty D.Carrier] : D.componentwiseStandardFactor := by
  have hEmpty : IsEmpty (ConnectedComponents D.Carrier) :=
    ConnectedComponents.isEmpty_iff_isEmpty.mpr inferInstance
  exact fun C => (hEmpty.false C).elim

namespace SphericalSpaceFormGroup

private theorem sphereDiffeo_one :
    DifferentialGeometry.Geometry.sphereDiffeo (n := 3)
        (1 : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) =
      Diffeomorph.refl (𝓡 3) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞ := by
  ext x
  simp [DifferentialGeometry.Geometry.sphereDiffeo_coe]

def trivial : SphericalSpaceFormGroup where
  group := ⊥
  finite := inferInstance
  positive := fun γ => by
    have hγ : γ = 1 := Subsingleton.elim γ 1
    subst hγ
    simp only [OneMemClass.coe_one, sphereDiffeo_one]
    exact Diffeomorph.preservesOrientation_refl _
  free := fun γ _ _ => Subsingleton.elim γ 1

theorem subsingleton_trivial : Subsingleton ↥(trivial.group) := by
  change Subsingleton ↥(⊥ : Subgroup (EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)))
  infer_instance

end SphericalSpaceFormGroup

theorem isStandardFactor_standardThreeSphereLift :
    isStandardFactor standardThreeSphereLift.{u} :=
  Or.inl ⟨SphericalSpaceFormGroup.trivial,
    (exists_orientedDiffeomorph_standardThreeSphere_of_subsingleton_group
      SphericalSpaceFormGroup.trivial SphericalSpaceFormGroup.subsingleton_trivial).map
      ClosedOrientedManifold.OrientedDiffeomorph.symm⟩

theorem exists_nonempty_isStandardFactor :
    ∃ N : ConnectedClosedOrientedManifold.{u} 3, isStandardFactor N ∧ Nonempty N.Carrier :=
  ⟨standardThreeSphereLift.{u}, isStandardFactor_standardThreeSphereLift,
    ⟨ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩⟩⟩

namespace SphericalTubeSystem

variable {M : ClosedOrientedManifold.{u} 3}

def emptyIndex (M : ClosedOrientedManifold.{u} 3) : SphericalTubeSystem M where
  Index := PEmpty
  finiteIndex := inferInstance
  tube := fun a => PEmpty.elim a
  smooth := fun a => PEmpty.elim a
  disjoint := fun a => PEmpty.elim a

theorem isEmpty_boundary_of_isEmpty_index (T : SphericalTubeSystem M) [IsEmpty T.Index] :
    IsEmpty T.Boundary :=
  ⟨fun b => isEmptyElim b.1⟩

theorem core_eq_univ_of_isEmpty_index (T : SphericalTubeSystem M) [IsEmpty T.Index] :
    T.core = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  rw [SphericalTubeSystem.core]
  simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
  intro a
  exact isEmptyElim a

theorem emptyIndex_core (M : ClosedOrientedManifold.{u} 3) : (emptyIndex M).core = Set.univ :=
  @core_eq_univ_of_isEmpty_index M (emptyIndex M) (inferInstanceAs (IsEmpty PEmpty))

end SphericalTubeSystem

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3}

theorem range_coreInclusion_eq_univ_of_isEmpty_index (E : SphericalCutCapTransition M Q)
    [IsEmpty E.tubes.Index] : Set.range E.capping.coreInclusion = Set.univ := by
  have hcap : (⋃ b : E.tubes.Boundary, Set.range (E.capping.cap b)) = ∅ := by
    rw [Set.iUnion_eq_empty]
    intro b
    exact ((SphericalTubeSystem.isEmpty_boundary_of_isEmpty_index E.tubes).false b).elim
  have h := E.capping.exhaustive
  rw [hcap, Set.union_empty] at h
  exact h

theorem retainedLocus_eq_univ_of_isEmpty_index (E : SphericalCutCapTransition M Q)
    [IsEmpty E.tubes.Index] :
    {q : Q.Carrier | ∃ x : E.tubes.core,
      E.presentation (E.capping.coreInclusion x) = Sum.inl q} = Set.univ := by
  have hcap : {q : Q.Carrier | ∃ b : E.tubes.Boundary, ∃ z : ClosedCell 3,
      E.presentation (E.capping.cap b z) = Sum.inl q} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun q => ?_
    rintro ⟨b, -⟩
    exact (SphericalTubeSystem.isEmpty_boundary_of_isEmpty_index E.tubes).false b
  have h := E.retained_complement
  rw [hcap] at h
  have hsub : Set.univ ⊆ interior {q : Q.Carrier | ∃ x : E.tubes.core,
      E.presentation (E.capping.coreInclusion x) = Sum.inl q} := by
    intro q _
    by_contra hq
    have hq' : q ∈ (interior {q : Q.Carrier | ∃ x : E.tubes.core,
        E.presentation (E.capping.coreInclusion x) = Sum.inl q})ᶜ := hq
    rw [h] at hq'
    exact hq'
  refine Set.eq_univ_of_forall fun q => interior_subset (hsub (Set.mem_univ q))

theorem poincareControlled_of_componentwiseConnectedSumStandardFactor
    (E : SphericalCutCapTransition M Q) (h : E.discarded.componentwiseConnectedSumStandardFactor) :
    E.poincareControlled :=
  componentwise_isPoincareStandard_of_componentwiseConnectedSumStandardFactor E.discarded h

theorem poincareControlled_of_componentwiseStandardFactor (E : SphericalCutCapTransition M Q)
    (h : E.discarded.componentwiseStandardFactor) : E.poincareControlled :=
  poincareControlled_of_componentwiseConnectedSumStandardFactor E
    (componentwiseConnectedSumStandardFactor_of_componentwiseStandardFactor E.discarded h)

theorem poincareControlled_of_isEmpty_discarded (E : SphericalCutCapTransition M Q)
    [IsEmpty E.discarded.Carrier] : E.poincareControlled :=
  poincareControlled_of_componentwiseStandardFactor E
    (componentwiseStandardFactor_of_isEmpty E.discarded)

end SphericalCutCapTransition

end DifferentialGeometry.Topology
