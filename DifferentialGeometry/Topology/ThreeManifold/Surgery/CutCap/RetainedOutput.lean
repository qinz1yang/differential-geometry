import DifferentialGeometry.Topology.ThreeManifold.Surgery.CutCap.CappingRealization

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace CutCapTopology

variable {M Q D N : Type*} [TopologicalSpace M] [TopologicalSpace Q] [TopologicalSpace D]
  [TopologicalSpace N]

theorem isClopen_retainedCore (E : CutCapTopology M Q D N) : IsClopen E.retainedCore := by
  have hcont : Continuous
      (fun x : E.tubes.core => E.presentation (E.capping.coreInclusion x)) :=
    E.presentation.continuous.comp E.capping.coreInclusion.continuous
  have hset : E.retainedCore =
      (fun x : E.tubes.core => E.presentation (E.capping.coreInclusion x)) ⁻¹'
        Set.range (Sum.inl : Q → Q ⊕ D) := by
    ext x
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, hq.symm⟩
    · rintro ⟨q, hq⟩
      exact ⟨q, hq.symm⟩
  rw [hset]
  exact isClopen_range_inl.preimage hcont

theorem connectedComponent_subset_compl_retainedCore (E : CutCapTopology M Q D N)
    (x : E.tubes.core) (hx : x ∉ E.retainedCore) :
    connectedComponent x ⊆ E.retainedCoreᶜ :=
  (isClopen_retainedCore E).compl.connectedComponent_subset hx

end CutCapTopology

set_option autoImplicit false

namespace CutCapTopology

variable {M Q D N : Type*} [TopologicalSpace M] [TopologicalSpace Q]
    [TopologicalSpace D] [TopologicalSpace N]

theorem retainedCore_isOpen (E : CutCapTopology M Q D N) : IsOpen E.retainedCore :=
  E.isClopen_retainedCore.isOpen

end CutCapTopology

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}}

def retainedCoreOpens (X : SmoothCutCapTransition P Q D N) :
    TopologicalSpace.Opens X.trace.tubes.core :=
  ⟨X.trace.retainedCore, X.trace.retainedCore_isOpen⟩

end SmoothCutCapTransition

namespace CutCapTopology

variable {M Q D N : Type*} [TopologicalSpace M] [TopologicalSpace Q]
  [TopologicalSpace D] [TopologicalSpace N]

def retainedOutput (E : CutCapTopology M Q D N) (x : E.retainedCore) : Q :=
  Classical.choose x.2

theorem retainedOutput_eq (E : CutCapTopology M Q D N) (x : E.retainedCore) :
    E.presentation (E.capping.coreInclusion x.1) = Sum.inl (E.retainedOutput x) :=
  Classical.choose_spec x.2

theorem continuous_retainedOutput (E : CutCapTopology M Q D N) :
    Continuous E.retainedOutput := by
  refine (Topology.IsEmbedding.inl (X := Q) (Y := D)).continuous_iff.mpr ?_
  have h : (Sum.inl ∘ E.retainedOutput) =
      fun x : E.retainedCore => E.presentation (E.capping.coreInclusion x.1) := by
    funext x
    exact (E.retainedOutput_eq x).symm
  rw [h]
  exact E.presentation.continuous.comp
    (E.capping.coreInclusion.continuous.comp continuous_subtype_val)

end CutCapTopology

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}}

def retainedOutputMap (X : SmoothCutCapTransition P Q D N) :
    C((X.retainedCoreOpens : Type u), Q.Carrier) :=
  ⟨X.trace.retainedOutput, X.trace.continuous_retainedOutput⟩

theorem retainedOutputMap_apply (X : SmoothCutCapTransition P Q D N)
    (x : X.retainedCoreOpens) :
    X.retainedOutputMap x = X.trace.retainedOutput x := rfl

theorem retainedOutputMap_eq (X : SmoothCutCapTransition P Q D N)
    (x : X.retainedCoreOpens) :
    X.trace.presentation (X.trace.capping.coreInclusion x.1) =
      Sum.inl (X.retainedOutputMap x) :=
  X.trace.retainedOutput_eq x

end SmoothCutCapTransition

namespace SmoothCutCapCompletion

variable {P Q D N : OrientedThreeStage.{u}} {X : SmoothCutCapTransition P Q D N}

theorem exists_retainedOutputMap_eq (h : SmoothCutCapCompletion X)
    (c : ConnectedComponents Q.Carrier) :
    ∃ x : X.retainedCoreOpens, ConnectedComponents.mk (X.retainedOutputMap x) = c := by
  obtain ⟨x, q, hpres, hmk⟩ := h.every_component_meets_core c
  have hpres' : X.trace.presentation (X.trace.capping.coreInclusion x) = Sum.inl q := by
    rw [← h.coreInclusion_eq x, ← X.presentation_eq]
    exact hpres
  have hx : x ∈ X.trace.retainedCore := ⟨q, hpres'⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  have h1 : X.trace.presentation (X.trace.capping.coreInclusion x) =
      Sum.inl (X.retainedOutputMap ⟨x, hx⟩) := X.retainedOutputMap_eq ⟨x, hx⟩
  rw [hpres'] at h1
  rw [← Sum.inl_injective h1, hmk]

end SmoothCutCapCompletion

private def twoPointTubeSystem : TubeSystem (PUnit.{1} ⊕ PUnit.{1}) where
  Index := PEmpty
  finiteIndex := inferInstance
  tube := fun a => PEmpty.elim a
  embedding := fun a => PEmpty.elim a
  disjoint := fun a => PEmpty.elim a

private theorem twoPointTubeSystem_core : twoPointTubeSystem.core = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  simp only [TubeSystem.core, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
  intro a
  exact PEmpty.elim a

private def twoPointCapping : Capping twoPointTubeSystem (PUnit.{1} ⊕ PUnit.{1}) where
  coreInclusion := ⟨Subtype.val, continuous_subtype_val⟩
  coreEmbedding := Topology.IsEmbedding.subtypeVal
  cap := fun b => PEmpty.elim b.1
  capEmbedding := fun b => PEmpty.elim b.1
  attaching := fun b => PEmpty.elim b.1
  boundary_eq := fun b => PEmpty.elim b.1
  exhaustive := by
    have hunion : (⋃ b : twoPointTubeSystem.Boundary,
        Set.range (PEmpty.elim b.1 : C(ThreeBall, PUnit.{1} ⊕ PUnit.{1}))) = ∅ := by
      apply Set.iUnion_eq_empty.mpr
      intro b
      exact PEmpty.elim b.1
    rw [hunion, Set.union_empty]
    apply Set.range_eq_univ.mpr
    intro x
    exact ⟨⟨x, by rw [twoPointTubeSystem_core]; exact Set.mem_univ x⟩, rfl⟩
  core_cap_intersection := fun b => PEmpty.elim b.1
  cap_disjoint := fun b => PEmpty.elim b.1

private def twoPointCutCap :
    CutCapTopology (PUnit.{1} ⊕ PUnit.{1}) PUnit.{1} PUnit.{1} (PUnit.{1} ⊕ PUnit.{1}) where
  tubes := twoPointTubeSystem
  capping := twoPointCapping
  presentation := Homeomorph.refl _
  nontrivial := Or.inr ⟨PUnit.unit⟩

theorem exists_cutCapTopology_retainedOutput :
    ∃ (E : CutCapTopology (PUnit.{1} ⊕ PUnit.{1}) PUnit.{1} PUnit.{1}
        (PUnit.{1} ⊕ PUnit.{1})) (x : E.retainedCore),
      E.retainedOutput x = PUnit.unit :=
  ⟨twoPointCutCap,
    ⟨⟨Sum.inl PUnit.unit,
        show Sum.inl PUnit.unit ∈ twoPointTubeSystem.core from by
          rw [twoPointTubeSystem_core]
          exact Set.mem_univ _⟩,
      ⟨PUnit.unit, rfl⟩⟩,
    Subsingleton.elim _ _⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
