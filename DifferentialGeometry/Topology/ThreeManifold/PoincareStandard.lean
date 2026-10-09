import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Finite
import DifferentialGeometry.Topology.ThreeManifold.StandardFactors
import DifferentialGeometry.Topology.Manifold.Components
import DifferentialGeometry.Topology.ThreeManifold.CutCap

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

structure PoincareStandardPresentation (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] where
  factors : List (ConnectedClosedOrientedManifold.{u} 3)
  standard : ∀ F ∈ factors, isStandardFactor F
  diffeomorph : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ (finiteConnectedSum factors).Carrier

def isPoincareStandard (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop :=
  Nonempty (PoincareStandardPresentation M)

theorem isPoincareStandard_connectedSpace {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (h : isPoincareStandard M) :
    ConnectedSpace M := by
  obtain ⟨p⟩ := h
  exact p.diffeomorph.toHomeomorph.connectedSpace_iff.mpr inferInstance

theorem isPoincareStandard_compactSpace {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (h : isPoincareStandard M) :
    CompactSpace M := by
  obtain ⟨p⟩ := h
  exact p.diffeomorph.symm.toHomeomorph.compactSpace

theorem not_isPoincareStandard_of_isEmpty (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsEmpty M] : ¬isPoincareStandard M := by
  intro h
  let := isPoincareStandard_connectedSpace h
  exact isEmptyElim (Classical.choice (inferInstance : Nonempty M))

theorem isPoincareStandard_of_diffeomorph
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (f : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) (hN : isPoincareStandard N) :
    isPoincareStandard M := by
  obtain ⟨p⟩ := hN
  exact ⟨⟨p.factors, p.standard, f.trans p.diffeomorph⟩⟩

theorem isPoincareStandard_iff_of_diffeomorph
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (f : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) :
    isPoincareStandard M ↔ isPoincareStandard N :=
  ⟨isPoincareStandard_of_diffeomorph f.symm, isPoincareStandard_of_diffeomorph f⟩

theorem isPoincareStandard_finite_sum
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (hL : ∀ F ∈ L, isStandardFactor F) : isPoincareStandard (finiteConnectedSum L).Carrier :=
  ⟨⟨L, hL, Diffeomorph.refl _ _ ∞⟩⟩

theorem isPoincareStandard_sphere : isPoincareStandard standardThreeSphereLift.{u}.Carrier := by
  exact isPoincareStandard_finite_sum [] (by simp)

theorem isPoincareStandard_of_standard_factor (M : ConnectedClosedOrientedManifold.{u} 3)
    (h : isStandardFactor M) : isPoincareStandard M.Carrier := by
  exact isPoincareStandard_finite_sum [M] (by simpa using h)

@[simp] theorem isPoincareStandard_opposite_iff (M : ConnectedClosedOrientedManifold.{u} 3) :
    isPoincareStandard M.opposite.Carrier ↔ isPoincareStandard M.Carrier := Iff.rfl

def componentIsPoincareStandard (M : ClosedOrientedManifold.{u} 3)
    (C : ConnectedComponents M.Carrier) : Prop :=
  isPoincareStandard (M.component C).Carrier

def SphericalCutCapTransition.poincareControlled {M Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M Q) : Prop :=
  E.controlledBy componentIsPoincareStandard

theorem SphericalCutCapTransition.poincareControlled_iff
    {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q) :
    E.poincareControlled ↔
      ∀ C : ConnectedComponents E.discarded.Carrier,
        isPoincareStandard (E.discarded.component C).Carrier := Iff.rfl

def FiniteCutCapTrace.poincareControlled (T : FiniteCutCapTrace.{u}) : Prop :=
  T.controlledBy componentIsPoincareStandard

theorem FiniteCutCapTrace.poincareControlled_iff (T : FiniteCutCapTrace.{u}) :
    T.poincareControlled ↔ ∀ i : Fin T.eventCount, (T.transition i).poincareControlled := Iff.rfl

theorem FiniteCutCapTrace.discarded_poincareStandard (T : FiniteCutCapTrace.{u})
    (h : T.poincareControlled) (i : Fin T.eventCount)
    (C : ConnectedComponents (T.transition i).discarded.Carrier) :
    isPoincareStandard ((T.transition i).discarded.component C).Carrier := h i C

end DifferentialGeometry.Topology
