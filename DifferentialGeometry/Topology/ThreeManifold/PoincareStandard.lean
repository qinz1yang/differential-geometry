import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Finite
import DifferentialGeometry.Topology.ThreeManifold.StandardFactors
import DifferentialGeometry.Topology.Manifold.Components
import DifferentialGeometry.Topology.ThreeManifold.Surgery.CutCap.Defs

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

structure StandardConnectedSumPresentation (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] where
  factors : List (ConnectedClosedOrientedManifold.{u} 3)
  standard : ∀ F ∈ factors, isStandardFactor F
  diffeomorph : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ (finiteConnectedSum factors).Carrier

def isStandardConnectedSum (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] : Prop :=
  Nonempty (StandardConnectedSumPresentation M)

theorem isStandardConnectedSum_connectedSpace {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (h : isStandardConnectedSum M) :
    ConnectedSpace M := by
  obtain ⟨p⟩ := h
  exact p.diffeomorph.toHomeomorph.connectedSpace_iff.mpr inferInstance

theorem isStandardConnectedSum_compactSpace {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] (h : isStandardConnectedSum M) :
    CompactSpace M := by
  obtain ⟨p⟩ := h
  exact p.diffeomorph.symm.toHomeomorph.compactSpace

theorem not_isStandardConnectedSum_of_isEmpty (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsEmpty M] : ¬isStandardConnectedSum M := by
  intro h
  let := isStandardConnectedSum_connectedSpace h
  exact isEmptyElim (Classical.choice (inferInstance : Nonempty M))

theorem isStandardConnectedSum_of_diffeomorph
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (f : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) (hN : isStandardConnectedSum N) :
    isStandardConnectedSum M := by
  obtain ⟨p⟩ := hN
  exact ⟨⟨p.factors, p.standard, f.trans p.diffeomorph⟩⟩

theorem isStandardConnectedSum_iff_of_diffeomorph
    {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    (f : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N) :
    isStandardConnectedSum M ↔ isStandardConnectedSum N :=
  ⟨isStandardConnectedSum_of_diffeomorph f.symm, isStandardConnectedSum_of_diffeomorph f⟩

theorem isStandardConnectedSum_finite_sum
    (L : List (ConnectedClosedOrientedManifold.{u} 3))
    (hL : ∀ F ∈ L, isStandardFactor F) : isStandardConnectedSum (finiteConnectedSum L).Carrier :=
  ⟨⟨L, hL, Diffeomorph.refl _ _ ∞⟩⟩

theorem isStandardConnectedSum_sphere : isStandardConnectedSum standardThreeSphereLift.{u}.Carrier := by
  exact isStandardConnectedSum_finite_sum [] (by simp)

theorem isStandardConnectedSum_of_standard_factor (M : ConnectedClosedOrientedManifold.{u} 3)
    (h : isStandardFactor M) : isStandardConnectedSum M.Carrier := by
  exact isStandardConnectedSum_finite_sum [M] (by simpa using h)

@[simp] theorem isStandardConnectedSum_opposite_iff (M : ConnectedClosedOrientedManifold.{u} 3) :
    isStandardConnectedSum M.opposite.Carrier ↔ isStandardConnectedSum M.Carrier := Iff.rfl

def componentIsPoincareStandard (M : ClosedOrientedManifold.{u} 3)
    (C : ConnectedComponents M.Carrier) : Prop :=
  isStandardConnectedSum (M.component C).Carrier

def SphericalCutCapTransition.poincareControlled {M Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M Q) : Prop :=
  E.controlledBy componentIsPoincareStandard

theorem SphericalCutCapTransition.poincareControlled_iff
    {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q) :
    E.poincareControlled ↔
      ∀ C : ConnectedComponents E.discarded.Carrier,
        isStandardConnectedSum (E.discarded.component C).Carrier := Iff.rfl

def FiniteCutCapTrace.poincareControlled (T : FiniteCutCapTrace.{u}) : Prop :=
  T.controlledBy componentIsPoincareStandard

theorem FiniteCutCapTrace.poincareControlled_iff (T : FiniteCutCapTrace.{u}) :
    T.poincareControlled ↔ ∀ i : Fin T.eventCount, (T.transition i).poincareControlled := Iff.rfl

theorem FiniteCutCapTrace.discarded_poincareStandard (T : FiniteCutCapTrace.{u})
    (h : T.poincareControlled) (i : Fin T.eventCount)
    (C : ConnectedComponents (T.transition i).discarded.Carrier) :
    isStandardConnectedSum ((T.transition i).discarded.component C).Carrier := h i C

end DifferentialGeometry.Topology
