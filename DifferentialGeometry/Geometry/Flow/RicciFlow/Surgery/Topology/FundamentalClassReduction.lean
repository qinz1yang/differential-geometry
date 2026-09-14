import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalClassRealizationTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassFrontier

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

section Unconditional

variable (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (x : M)

def ClosedThreeManifoldPuncturedVanishing : Prop :=
  Subsingleton (IntegralHomology ({x}ᶜ : Set M) 2) ∧
    Subsingleton (IntegralHomology ({x}ᶜ : Set M) 3)

end Unconditional

section Proof

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [ConnectedSpace M]

theorem exists_unique_fundamentalClass_of_puncturedVanishing_of_localClassTransport
    {x : M} {o : TangentOrientationSection M}
    (h : ClosedThreeManifoldPuncturedVanishing M x) (htransport : localClassTransport o) :
    ∃! z : IntegralHomology M 3, ∀ y : M,
      absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y := by
  obtain ⟨h₂, h₃⟩ := h
  exact exists_unique_fundamentalClass_of_surjective_and_injective o
    (localClassRealizationLocallyConstant_of_localClassTransport o htransport) x
    (absoluteToRelative_surjective_of_subsingleton_punctured x h₂)
    (absoluteToRelative_compl_singleton_injective_of_subsingleton x h₃)

end Proof

section Frontier

def ClosedThreeManifoldFundamentalClassFrontier : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [ConnectedSpace M] (x : M) (o : TangentOrientationSection M),
    ClosedThreeManifoldPuncturedVanishing M x ∧ localClassTransport o

theorem fundamentalClass_exists_of_closedThreeManifoldFrontier
    (h : ClosedThreeManifoldFundamentalClassFrontier.{u})
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [ConnectedSpace M]
    (x : M) (o : TangentOrientationSection M) :
    ∃ z : IntegralHomology M 3, ∀ y : M,
      absoluteToRelative M ({y}ᶜ) 3 z = localOrientationClass o y :=
  (exists_unique_fundamentalClass_of_puncturedVanishing_of_localClassTransport
    (h M x o).1 (h M x o).2).exists

end Frontier

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ClosedThreeManifoldPuncturedVanishing,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_fundamentalClass_of_puncturedVanishing_of_localClassTransport,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ClosedThreeManifoldFundamentalClassFrontier,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fundamentalClass_exists_of_closedThreeManifoldFrontier] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
