import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalClassRealizationTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassFrontier

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Topology

universe u

def PuncturedThreeManifoldTopHomologyVanishing
    (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (x₀ : M) : Prop :=
  (Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 2) ∧
    Subsingleton (IntegralHomology ({x₀}ᶜ : Set M) 3)) ∧
    ∀ x : M, Subsingleton (IntegralHomology ({x}ᶜ : Set M) 3)

theorem exists_unique_fundamentalClass_of_puncturedVanishing_of_localClassTransport
    (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [ConnectedSpace M]
    (x₀ : M) (o : TangentOrientationSection M)
    (hvan : PuncturedThreeManifoldTopHomologyVanishing M x₀)
    (htransport : localClassTransport o) :
    ∃! z : IntegralHomology M 3, ∀ x : M,
      absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x := by
  obtain ⟨⟨h₂, h₃⟩, htop⟩ := hvan
  exact exists_unique_fundamentalClass_of_surjective_and_injective o
    (localClassRealizationLocallyConstant_of_localClassTransport o htransport) x₀
    (absoluteToRelative_surjective_of_subsingleton_punctured x₀ h₂)
    (absoluteToRelative_compl_singleton_injective_of_subsingleton x₀ h₃)

def ClosedThreeManifoldFundamentalClassFrontier : Prop :=
  (∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (x₀ : M), PuncturedThreeManifoldTopHomologyVanishing M x₀) ∧
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (o : TangentOrientationSection M), localClassTransport o

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.PuncturedThreeManifoldTopHomologyVanishing,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_unique_fundamentalClass_of_puncturedVanishing_of_localClassTransport,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ClosedThreeManifoldFundamentalClassFrontier] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
