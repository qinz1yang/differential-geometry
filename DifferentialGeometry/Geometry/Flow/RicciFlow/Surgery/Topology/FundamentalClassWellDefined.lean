import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Homology

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M]

def fundamentalClassRealization (o : TangentOrientationSection M) (z : IntegralHomology M 3) : Prop :=
  ∀ x : M, absoluteToRelative M ({x}ᶜ) 3 z = localOrientationClass o x

namespace FundamentalClassRealization

theorem eq_of_injective {o : TangentOrientationSection M} {z z' : IntegralHomology M 3}
    (hz : fundamentalClassRealization o z) (hz' : fundamentalClassRealization o z') (x : M)
    (hinj : Function.Injective (absoluteToRelative M ({x}ᶜ) 3)) : z = z' :=
  hinj (by rw [hz x, hz' x])

theorem eq_of_subsingleton {o : TangentOrientationSection M} {z z' : IntegralHomology M 3}
    (hz : fundamentalClassRealization o z) (hz' : fundamentalClassRealization o z') (x : M)
    (hsub : Subsingleton (IntegralHomology ({x}ᶜ : Set M) 3)) : z = z' :=
  eq_of_injective hz hz' x
    (absoluteToRelative_compl_singleton_injective_of_subsingleton x hsub)

theorem eq_choose_of_injective {o : TangentOrientationSection M}
    (h : ∃ z : IntegralHomology M 3, fundamentalClassRealization o z) (x : M)
    (hinj : Function.Injective (absoluteToRelative M ({x}ᶜ) 3))
    {z' : IntegralHomology M 3} (hz' : fundamentalClassRealization o z') :
    Classical.choose h = z' :=
  eq_of_injective (Classical.choose_spec h) hz' x hinj

theorem existsUnique_iff_exists_and_unique (o : TangentOrientationSection M) :
    (∃! z : IntegralHomology M 3, fundamentalClassRealization o z) ↔
      (∃ z : IntegralHomology M 3, fundamentalClassRealization o z) ∧
        ∀ z z' : IntegralHomology M 3,
          fundamentalClassRealization o z → fundamentalClassRealization o z' → z = z' :=
  ⟨fun h => ⟨h.exists, fun _ _ hz hz' => h.unique hz hz'⟩,
    fun h => existsUnique_of_exists_of_unique h.1 h.2⟩

end FundamentalClassRealization

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Lean in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.fundamentalClassRealization,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FundamentalClassRealization.eq_of_injective,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FundamentalClassRealization.eq_of_subsingleton,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FundamentalClassRealization.eq_choose_of_injective,
      ``DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.FundamentalClassRealization.existsUnique_iff_exists_and_unique] do
    let axs ← Lean.collectAxioms n
    unless axs.all (fun a => allowed.contains a) do
      throwError "unexpected axioms for {n}: {axs}"
