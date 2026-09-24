import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveComponentModels
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.DeckCovering
import DifferentialGeometry.Topology.FundamentalGroup.RealProjective

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Algebra.Group

namespace DifferentialGeometry.Topology

theorem finite_fundamentalGroup_realProjectiveThree :
    Finite (FundamentalGroup RealProjectiveThree realProjectiveThreeBasepoint) :=
  Finite.of_equiv TwoElementGroup fundamentalGroupRealProjectiveThreeEquivTwoElement.symm

theorem not_subsingleton_fundamentalGroup_realProjectiveThree :
    ¬ Subsingleton (FundamentalGroup RealProjectiveThree realProjectiveThreeBasepoint) := by
  intro h
  have h' : Subsingleton TwoElementGroup :=
    ⟨fun a b => fundamentalGroupRealProjectiveThreeEquivTwoElement.symm.injective
      (Subsingleton.elim _ _)⟩
  have h2 : (0 : ZMod 2) = 1 := Multiplicative.ofAdd.injective (Subsingleton.elim _ _)
  exact (by decide : ¬ ((0 : ZMod 2) = 1)) h2

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry
open DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

def finiteFundamentalGroupForcesTrivial : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] (m₀ : M),
    Finite (FundamentalGroup M m₀) → Subsingleton (FundamentalGroup M m₀)

theorem finiteFundamentalGroupForcesTrivial_false :
    ¬ finiteFundamentalGroupForcesTrivial.{0} :=
  fun h => not_subsingleton_fundamentalGroup_realProjectiveThree
    (h RealProjectiveThree realProjectiveThreeBasepoint
      finite_fundamentalGroup_realProjectiveThree)

theorem subsingleton_deckGroup_of_subsingleton_fundamentalGroup
    (D : RoundSphereQuotient (EuclideanSpace ℝ (Fin 4)) 3) (x₀ : D.Q)
    (h : Subsingleton (FundamentalGroup D.Q x₀)) : Subsingleton D.Γ :=
  (RoundSphereQuotient.subsingleton_deckGroup_iff_subsingleton_fundamentalGroup
    D x₀ (by norm_num)).mpr h

theorem not_subsingleton_fundamentalGroup_of_not_subsingleton_deckGroup
    (D : RoundSphereQuotient (EuclideanSpace ℝ (Fin 4)) 3) (x₀ : D.Q)
    (h : ¬ Subsingleton D.Γ) : ¬ Subsingleton (FundamentalGroup D.Q x₀) :=
  fun h' => h (subsingleton_deckGroup_of_subsingleton_fundamentalGroup D x₀ h')

theorem exists_diffeomorph_sphereThree_of_subsingleton_deckGroup
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    (D : RoundSphereQuotient (EuclideanSpace ℝ (Fin 4)) 3) [Subsingleton D.Γ]
    (e : Diffeomorph (𝓡 3) I3 D.Q M ∞) :
    Nonempty (Diffeomorph (𝓡 3) I3 (Sphere 3) M ∞) :=
  ⟨(RoundSphereQuotient.sphereDiffeomorph_of_subsingleton_deckGroup D).trans e⟩

theorem subsingleton_fundamentalGroup_sphereThree (x₀ : Sphere 3) :
    Subsingleton (FundamentalGroup (Sphere 3) x₀) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  let : SimplyConnectedSpace (Sphere 3) :=
    RoundSphereQuotient.simplyConnectedSpace_sphere_of_one_lt
      (E := EuclideanSpace ℝ (Fin 4)) (n := 3) (by norm_num)
  exact inferInstance

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
