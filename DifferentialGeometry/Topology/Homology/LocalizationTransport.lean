import DifferentialGeometry.Topology.Homology.RelativeFunctoriality
import DifferentialGeometry.Topology.Homology.Integral
import DifferentialGeometry.Topology.Homology.RelativeHomeomorphism
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set
open scoped Topology unitInterval

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

theorem integralRelativeHomologyMap_absoluteToRelative_eq_of_homotopic_id
    (n : ℕ) (f : C(X, X)) {x y : X}
    (hf : MapsTo f ({x}ᶜ : Set X) ({y}ᶜ : Set X))
    (hhom : f.Homotopic (.id X)) (w : integralSingularHomology n X) :
    integralRelativeHomologyMap n f hf (integralAbsoluteToRelative n ({x}ᶜ) w) =
      integralAbsoluteToRelative n ({y}ᶜ) w := by
  have h := congrArg
    (fun k : integralSingularHomology n X →ₗ[ℤ] integralRelativeHomology n ({y}ᶜ) => k w)
    (integralAbsoluteToRelative_natural n f hf)
  simp only [LinearMap.comp_apply] at h
  rw [← h, integralSingularHomologyMap_homotopic n hhom, integralSingularHomologyMap_id,
    LinearMap.id_apply]

theorem integralRelativeHomologyMap_id_of_mapsTo (n : ℕ) (A : Set X)
    (h : MapsTo (ContinuousMap.id X) A A) :
    integralRelativeHomologyMap n (ContinuousMap.id X) h = LinearMap.id := by
  unfold integralRelativeHomologyMap
  rw [integralRelativeChainMap_eq_id (ContinuousMap.id X) A h rfl,
    HomologicalComplex.homologyMap_id]
  rfl

theorem injective_integralRelativeHomologyMap_of_homeomorph (n : ℕ) (e : X ≃ₜ Y)
    {A : Set X} {B : Set Y} (he : MapsTo e A B) (he' : MapsTo e.symm B A) :
    Function.Injective (integralRelativeHomologyMap n (⟨e, e.continuous⟩ : C(X, Y)) he) := by
  rw [← integralRelativeHomologyHomeomorphIso_hom n e A B he he']
  exact (integralRelativeHomologyHomeomorphIso n e A B he he').toLinearEquiv.injective

theorem homotopic_addRight_id (c : EuclideanSpace ℝ (Fin 3)) :
    (Homeomorph.addRight c : C(EuclideanSpace ℝ (Fin 3), EuclideanSpace ℝ (Fin 3))).Homotopic
      (ContinuousMap.id _) := by
  let F : C(I × EuclideanSpace ℝ (Fin 3), EuclideanSpace ℝ (Fin 3)) :=
    ⟨fun p => (p.2 : EuclideanSpace ℝ (Fin 3)) + (1 - (p.1 : ℝ)) • c, by fun_prop⟩
  exact ⟨{ toContinuousMap := F
           map_zero_left := fun x => by simp [F]
           map_one_left := fun x => by simp [F] }⟩

theorem mapsTo_addRight_compl (a c : EuclideanSpace ℝ (Fin 3)) :
    MapsTo (Homeomorph.addRight c : C(EuclideanSpace ℝ (Fin 3), EuclideanSpace ℝ (Fin 3)))
      ({a}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) ({(a + c)}ᶜ) :=
  fun _ hz h => hz (add_right_cancel h)

theorem integralRelativeHomologyMap_addRight_absoluteToRelative
    (n : ℕ) (a c : EuclideanSpace ℝ (Fin 3))
    (w : integralSingularHomology n (EuclideanSpace ℝ (Fin 3))) :
    integralRelativeHomologyMap n
        (Homeomorph.addRight c : C(EuclideanSpace ℝ (Fin 3), EuclideanSpace ℝ (Fin 3)))
        (mapsTo_addRight_compl a c)
        (integralAbsoluteToRelative n ({a}ᶜ) w) =
      integralAbsoluteToRelative n ({(a + c)}ᶜ) w :=
  integralRelativeHomologyMap_absoluteToRelative_eq_of_homotopic_id n _ _
    (homotopic_addRight_id c) w

end DifferentialGeometry.Topology
