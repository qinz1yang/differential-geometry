import DifferentialGeometry.Topology.Homology.RelativeFunctoriality
import DifferentialGeometry.Topology.Homology.LocalHomology



noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

set_option backward.isDefEq.respectTransparency false in


def integralRelativeChainHomeomorphIso (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (he : MapsTo e A B) (he' : MapsTo e.symm B A) :
    integralRelativeChains A ≅ integralRelativeChains B where
  hom := integralRelativeChainMap ⟨e, e.continuous⟩ he
  inv := integralRelativeChainMap ⟨e.symm, e.symm.continuous⟩ he'
  hom_inv_id := by
    rw [← integralRelativeChainMap_comp]
    have h : (⟨e.symm, e.symm.continuous⟩ : C(Y, X)).comp ⟨e, e.continuous⟩ = ContinuousMap.id X := by
      ext x
      exact e.symm_apply_apply x
    exact integralRelativeChainMap_eq_id _ _ _ h
  inv_hom_id := by
    rw [← integralRelativeChainMap_comp]
    have h : (⟨e, e.continuous⟩ : C(X, Y)).comp ⟨e.symm, e.symm.continuous⟩ = ContinuousMap.id Y := by
      ext y
      exact e.apply_symm_apply y
    exact integralRelativeChainMap_eq_id _ _ _ h



def integralRelativeHomologyHomeomorphIso (n : ℕ) (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (he : MapsTo e A B) (he' : MapsTo e.symm B A) :
    integralRelativeHomology n A ≅ integralRelativeHomology n B :=
  HomologicalComplex.homologyMapIso (integralRelativeChainHomeomorphIso e A B he he') n


theorem integralRelativeHomologyHomeomorphIso_hom (n : ℕ) (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (he : MapsTo e A B) (he' : MapsTo e.symm B A) :
    (integralRelativeHomologyHomeomorphIso n e A B he he').hom.hom =
      integralRelativeHomologyMap n ⟨e, e.continuous⟩ he := rfl



def integralLocalHomologyHomeomorphIso (n : ℕ) (e : X ≃ₜ Y) (x : X) :
    integralLocalHomology n x ≅ integralLocalHomology n (e x) :=
  integralRelativeHomologyHomeomorphIso n e {x}ᶜ {e x}ᶜ
    (fun _ hy => e.injective.ne hy)
    (fun y hy => by
      change e.symm y ≠ x
      intro h
      apply hy
      exact (e.apply_symm_apply y).symm.trans (congrArg e h))

end DifferentialGeometry.Topology
