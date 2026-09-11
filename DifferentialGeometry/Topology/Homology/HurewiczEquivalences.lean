import DifferentialGeometry.Topology.Homology.HurewiczLowDegrees







noncomputable section

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]



def hurewiczTwoMulEquiv (x : X)
    (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    HomotopyGroup (Fin 2) X x ≃* Multiplicative (integralSingularHomology 2 X) :=
  MulEquiv.ofBijective
    ({ toFun := fun a => Multiplicative.ofAdd (sphereHurewicz 1 x c a)
       map_one' := sphereHurewicz_one 1 x c
       map_mul' := (hurewicz_two_isomorphism x c hc).2 } :
      HomotopyGroup (Fin 2) X x →* Multiplicative (integralSingularHomology 2 X))
    (hurewicz_two_isomorphism x c hc).1


theorem hurewiczTwoMulEquiv_apply (x : X)
    (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) (a : HomotopyGroup (Fin 2) X x) :
    (hurewiczTwoMulEquiv x c hc a).toAdd = sphereHurewicz 1 x c a := rfl



def hurewiczThreeMulEquiv (x : X)
    (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) X x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    HomotopyGroup (Fin 3) X x ≃* Multiplicative (integralSingularHomology 3 X) :=
  MulEquiv.ofBijective
    ({ toFun := fun a => Multiplicative.ofAdd (sphereHurewicz 2 x c a)
       map_one' := sphereHurewicz_one 2 x c
       map_mul' := (hurewicz_three_isomorphism x hπ₂ c hc).2 } :
      HomotopyGroup (Fin 3) X x →* Multiplicative (integralSingularHomology 3 X))
    (hurewicz_three_isomorphism x hπ₂ c hc).1


theorem hurewiczThreeMulEquiv_apply (x : X)
    (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) X x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) (a : HomotopyGroup (Fin 3) X x) :
    (hurewiczThreeMulEquiv x hπ₂ c hc a).toAdd = sphereHurewicz 2 x c a := rfl




theorem homotopyTwo_subsingleton_of_homologyTwo
    [Subsingleton (integralSingularHomology 2 X)] (x : X) :
    Subsingleton (HomotopyGroup (Fin 2) X x) := by
  have h := (hurewicz_two_isomorphism x (integralLiftedSphereGenerator 1)
    (integralLiftedSphereGenerator_isGenerator 1)).1.1
  exact ⟨fun a b => h (Subsingleton.elim _ _)⟩

end DifferentialGeometry.Topology
