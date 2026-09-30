import Mathlib.Topology.Homotopy.Basic

noncomputable section

namespace DifferentialGeometry.Topology

def freeHomotopySetoid (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :
    Setoid C(X, Y) := ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩


def FreeHomotopyClass (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :=
  Quotient (freeHomotopySetoid X Y)







namespace FreeHomotopyClass

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]


def mk (f : C(X, Y)) : FreeHomotopyClass X Y := Quotient.mk _ f

theorem mk_eq_mk_iff (f g : C(X, Y)) : mk f = mk g ↔ ContinuousMap.Homotopic f g :=
  Quotient.eq


def map (f : C(Y, Z)) : FreeHomotopyClass X Y → FreeHomotopyClass X Z :=
  Quotient.map (fun g => f.comp g)
    (fun _ _ h => (ContinuousMap.Homotopic.refl f).comp h)

@[simp] theorem map_mk (f : C(Y, Z)) (g : C(X, Y)) : map f (mk g) = mk (f.comp g) := rfl

@[simp] theorem map_id (ξ : FreeHomotopyClass X Y) : map (ContinuousMap.id Y) ξ = ξ := by
  induction ξ using Quotient.inductionOn with
  | h f => rfl

@[simp] theorem map_comp {W : Type*} [TopologicalSpace W]
    (f : C(Y, Z)) (g : C(Z, W)) (ξ : FreeHomotopyClass X Y) :
    map (g.comp f) ξ = map g (map f ξ) := by
  induction ξ using Quotient.inductionOn with
  | h h => rfl

end FreeHomotopyClass

end DifferentialGeometry.Topology
