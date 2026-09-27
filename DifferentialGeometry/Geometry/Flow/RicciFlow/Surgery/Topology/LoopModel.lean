import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Homotopy.Basic

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


abbrev Circle := AddCircle (1 : ℝ)


abbrev Sphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1


abbrev ContinuousFreeLoop (Q : Type*) [TopologicalSpace Q] := C(Circle, Q)


abbrev SphereFamily (Q : Type*) [TopologicalSpace Q] := C(Sphere 2, ContinuousFreeLoop Q)

variable {P Q R : Type*} [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace R]


def loopEvaluation : C(ContinuousFreeLoop Q, Q) :=
  ⟨fun γ => γ 0, continuous_eval_const 0⟩


def constantLoops : C(Q, ContinuousFreeLoop Q) := ContinuousMap.const'

@[simp] theorem loopEvaluation_constantLoops (q : Q) :
    loopEvaluation (constantLoops q) = q := rfl


abbrev BasedContinuousLoop (q : Q) := {γ : ContinuousFreeLoop Q // γ 0 = q}


def basedConstantLoop (q : Q) : BasedContinuousLoop q := ⟨constantLoops q, rfl⟩


def basedLoopInclusion (q : Q) : C(BasedContinuousLoop q, ContinuousFreeLoop Q) :=
  ⟨Subtype.val, continuous_subtype_val⟩


def loopPostcompose (f : C(P, Q)) : C(ContinuousFreeLoop P, ContinuousFreeLoop Q) :=
  ⟨fun γ => f.comp γ, ContinuousMap.continuous_postcomp f⟩

@[simp] theorem loopPostcompose_apply (f : C(P, Q)) (γ : ContinuousFreeLoop P)
    (z : Circle) : loopPostcompose f γ z = f (γ z) := rfl

@[simp] theorem loopPostcompose_constantLoops (f : C(P, Q)) (p : P) :
    loopPostcompose f (constantLoops p) = constantLoops (f p) := rfl

@[simp] theorem loopPostcompose_id :
    loopPostcompose (ContinuousMap.id Q) = ContinuousMap.id (ContinuousFreeLoop Q) := rfl

@[simp] theorem loopPostcompose_comp (f : C(P, Q)) (g : C(Q, R)) :
    loopPostcompose (g.comp f) = (loopPostcompose g).comp (loopPostcompose f) := rfl


def IsContractibleLoop (γ : ContinuousFreeLoop Q) : Prop :=
  ∃ q : Q, ContinuousMap.Homotopic γ (constantLoops q)


abbrev ContractibleContinuousLoop (Q : Type*) [TopologicalSpace Q] :=
  {γ : ContinuousFreeLoop Q // IsContractibleLoop γ}


abbrev ContractibleSphereFamily (Q : Type*) [TopologicalSpace Q] :=
  C(Sphere 2, ContractibleContinuousLoop Q)

theorem isContractibleLoop_constant (q : Q) : IsContractibleLoop (constantLoops q) :=
  ⟨q, ContinuousMap.Homotopic.refl _⟩

theorem IsContractibleLoop.postcompose {γ : ContinuousFreeLoop P}
    (hγ : IsContractibleLoop γ) (f : C(P, Q)) :
    IsContractibleLoop (loopPostcompose f γ) := by
  obtain ⟨p, hp⟩ := hγ
  exact ⟨f p, (ContinuousMap.Homotopic.refl f).comp hp⟩


def contractibleLoopPostcompose (f : C(P, Q)) :
    C(ContractibleContinuousLoop P, ContractibleContinuousLoop Q) :=
  ⟨fun γ => ⟨loopPostcompose f γ.1, γ.2.postcompose f⟩,
    ((loopPostcompose f).continuous.comp continuous_subtype_val).subtype_mk _⟩


def freeHomotopySetoid (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :
    Setoid C(X, Y) := ⟨ContinuousMap.Homotopic, ContinuousMap.Homotopic.equivalence⟩


def FreeHomotopyClass (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :=
  Quotient (freeHomotopySetoid X Y)


abbrev FreeSphereClass (Q : Type*) [TopologicalSpace Q] :=
  FreeHomotopyClass (Sphere 2) (ContinuousFreeLoop Q)


abbrev FreeContractibleSphereClass (Q : Type*) [TopologicalSpace Q] :=
  FreeHomotopyClass (Sphere 2) (ContractibleContinuousLoop Q)

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


def sphereFamilyUncurry (Γ : SphereFamily Q) : C(Sphere 2 × Circle, Q) := Γ.uncurry

@[simp] theorem sphereFamilyUncurry_apply (Γ : SphereFamily Q) (p : Sphere 2) (z : Circle) :
    sphereFamilyUncurry Γ (p, z) = Γ p z := rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


abbrev ThreeSpace := EuclideanSpace ℝ (Fin 3)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
