import DifferentialGeometry.Topology.Double.ClosedCover

set_option autoImplicit false
noncomputable section
open Set Function Topology
namespace DifferentialGeometry.Topology
variable {X : Type*} [TopologicalSpace X]


def doubleReflect (B : Set X) : C(Double B, Double B) :=
  doubleDesc B (doubleNegative B) (doublePositive B) (fun b => (double_seam B b).symm)

@[simp] theorem doubleReflect_positive (B : Set X) (x : X) :
    doubleReflect B (doublePositive B x) = doubleNegative B x := rfl

@[simp] theorem doubleReflect_negative (B : Set X) (x : X) :
    doubleReflect B (doubleNegative B x) = doublePositive B x := rfl


theorem doubleReflect_involutive (B : Set X) : Involutive (doubleReflect B) := by
  intro z
  rcases double_cases B z with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;> rfl


def doubleReflection (B : Set X) : Double B ≃ₜ Double B where
  toFun := doubleReflect B
  invFun := doubleReflect B
  left_inv := doubleReflect_involutive B
  right_inv := doubleReflect_involutive B
  continuous_toFun := (doubleReflect B).continuous
  continuous_invFun := (doubleReflect B).continuous


theorem doubleHeight_reflection (B : Set X) (r : C(X, ℝ))
    (hr : ∀ b : B, r b.val = 0) (z : Double B) :
    doubleHeight B r hr (doubleReflection B z) = -doubleHeight B r hr z := by
  rcases double_cases B z with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rfl
  · exact (neg_neg (r x)).symm

end DifferentialGeometry.Topology
