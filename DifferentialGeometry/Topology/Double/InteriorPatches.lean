import DifferentialGeometry.Topology.Double.Reflection
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false
noncomputable section
open Set Function Topology
namespace DifferentialGeometry.Topology
variable {X : Type*} [TopologicalSpace X]
  (B : Set X) (r : C(X, ℝ)) (hr : ∀ b : B, r b.val = 0) (hn : ∀ x, 0 ≤ r x)


def doublePositivePatch : OpenPartialHomeomorph X (Double B) where
  toFun := doublePositive B
  invFun := doubleFold B
  source := {x | 0 < r x}
  target := {z | 0 < doubleHeight B r hr z}
  map_source' _ hx := hx
  map_target' z hz := by
    rcases double_cases B z with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · exact hz
    · change 0 < -r x at hz
      exact (not_lt_of_ge (neg_nonpos.mpr (hn x)) hz).elim
  left_inv' _ _ := rfl
  right_inv' z hz := by
    rcases double_cases B z with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · rfl
    · change 0 < -r x at hz
      exact (not_lt_of_ge (neg_nonpos.mpr (hn x)) hz).elim
  open_source := isOpen_lt continuous_const r.continuous
  open_target := isOpen_lt continuous_const (doubleHeight B r hr).continuous
  continuousOn_toFun := (doublePositive B).continuous.continuousOn
  continuousOn_invFun := (doubleFold B).continuous.continuousOn


def doubleNegativePatch : OpenPartialHomeomorph X (Double B) where
  toFun := doubleNegative B
  invFun := doubleFold B
  source := {x | 0 < r x}
  target := {z | doubleHeight B r hr z < 0}
  map_source' x hx := by
    change -r x < 0
    exact neg_neg_of_pos hx
  map_target' z hz := by
    rcases double_cases B z with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · exact (not_lt_of_ge (hn x) hz).elim
    · change -r x < 0 at hz
      exact neg_neg_iff_pos.mp hz
  left_inv' _ _ := rfl
  right_inv' z hz := by
    rcases double_cases B z with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · exact (not_lt_of_ge (hn x) hz).elim
    · rfl
  open_source := isOpen_lt continuous_const r.continuous
  open_target := isOpen_lt (doubleHeight B r hr).continuous continuous_const
  continuousOn_toFun := (doubleNegative B).continuous.continuousOn
  continuousOn_invFun := (doubleFold B).continuous.continuousOn

@[simp] theorem doublePositivePatch_apply (x : X) :
    doublePositivePatch B r hr hn x = doublePositive B x := rfl

@[simp] theorem doubleNegativePatch_apply (x : X) :
    doubleNegativePatch B r hr hn x = doubleNegative B x := rfl

@[simp] theorem doublePositivePatch_symm_apply (z : Double B) :
    (doublePositivePatch B r hr hn).symm z = doubleFold B z := rfl

@[simp] theorem doubleNegativePatch_symm_apply (z : Double B) :
    (doubleNegativePatch B r hr hn).symm z = doubleFold B z := rfl

end DifferentialGeometry.Topology
