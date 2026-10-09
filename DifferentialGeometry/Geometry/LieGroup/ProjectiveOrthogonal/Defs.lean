/-
Released under Apache 2.0 license as described in the file LICENSE.
Definitions from leanprover/lean-eval at commit 4ae7061fe4b0b70dcb7fe24fdee067b68636226b.
-/
import Mathlib.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Instances.Matrix

namespace DifferentialGeometry.ProjectiveOrthogonalGroup

universe u

variable (p q : Type u) (α : Type*)

def MatrixSum : Type _ := Matrix (p ⊕ q) (p ⊕ q) α

variable [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] [Ring α]

instance : Ring (MatrixSum p q α) := inferInstanceAs (Ring (Matrix ..))

variable {p q α} in
def MatrixSum.ofMatrix : Matrix (p ⊕ q) (p ⊕ q) α ≃+* MatrixSum p q α := .refl _

variable {p q α} in
def pmOneMat : Matrix (p ⊕ q) (p ⊕ q) α := .fromBlocks 1 0 0 (-1)

theorem pmOneMat_mul_pmOneMat : pmOneMat * pmOneMat = (1 : Matrix (p ⊕ q) _ α) := by
  simp [pmOneMat, Matrix.fromBlocks_multiply]

open MatrixSum Matrix

section Star

variable [StarRing α]

omit [Fintype p] [Fintype q] in
@[simp] theorem conjTranspose_pmOneMat : (pmOneMat : Matrix (p ⊕ q) _ α)ᴴ = pmOneMat := by
  simp_rw [pmOneMat, conjTranspose, fromBlocks_transpose, fromBlocks_map]
  simp [Matrix.map_neg]

instance : StarRing (MatrixSum p q α) where
  star A := .ofMatrix (pmOneMat * (ofMatrix.symm A).conjTranspose * pmOneMat)
  star_involutive A := by
    simp [← mul_assoc pmOneMat, mul_assoc (ofMatrix.symm A), pmOneMat_mul_pmOneMat]
  star_mul A B := by
    conv_lhs => rw [map_mul _ A, conjTranspose_mul, ← mul_one _ᴴ, ← pmOneMat_mul_pmOneMat]
    simp [mul_assoc]
  star_add A B := by simp [add_mul, mul_add]

end Star

section Topology

variable [TopologicalSpace α]

instance : TopologicalSpace (MatrixSum p q α) := inferInstanceAs (TopologicalSpace (Matrix ..))

instance [T1Space α] : T1Space (MatrixSum p q α) := inferInstanceAs (T1Space (_ → _))

omit [Fintype p] [Fintype q] in
instance [Finite p] [Finite q] [LocallyCompactSpace α] : LocallyCompactSpace (MatrixSum p q α) := by
  let _ := Fintype.ofFinite p
  let _ := Fintype.ofFinite q
  exact inferInstanceAs (LocallyCompactSpace (_ → _))

@[fun_prop] theorem MatrixSum.continuous_ofMatrix : Continuous (@ofMatrix p q α _ _ _ _ _) :=
  continuous_id

@[fun_prop] theorem MatrixSum.continuous_ofMatrix_symm : Continuous (@ofMatrix p q α ..).symm :=
  continuous_id

variable [IsTopologicalRing α]

instance : IsTopologicalRing (MatrixSum p q α) :=
  inferInstanceAs (IsTopologicalRing (Matrix ..))

variable [StarRing α] [ContinuousStar α]

instance : ContinuousStar (MatrixSum p q α) where
  continuous_star := by rw [star]; fun_prop

theorem MatrixSum.isClosed_unitary [T1Space α] :
    IsClosed (SetLike.coe <| unitary (MatrixSum p q α)) :=
  .inter (isClosed_singleton.preimage <| by fun_prop) (isClosed_singleton.preimage <| by fun_prop)

instance [T1Space α] [LocallyCompactSpace α] :
    LocallyCompactSpace (unitary (MatrixSum p q α)) :=
  (MatrixSum.isClosed_unitary ..).isClosedEmbedding_subtypeVal.locallyCompactSpace

instance : IsTopologicalGroup (unitary (MatrixSum p q α)) where
  continuous_inv := by simp_rw [Inv.inv, star]; fun_prop

end Topology

variable (p q : ℕ)

@[reducible]
def PO := unitary (MatrixSum (Fin p) (Fin q) ℝ) ⧸ Subgroup.center _

instance : MeasurableSpace (PO p q) := borel _
instance : BorelSpace (PO p q) := ⟨rfl⟩

open MeasureTheory

noncomputable instance : MeasureSpace (PO p q) := ⟨.haar⟩

end DifferentialGeometry.ProjectiveOrthogonalGroup
