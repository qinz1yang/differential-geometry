import Mathlib
import DifferentialGeometry.Analysis.Convex.ProperConeFace
import DifferentialGeometry.Analysis.InnerProductSpace.ProperConeFace
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.InnerProductSpace
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DifferentialGeometry.Analysis.Convex
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev MatrixData (ι : Type*) := EuclideanSpace ℝ (ι × ι)

def matEvalCLM (x : EuclideanSpace ℝ ι) : MatrixData ι →L[ℝ] ℝ :=
{ toFun := fun A => ∑ i, x i * (∑ j, A (i, j) * x j)
  map_add' := by
    intro A B
    change (∑ i, x i * (∑ j, (A (i, j) + B (i, j)) * x j)) =
      (∑ i, x i * (∑ j, A (i, j) * x j)) + (∑ i, x i * (∑ j, B (i, j) * x j))
    simp [Finset.sum_add_distrib, mul_add, add_mul]
  map_smul' := by
    intro c A
    change (∑ i, x i * (∑ j, (c * A (i, j)) * x j)) =
      c * (∑ i, x i * (∑ j, A (i, j) * x j))
    simp [Finset.mul_sum, mul_left_comm, mul_comm]
  cont := by
    fun_prop }

def matSymEvalCLM (i j : ι) : MatrixData ι →L[ℝ] ℝ :=
{ toFun := fun A => A (i, j) - A (j, i)
  map_add' := by intro A B; simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  map_smul' := by
    intro c A
    change c * A (i, j) - c * A (j, i) = c * (A (i, j) - A (j, i))
    ring
  cont := by fun_prop }

def matSymmetricCone : ProperCone ℝ (MatrixData ι) :=
  ⨅ i : ι, ⨅ j : ι, (⊥ : ProperCone ℝ ℝ).comap (matSymEvalCLM i j)

def matQuadraticNonnegativeCone : ProperCone ℝ (MatrixData ι) :=
  ⨅ x : EuclideanSpace ℝ ι, (ProperCone.positive ℝ ℝ).comap (matEvalCLM x)

def matPositiveSemidefiniteCone : ProperCone ℝ (MatrixData ι) :=
  matSymmetricCone ⊓ matQuadraticNonnegativeCone

omit [DecidableEq ι] in
theorem matPositiveSemidefinite_symm {A : MatrixData ι}
    (hA : A ∈ matPositiveSemidefiniteCone) (i j : ι) :
    A (i, j) = A (j, i) := by
  have hsym : A ∈ matSymmetricCone :=
    (inf_le_left : matPositiveSemidefiniteCone ≤ matSymmetricCone) hA
  have hle : matSymmetricCone ≤
      (⊥ : ProperCone ℝ ℝ).comap (matSymEvalCLM i j) := by
    exact le_trans
      (iInf_le (fun k : ι => ⨅ l : ι, (⊥ : ProperCone ℝ ℝ).comap (matSymEvalCLM k l)) i)
      (iInf_le (fun l : ι => (⊥ : ProperCone ℝ ℝ).comap (matSymEvalCLM i l)) j)
  have hzero : matSymEvalCLM i j A = 0 := by
    exact hle hsym
  have hzero' : A (i, j) - A (j, i) = 0 := by
    simpa [matSymEvalCLM] using hzero
  linarith

omit [DecidableEq ι] in
theorem matPositiveSemidefinite_eval_nonneg {A : MatrixData ι}
    (hA : A ∈ matPositiveSemidefiniteCone) (x : EuclideanSpace ℝ ι) :
    0 ≤ ∑ i, x i * (∑ j, A (i, j) * x j) := by
  have hquad : A ∈ matQuadraticNonnegativeCone :=
    (inf_le_right : matPositiveSemidefiniteCone ≤ matQuadraticNonnegativeCone) hA
  have hle : matQuadraticNonnegativeCone ≤
      (ProperCone.positive ℝ ℝ).comap (matEvalCLM x) :=
    iInf_le (fun y : EuclideanSpace ℝ ι => (ProperCone.positive ℝ ℝ).comap (matEvalCLM y)) x
  exact hle hquad

omit [DecidableEq ι] in
theorem matPositiveSemidefiniteCone_nonempty :
    (matPositiveSemidefiniteCone (ι := ι) : Set (MatrixData ι)).Nonempty :=
  matPositiveSemidefiniteCone.nonempty

omit [DecidableEq ι] in
theorem matPositiveSemidefiniteCone_isClosed :
    IsClosed (matPositiveSemidefiniteCone (ι := ι) : Set (MatrixData ι)) :=
  matPositiveSemidefiniteCone.isClosed

omit [DecidableEq ι] in
theorem matPositiveSemidefiniteCone_convex :
    Convex ℝ (matPositiveSemidefiniteCone (ι := ι) : Set (MatrixData ι)) :=
  matPositiveSemidefiniteCone.convex

end DifferentialGeometry.Analysis.Convex
