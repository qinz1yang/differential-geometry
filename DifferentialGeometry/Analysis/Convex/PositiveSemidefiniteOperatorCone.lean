import DifferentialGeometry.Analysis.Convex.ProperConeFace
import DifferentialGeometry.Analysis.InnerProductSpace.ProperConeFace
open DifferentialGeometry.Analysis.Convex
open DifferentialGeometry.Analysis.InnerProductSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace DifferentialGeometry.Analysis.Convex

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable [FiniteDimensional ℝ F]

def opEvalCLM (v w : F) : (F →L[ℝ] F) →L[ℝ] ℝ :=
  ((innerSL ℝ) w).comp ((ContinuousLinearMap.apply ℝ F) v)

omit [CompleteSpace F] [FiniteDimensional ℝ F] in
@[simp]
theorem opEvalCLM_apply (v w : F) (A : F →L[ℝ] F) :
    opEvalCLM v w A = inner ℝ w (A v) := by
  unfold opEvalCLM
  simp [ContinuousLinearMap.comp_apply]

def opSymEvalCLM (v w : F) : (F →L[ℝ] F) →L[ℝ] ℝ :=
  opEvalCLM v w - opEvalCLM w v

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (basis : Module.Basis ι ℝ F)

def opSymmetricCone : ProperCone ℝ (F →L[ℝ] F) :=
  ⨅ i : ι, ⨅ j : ι,
    (⊥ : ProperCone ℝ ℝ).comap (opSymEvalCLM (basis i) (basis j))

def opQuadraticNonnegativeCone : ProperCone ℝ (F →L[ℝ] F) :=
  ⨅ v : F, (ProperCone.positive ℝ ℝ).comap (opEvalCLM v v)

def opPositiveSemidefiniteCone : ProperCone ℝ (F →L[ℝ] F) :=
  opSymmetricCone basis ⊓ opQuadraticNonnegativeCone

omit [CompleteSpace F] [FiniteDimensional ℝ F] [Fintype ι] [DecidableEq ι] in
theorem opPositiveSemidefinite_symm_basis
    {A : F →L[ℝ] F} (hA : A ∈ opPositiveSemidefiniteCone basis) (i j : ι) :
    inner ℝ (basis j) (A (basis i)) = inner ℝ (basis i) (A (basis j)) := by
  have hsym : A ∈ opSymmetricCone basis :=
    (inf_le_left : opPositiveSemidefiniteCone basis ≤ opSymmetricCone basis) hA
  have hj : opSymmetricCone basis ≤
      (⊥ : ProperCone ℝ ℝ).comap (opSymEvalCLM (basis i) (basis j)) := by
    exact le_trans (iInf_le (fun k : ι => ⨅ l : ι,
      (⊥ : ProperCone ℝ ℝ).comap (opSymEvalCLM (basis k) (basis l))) i)
      (iInf_le (fun l : ι =>
        (⊥ : ProperCone ℝ ℝ).comap (opSymEvalCLM (basis i) (basis l))) j)
  have hzero : opSymEvalCLM (basis i) (basis j) A = 0 := by
    have hm := hj hsym
    simpa using hm
  simpa [opSymEvalCLM, opEvalCLM_apply, sub_eq_zero] using hzero

omit [CompleteSpace F] [FiniteDimensional ℝ F] [Fintype ι] [DecidableEq ι] in
theorem opPositiveSemidefinite_eval_nonneg
    {A : F →L[ℝ] F} (hA : A ∈ opPositiveSemidefiniteCone basis) (v : F) :
    0 ≤ inner ℝ v (A v) := by
  have hquad : A ∈ opQuadraticNonnegativeCone :=
    (inf_le_right : opPositiveSemidefiniteCone basis ≤ opQuadraticNonnegativeCone) hA
  have hle : opQuadraticNonnegativeCone ≤
      (ProperCone.positive ℝ ℝ).comap (opEvalCLM v v) :=
    iInf_le (fun w : F => (ProperCone.positive ℝ ℝ).comap (opEvalCLM w w)) v
  exact hle hquad

omit [CompleteSpace F] [FiniteDimensional ℝ F] [Fintype ι] [DecidableEq ι] in
theorem opPositiveSemidefiniteCone_nonempty :
    (opPositiveSemidefiniteCone basis : Set (F →L[ℝ] F)).Nonempty :=
  (opPositiveSemidefiniteCone basis).nonempty

omit [CompleteSpace F] [FiniteDimensional ℝ F] [Fintype ι] [DecidableEq ι] in
theorem opPositiveSemidefiniteCone_isClosed :
    IsClosed (opPositiveSemidefiniteCone basis : Set (F →L[ℝ] F)) :=
  (opPositiveSemidefiniteCone basis).isClosed

omit [CompleteSpace F] [FiniteDimensional ℝ F] [Fintype ι] [DecidableEq ι] in
theorem opPositiveSemidefiniteCone_convex :
    Convex ℝ (opPositiveSemidefiniteCone basis : Set (F →L[ℝ] F)) :=
  (opPositiveSemidefiniteCone basis).convex

end DifferentialGeometry.Analysis.Convex
