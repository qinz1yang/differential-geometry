import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Data.Sign.Basic

set_option autoImplicit false
noncomputable section
open InnerProductSpace
open scoped BigOperators
namespace DifferentialGeometry.QuadraticForm
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


def operatorForm (T : E →ₗ[ℝ] E) : QuadraticForm ℝ E :=
  LinearMap.BilinMap.toQuadraticMap ((innerₗ E).comp T)


theorem operatorForm_apply (T : E →ₗ[ℝ] E) (x : E) :
    operatorForm T x = inner ℝ (T x) x := rfl


theorem associated_operatorForm {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) :
    QuadraticMap.associated (operatorForm T) = (innerₗ E).comp T := by
  apply QuadraticMap.associated_left_inverse ℝ
  intro x y
  change inner ℝ (T x) y = inner ℝ (T y) x
  rw [hT x y, real_inner_comm]

variable [FiniteDimensional ℝ E]


theorem operatorForm_separatingLeft_iff {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) :
    (QuadraticMap.associated (operatorForm T)).SeparatingLeft ↔ T.det ≠ 0 := by
  rw [associated_operatorForm hT, ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not,
    LinearMap.ker_eq_bot']
  constructor
  · intro h x hx
    apply h x
    intro y
    change inner ℝ (T x) y = 0
    rw [hx, inner_zero_left]
  · intro h x hx
    apply h x
    exact (inner_self_eq_zero (𝕜 := ℝ)).mp (hx (T x))


theorem operatorForm_equivalent_eigenvalues {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) :
    QuadraticMap.Equivalent (operatorForm T)
      (QuadraticMap.weightedSumSquares ℝ (hT.eigenvalues rfl)) := by
  refine ⟨{ (hT.eigenvectorBasis rfl).toBasis.equivFun with map_app' := ?_ }⟩
  intro x
  rw [operatorForm_apply, ← (hT.eigenvectorBasis rfl).repr.inner_map_map]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp only [QuadraticMap.weightedSumSquares_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [OrthonormalBasis.coe_toBasis_repr]
  rw [hT.eigenvectorBasis_apply_self_apply]
  change hT.eigenvalues rfl i * (((hT.eigenvectorBasis rfl).repr x) i *
    ((hT.eigenvectorBasis rfl).repr x) i) =
    ((hT.eigenvectorBasis rfl).repr x) i *
      (hT.eigenvalues rfl i * ((hT.eigenvectorBasis rfl).repr x) i)
  ring


theorem operatorForm_sigNeg {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) :
    _root_.sigNeg (operatorForm T) = {i | hT.eigenvalues rfl i < 0}.ncard :=
  QuadraticForm.sigNeg_of_equiv_weightedSumSquares
    (operatorForm_equivalent_eigenvalues hT)

private theorem sign_prod {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, w i ≠ 0) :
    (SignType.sign (∏ i ∈ s, w i) : ℤ) = (-1 : ℤ) ^ (s.filter (fun i => w i < 0)).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, _root_.sign_mul, SignType.coe_mul]
    have haw := hw a (Finset.mem_insert_self _ _)
    have hsw : ∀ i ∈ s, w i ≠ 0 := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    rw [ih hsw]
    by_cases hn : w a < 0
    · simp [hn, Finset.filter_insert, ha, pow_succ, mul_comm]
    · have hp : 0 < w a := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm haw)
      simp [hp, hn, Finset.filter_insert]


theorem sign_det_eq_neg_one_pow_sigNeg {T : E →ₗ[ℝ] E}
    (hT : T.IsSymmetric) (hdet : LinearMap.det T ≠ 0) :
    (SignType.sign (LinearMap.det T) : ℤ) = (-1 : ℤ) ^ sigNeg (operatorForm T) := by
  classical
  rw [operatorForm_sigNeg hT, hT.det_eq_prod_eigenvalues rfl]
  have hw : ∀ i ∈ Finset.univ, hT.eigenvalues rfl i ≠ 0 := by
    simpa only [hT.det_eq_prod_eigenvalues rfl, RCLike.ofReal_real_eq_id, id_eq,
      ne_eq, Finset.prod_eq_zero_iff, not_exists, not_and] using hdet
  simpa only [RCLike.ofReal_real_eq_id, id_eq, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
    using sign_prod Finset.univ (hT.eigenvalues rfl) hw

end DifferentialGeometry.QuadraticForm
