import DifferentialGeometry.Geometry.Curvature.AlgebraicForm
import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open scoped BigOperators TensorProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def curvatureBilinearSlice
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) (e f : E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ :=
  (T.curryMid 3 f).curryMid 1 e

private theorem curvatureBilinearSlice_apply
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) (e f : E) (v : Fin 2 → E) :
    curvatureBilinearSlice T e f v = T ![v 0, e, v 1, f] := by
  change T _ = T _
  congr 1
  ext i
  fin_cases i <;> rfl

def curvatureQuadraticContraction
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ :=
  -∑ i, ∑ j, (((curvatureBilinearSlice T (b i) (b j)).smulRight
    (curvatureBilinearSlice T (b i) (b j))).uncurrySum.domDomCongr finSumFinEquiv)

theorem curvatureQuadraticContraction_apply
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) (a c d e : E) :
    curvatureQuadraticContraction b T ![a, c, d, e] =
      -∑ i, ∑ j, T ![a, b i, c, b j] * T ![d, b i, e, b j] := by
  simp only [curvatureQuadraticContraction, neg_apply, sum_apply,
    ContinuousMultilinearMap.domDomCongr_apply, ContinuousMultilinearMap.uncurrySum_apply,
    ContinuousMultilinearMap.smulRight_apply, smul_apply, smul_eq_mul,
    curvatureBilinearSlice_apply]
  rfl

def curvatureQuadraticReaction
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ :=
  let B := curvatureQuadraticContraction b T
  (2 : ℝ) • (B - B.domDomCongr (Equiv.swap 2 3) +
    B.domDomCongr (Equiv.swap 1 2) -
    B.domDomCongr (Equiv.ofBijective ![0, 3, 1, 2] (by decide)))

theorem curvatureQuadraticReaction_apply
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) (a c d e : E) :
    curvatureQuadraticReaction b T ![a, c, d, e] =
      let B := fun a c d e => curvatureQuadraticContraction b T ![a, c, d, e]
      2 * (B a c d e - B a c e d + B a d c e - B a e c d) := by
  simp only [curvatureQuadraticReaction, smul_apply, smul_eq_mul, add_apply, sub_apply,
    ContinuousMultilinearMap.domDomCongr_apply]
  have h23 : (fun i : Fin 4 => ![a, c, d, e] (Equiv.swap 2 3 i)) = ![a, c, e, d] := by
    ext i
    fin_cases i <;> rfl
  have h12 : (fun i : Fin 4 => ![a, c, d, e] (Equiv.swap 1 2 i)) = ![a, d, c, e] := by
    ext i
    fin_cases i <;> rfl
  have hcycle : (fun i : Fin 4 => ![a, c, d, e] (![0, 3, 1, 2] i)) = ![a, e, c, d] := by
    ext i
    fin_cases i <;> rfl
  change 2 * (_ - _ + _ - (curvatureQuadraticContraction b T)
    (fun i => ![a, c, d, e] (![0, 3, 1, 2] i))) = _
  rw [h23, h12, hcycle]

theorem curvatureQuadraticReaction_isAlgCurvForm
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun a c d e => T ![a, c, d, e])) :
    IsAlgCurvForm (fun a c d e => curvatureQuadraticReaction b T ![a, c, d, e]) := by
  let B := fun a c d e => curvatureQuadraticContraction b T ![a, c, d, e]
  have hpair (a c d e : E) : B a c d e = B d e a c := by
    simp only [B, curvatureQuadraticContraction_apply]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hswap (a c d e : E) : B a c d e = B c a e d := by
    simp only [B, curvatureQuadraticContraction_apply]
    conv_rhs =>
      enter [1, 2, i, 2, j]
      rw [hT.pair_swap c, hT.pair_swap e]
    congr 1
    exact Finset.sum_comm
  have hP (a c d e : E) : curvatureQuadraticReaction b T ![a, c, d, e] =
      2 * (B a c d e - B a c e d + B a d c e - B a e c d) :=
    curvatureQuadraticReaction_apply b T a c d e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a a' c d e
    exact (curvatureQuadraticReaction b T).curryLeft.map_add a a' |> congrArg
      (fun f => f ![c, d, e])
  · intro r a c d e
    exact (curvatureQuadraticReaction b T).curryLeft.map_smul r a |> congrArg
      (fun f => f ![c, d, e])
  · intro a c d e
    simp only [hP]
    rw [hswap c a d e, hswap c a e d, hpair c d a e, hpair c e a d]
    ring
  · intro a c d e
    simp only [hP]
    ring
  · intro a c d e
    simp only [hP]
    rw [hpair c d a e, hswap c a d e, hpair c e d a, hswap d a e c,
      hswap d c a e, hpair d e a c]
    ring

private theorem sum_dual_mul_dual_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E)
    (f g : E →L[ℝ] ℝ) :
    ∑ i, f (b i) * g (b i) = ∑ j, f (c j) * g (c j) := by
  let _ := b.toBasis.finiteDimensional_of_finite
  let L : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := f.toLinearMap.smulRight g.toLinearMap
  have h := congrArg (TensorProduct.lift L)
    ((InnerProductSpace.canonicalCovariantTensor_eq_sum E b).symm.trans
      (InnerProductSpace.canonicalCovariantTensor_eq_sum E c))
  simpa [L, map_sum, TensorProduct.lift.tmul, smul_eq_mul] using h

theorem curvatureQuadraticContraction_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) :
    curvatureQuadraticContraction b T = curvatureQuadraticContraction c T := by
  ext v
  have hv : v = ![v 0, v 1, v 2, v 3] := by
    ext i
    fin_cases i <;> rfl
  rw [hv, curvatureQuadraticContraction_apply, curvatureQuadraticContraction_apply]
  congr 1
  have heval3 (a c d y : E) : (T.toContinuousLinearMap ![a, c, d, 0] 3) y =
      T ![a, c, d, y] := by
    change T (Function.update ![a, c, d, 0] 3 y) = _
    congr 1
    ext i
    fin_cases i <;> rfl
  have heval1 (a c d y : E) : (T.toContinuousLinearMap ![a, 0, c, d] 1) y =
      T ![a, y, c, d] := by
    change T (Function.update ![a, 0, c, d] 1 y) = _
    congr 1
    ext i
    fin_cases i <;> rfl
  have hlast (i : ι) :
      ∑ j, T ![v 0, b i, v 1, b j] * T ![v 2, b i, v 3, b j] =
        ∑ j, T ![v 0, b i, v 1, c j] * T ![v 2, b i, v 3, c j] := by
    simpa only [heval3] using sum_dual_mul_dual_eq b c
      (T.toContinuousLinearMap ![v 0, b i, v 1, 0] 3)
      (T.toContinuousLinearMap ![v 2, b i, v 3, 0] 3)
  simp_rw [hlast]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [heval1] using sum_dual_mul_dual_eq b c
    (T.toContinuousLinearMap ![v 0, 0, v 1, c j] 1)
    (T.toContinuousLinearMap ![v 2, 0, v 3, c j] 1)

theorem curvatureQuadraticReaction_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) :
    curvatureQuadraticReaction b T = curvatureQuadraticReaction c T := by
  simp only [curvatureQuadraticReaction, curvatureQuadraticContraction_eq b c]

variable [FiniteDimensional ℝ E]

def curvatureQuadraticReactionTensor
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ :=
  curvatureQuadraticReaction (stdOrthonormalBasis ℝ E) T

theorem curvatureQuadraticReactionTensor_isAlgCurvForm
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun a c d e => T ![a, c, d, e])) :
    IsAlgCurvForm (fun a c d e => curvatureQuadraticReactionTensor T ![a, c, d, e]) :=
  curvatureQuadraticReaction_isAlgCurvForm (stdOrthonormalBasis ℝ E) T hT

theorem curvatureQuadraticReactionTensor_eq_of_orthonormalBasis
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) :
    curvatureQuadraticReactionTensor T = curvatureQuadraticReaction b T :=
  curvatureQuadraticReaction_eq (stdOrthonormalBasis ℝ E) b T

theorem curvatureQuadraticReactionTensor_apply_orthonormalBasis
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ) (a c d e : E) :
    curvatureQuadraticReactionTensor T ![a, c, d, e] =
      let B := fun a c d e : E => -∑ i, ∑ j, T ![a, b i, c, b j] * T ![d, b i, e, b j]
      2 * (B a c d e - B a c e d + B a d c e - B a e c d) := by
  rw [curvatureQuadraticReactionTensor_eq_of_orthonormalBasis b,
    curvatureQuadraticReaction_apply]
  simp only [curvatureQuadraticContraction_apply]

end DifferentialGeometry.Geometry.Curvature
