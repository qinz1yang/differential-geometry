import DifferentialGeometry.Analysis.Elliptic.Euclidean.ScalarOperator.Basic
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.DirectionalJets

section

noncomputable section

namespace DifferentialGeometry.Analysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "V" => EuclideanSpace ℝ ι

theorem scalarEllipticOperator_fderiv_apply
    (A : V → Matrix ι ι ℝ) (b : V → ι → ℝ) {u : V → ℝ} {x : V}
    (hu : ContDiffAt ℝ 3 u x)
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hb : ∀ i, DifferentiableAt ℝ (fun y => b y i) x) (v : V) :
    scalarEllipticOperator A b (fun y => fderiv ℝ u y v) x =
      fderiv ℝ (scalarEllipticOperator A b u) x v -
        (∑ i, ∑ j, fderiv ℝ (fun y => A y i j) x v *
          fderiv ℝ (fderiv ℝ u) x
            (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) -
        ∑ i, fderiv ℝ (fun y => b y i) x v *
          fderiv ℝ u x (EuclideanSpace.single i 1) := by
  let e : ι → V := fun i => EuclideanSpace.single i 1
  have huD : ContDiffAt ℝ 2 (fderiv ℝ u) x :=
    hu.fderiv_right (by norm_num)
  have huDD : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ u)) x :=
    huD.fderiv_right (by norm_num)
  have hD := huD.differentiableAt (by norm_num)
  have hDD := huDD.differentiableAt (by norm_num)
  have hsym := hu.isSymmSndFDerivAt (by norm_num)
  have hfirst (w : V) :
      fderiv ℝ (fun y => fderiv ℝ u y w) x v =
        fderiv ℝ (fun y => fderiv ℝ u y v) x w := by
    rw [fderiv_clm_apply hD (differentiableAt_const w),
      fderiv_clm_apply hD (differentiableAt_const v)]
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
      ContinuousLinearMap.flip_apply]
    exact hsym.eq v w
  have hthird (w z : V) :
      fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ u) y w z) x v =
        fderiv ℝ (fderiv ℝ (fun y => fderiv ℝ u y v)) x w z := by
    have hI : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 u) x :=
      (hu.iteratedFDeriv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num)
    have he := congrArg
      (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => V) ℝ => T ![w, z])
      (hu.fderiv_iteratedFDeriv_apply (n := 2) v)
    have ha := fderiv_continuousMultilinear_apply_const_apply hI ![w, z] v
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] at he ha
    exact ha.trans he
  have hH (i j : ι) :
      DifferentiableAt ℝ
        (fun y => fderiv ℝ (fderiv ℝ u) y (e i) (e j)) x :=
    (hDD.clm_apply (differentiableAt_const (e i))).clm_apply
      (differentiableAt_const (e j))
  have hG (i : ι) : DifferentiableAt ℝ (fun y => fderiv ℝ u y (e i)) x :=
    hD.clm_apply (differentiableAt_const (e i))
  have hP (i j : ι) : DifferentiableAt ℝ
      (fun y => A y i j * fderiv ℝ (fderiv ℝ u) y (e i) (e j)) x :=
    (hA i j).mul (hH i j)
  have hB (i : ι) : DifferentiableAt ℝ
      (fun y => b y i * fderiv ℝ u y (e i)) x :=
    (hb i).mul (hG i)
  have hprincipal : DifferentiableAt ℝ
      (fun y => ∑ i, ∑ j, A y i j * fderiv ℝ (fderiv ℝ u) y (e i) (e j)) x :=
    DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ => hP i j
  have hdrift : DifferentiableAt ℝ
      (fun y => ∑ i, b y i * fderiv ℝ u y (e i)) x :=
    DifferentiableAt.fun_sum fun i _ => hB i
  have hoperator : fderiv ℝ (scalarEllipticOperator A b u) x v =
      (∑ i, ∑ j, (fderiv ℝ (fun y => A y i j) x v *
          fderiv ℝ (fderiv ℝ u) x (e i) (e j) +
        A x i j * fderiv ℝ
          (fun y => fderiv ℝ (fderiv ℝ u) y (e i) (e j)) x v)) +
      ∑ i, (fderiv ℝ (fun y => b y i) x v * fderiv ℝ u x (e i) +
        b x i * fderiv ℝ (fun y => fderiv ℝ u y (e i)) x v) := by
    change fderiv ℝ
      (fun y => (∑ i, ∑ j, A y i j * fderiv ℝ (fderiv ℝ u) y (e i) (e j)) +
        ∑ i, b y i * fderiv ℝ u y (e i)) x v = _
    rw [fderiv_fun_add hprincipal hdrift]
    simp only [add_apply]
    congr 1
    · rw [fderiv_fun_sum
        (fun i _ => DifferentiableAt.fun_sum fun j _ => hP i j)]
      simp only [sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [fderiv_fun_sum (fun j _ => hP i j)]
      simp only [sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [fderiv_fun_mul (hA i j) (hH i j)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    · rw [fderiv_fun_sum (fun i _ => hB i)]
      simp only [sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [fderiv_fun_mul (hb i) (hG i)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
  rw [hoperator]
  simp only [hthird, hfirst, Finset.sum_add_distrib, scalarEllipticOperator, e]
  ring

end DifferentialGeometry.Analysis

end

end

section

noncomputable section

namespace DifferentialGeometry.Analysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "V" => EuclideanSpace ℝ ι

theorem scalarEllipticOperator_gradient_sq
    (A : V → Matrix ι ι ℝ) (b : V → ι → ℝ) {u : V → ℝ} {x : V}
    (hu : ContDiffAt ℝ 3 u x)
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hb : ∀ i, DifferentiableAt ℝ (fun y => b y i) x) :
    scalarEllipticOperator A b
        (fun y => ∑ k, (fderiv ℝ u y (EuclideanSpace.single k 1)) ^ 2) x =
      2 * (∑ k, ∑ i, ∑ j, A x i j *
        fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single k 1)) x
          (EuclideanSpace.single i 1) *
        fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single k 1)) x
          (EuclideanSpace.single j 1)) +
      2 * (∑ k, fderiv ℝ u x (EuclideanSpace.single k 1) *
        fderiv ℝ (scalarEllipticOperator A b u) x (EuclideanSpace.single k 1)) -
      2 * (∑ k, ∑ i, ∑ j, fderiv ℝ u x (EuclideanSpace.single k 1) *
        fderiv ℝ (fun y => A y i j) x (EuclideanSpace.single k 1) *
        fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) -
      2 * (∑ k, ∑ i, fderiv ℝ u x (EuclideanSpace.single k 1) *
        fderiv ℝ (fun y => b y i) x (EuclideanSpace.single k 1) *
        fderiv ℝ u x (EuclideanSpace.single i 1)) := by
  have hpartial (k : ι) : ContDiffAt ℝ 2
      (fun y => fderiv ℝ u y (EuclideanSpace.single k 1)) x :=
    (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiffAt_const
  rw [scalarEllipticOperator_sum A b Finset.univ
    (fun k y => (fderiv ℝ u y (EuclideanSpace.single k 1)) ^ 2)
    (fun k _ => (hpartial k).pow 2)]
  simp_rw [scalarEllipticOperator_sq A b (hpartial _),
    scalarEllipticOperator_fderiv_apply A b hu hA hb]
  simp only [mul_sub, Finset.mul_sum, ← mul_assoc, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  ring

end DifferentialGeometry.Analysis

end

end
