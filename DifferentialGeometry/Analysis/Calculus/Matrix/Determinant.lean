import DifferentialGeometry.Analysis.Integration.Measure.JacobiFormula
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Matrix.Normed

noncomputable section

open scoped ContDiff Matrix.Norms.Elementwise

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem contDiff_det {𝕜 R : Type*} [NontriviallyNormedField 𝕜]
    [NormedCommRing R] [NormedAlgebra 𝕜 R] {n : ℕ∞ω} :
    ContDiff 𝕜 n (det : Matrix ι ι R → R) := by
  change ContDiff 𝕜 n (fun A : Matrix ι ι R => A.det)
  simp_rw [det_apply']
  refine ContDiff.sum fun σ _ => ?_
  exact contDiff_const.mul (contDiff_prod fun i _ =>
    contDiff_pi.mp (contDiff_pi.mp contDiff_id (σ i)) i)

theorem fderiv_det_apply (A B : Matrix ι ι ℝ) :
    fderiv ℝ det A B = trace (adjugate A * B) := by
  have hline : HasDerivAt (fun t : ℝ => A + t • B) B 0 := by
    exact (((hasDerivAt_id (0 : ℝ)).smul_const B).const_add A).congr_deriv (one_smul ℝ B)
  have hchain := (contDiff_det (𝕜 := ℝ) (n := 1)).differentiable (by simp) A
    |>.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hdet := DifferentialGeometry.Integral.Measure.hasDerivAt_det_eq_trace_adjugate_mul
    (fun t : ℝ => A + t • B) B 0
    (fun i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp hline i) j)
  exact (hchain.unique hdet).trans
    (congrArg (fun C : Matrix ι ι ℝ => trace (adjugate C * B))
      (show A + (0 : ℝ) • B = A by simp))

theorem fderiv_sqrt_det_apply (A B : Matrix ι ι ℝ) (hpos : 0 < A.det) :
    fderiv ℝ (fun C : Matrix ι ι ℝ => Real.sqrt C.det) A B =
      (1 / 2) * trace (A⁻¹ * B) * Real.sqrt A.det := by
  have hline : HasDerivAt (fun t : ℝ => A + t • B) B 0 := by
    exact (((hasDerivAt_id (0 : ℝ)).smul_const B).const_add A).congr_deriv (one_smul ℝ B)
  have houter := (contDiff_det (𝕜 := ℝ) (n := 1)).contDiffAt.sqrt hpos.ne'
  have hchain := houter.differentiableAt (by simp)
    |>.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hdet := DifferentialGeometry.Integral.Measure.hasDerivAt_sqrt_det_eq_half_trace_inv_mul
    (fun t : ℝ => A + t • B) B 0
    (fun i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp hline i) j) (by simpa using hpos)
  exact (hchain.unique hdet).trans
    (congrArg (fun C : Matrix ι ι ℝ => (1 / 2) * trace (C⁻¹ * B) * Real.sqrt C.det)
      (show A + (0 : ℝ) • B = A by simp))

theorem iteratedDeriv_two_sqrt_det_of_deriv_eq_zero
    {G : ℝ → Matrix ι ι ℝ} {t : ℝ} (hG : ContDiffAt ℝ 2 G t)
    (hzero : deriv G t = 0) (hpos : 0 < (G t).det) :
    iteratedDeriv 2 (fun s => Real.sqrt (G s).det) t =
      (1 / 2) * trace ((G t)⁻¹ * iteratedDeriv 2 G t) * Real.sqrt (G t).det := by
  have houter := (contDiff_det (𝕜 := ℝ) (n := 2)).contDiffAt.sqrt hpos.ne'
  have h := iteratedDeriv_vcomp_two houter hG
  let B := iteratedFDeriv ℝ 2 (fun C : Matrix ι ι ℝ => Real.sqrt C.det) (G t)
  have hvanish : B (fun _ => deriv G t) = 0 :=
    (congrArg (fun v : Matrix ι ι ℝ => B (fun _ => v)) hzero).trans B.map_zero
  refine h.trans ?_
  exact (congrArg (fun v : ℝ =>
    v + fderiv ℝ (fun C : Matrix ι ι ℝ => Real.sqrt C.det) (G t) (iteratedDeriv 2 G t))
    hvanish).trans ((zero_add _).trans (fderiv_sqrt_det_apply _ _ hpos))

end Matrix
