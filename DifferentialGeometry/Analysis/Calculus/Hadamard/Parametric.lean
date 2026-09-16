import DifferentialGeometry.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.Deriv.Prod
import DifferentialGeometry.Analysis.Integration.RadialIntegralSmoothness

noncomputable section

open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis.Calculus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
private theorem deriv_snd_eq_fderiv (f : E × ℝ → F) (hf : ContDiff ℝ ∞ f) (p : E × ℝ) :
    deriv (fun t => f (p.1, t)) p.2 = fderiv ℝ f p (0, 1) := by
  have hd : HasDerivAt (fun t : ℝ => (p.1, t)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact ((hf.differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.2 hd).deriv

omit [CompleteSpace F] in
theorem contDiffOn_hadamardFactor_param
    {S : Set E} {U : Set ℝ} (hS : IsOpen S) (hU : IsOpen U)
    (hstar : StarConvex ℝ 0 U) {f : E × ℝ → F}
    (hf : ContDiffOn ℝ ∞ f (S ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun p : E × ℝ => hadamardFactor (fun t => f (p.1, t)) 0 p.2)
      (S ×ˢ U) := by
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ f) (S ×ˢ U) :=
    (contDiffOn_infty_iff_fderiv_of_isOpen (hS.prod hU)).mp hf |>.2
  have hder : ContDiffOn ℝ ∞ (fun p : E × ℝ => deriv (fun t => f (p.1, t)) p.2)
      (S ×ˢ U) := by
    apply (hfd.clm_apply (contDiffOn_const (c := ((0 : E), (1 : ℝ))))).congr
    intro p hp
    have hd : HasDerivAt (fun t : ℝ => (p.1, t)) (0, 1) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    have hdif := (hf.contDiffAt ((hS.prod hU).mem_nhds hp)).differentiableAt (by simp)
    exact (hdif.hasFDerivAt.comp_hasDerivAt p.2 hd).deriv
  have hint := DifferentialGeometry.Integral.contDiffOn_radialIntegral_joint (⊤ : ℕ∞) 0
    hS hU hstar (f := fun p r => deriv (fun t => f (p, t)) r) hder
  simpa only [hadamardFactor, DifferentialGeometry.Integral.radialIntegral,
    sub_zero, zero_add, smul_eq_mul, pow_zero, one_smul] using hint

omit [CompleteSpace F] in
theorem contDiff_hadamardFactor_param
    (f : E × ℝ → F) (hf : ContDiff ℝ ∞ f) (a : ℝ) :
    ContDiff ℝ ∞ (fun p : E × ℝ => hadamardFactor (fun t => f (p.1, t)) a p.2) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
  have hder : ContDiff ℝ ∞ (fun p : E × ℝ => deriv (fun t => f (p.1, t)) p.2) := by
    convert hfd.clm_apply (contDiff_const (c := ((0 : E), (1 : ℝ)))) using 1
    funext p
    exact deriv_snd_eq_fderiv f hf p
  have hshift : ContDiff ℝ ∞ (fun p : E × ℝ => deriv (fun t => f (p.1, t)) (a + p.2)) :=
    hder.comp (contDiff_fst.prodMk (contDiff_const.add contDiff_snd))
  have hint := DifferentialGeometry.Integral.contDiffOn_radialIntegral_joint (⊤ : ℕ∞) 0
    isOpen_univ isOpen_univ (starConvex_univ (𝕜 := ℝ) (x := (0 : ℝ)))
    (f := fun p r => deriv (fun t => f (p, t)) (a + r)) hshift.contDiffOn
  have hint' : ContDiff ℝ ∞
      (fun p : E × ℝ => DifferentialGeometry.Integral.radialIntegral 0
        (fun r => deriv (fun t => f (p.1, t)) (a + r)) p.2) := by
    simpa only [univ_prod_univ, contDiffOn_univ] using hint
  have hfinal := hint'.comp (contDiff_fst.prodMk (contDiff_snd.sub (contDiff_const (c := a))))
  change ContDiff ℝ ∞ (fun p : E × ℝ => DifferentialGeometry.Integral.radialIntegral 0
    (fun r => deriv (fun t => f (p.1, t)) (a + r)) (p.2 - a)) at hfinal
  simpa only [DifferentialGeometry.Integral.radialIntegral, hadamardFactor,
    pow_zero, one_smul, smul_eq_mul] using hfinal

theorem hadamardFactor_zero (f : ℝ → F) :
    hadamardFactor f 0 0 = deriv f 0 := by
  simp [hadamardFactor]

omit [CompleteSpace F] in
theorem contDiff_rescaled_hadamardFactor
    (f : E × ℝ → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun q : E × ℝ × ℝ =>
      q.2.1 • hadamardFactor (fun t => f (q.1, t)) 0 (q.2.2 * q.2.1)) :=
  contDiff_snd.fst.smul ((contDiff_hadamardFactor_param f hf 0).comp
    (contDiff_fst.prodMk (contDiff_snd.snd.mul contDiff_snd.fst)))

theorem rescaled_hadamardFactor_eq (f : E × ℝ → F) (hf : ContDiff ℝ ∞ f)
    (p : E) (t s : ℝ) (hs : s ≠ 0) :
    t • hadamardFactor (fun r => f (p, r)) 0 (s * t) =
      s⁻¹ • (f (p, s * t) - f (p, 0)) := by
  have hsmooth : ContDiff ℝ ∞ (fun r => f (p, r)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  rw [hadamard_factorization (fun r => f (p, r)) hsmooth 0 (s * t), sub_zero,
    smul_smul, inv_mul_cancel_left₀ hs]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem rescaled_hadamardFactor_at_zero (f : E × ℝ → F) (p : E) (t : ℝ) :
    t • hadamardFactor (fun r => f (p, r)) 0 ((0 : ℝ) * t) =
      t • deriv (fun r => f (p, r)) 0 := by
  rw [zero_mul, hadamardFactor_zero]

end DifferentialGeometry.Analysis.Calculus
