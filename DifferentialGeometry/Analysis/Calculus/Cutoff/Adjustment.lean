import DifferentialGeometry.Analysis.Calculus.Cutoff.Basic
import DifferentialGeometry.Analysis.Normed.Operator.SurjectivePerturbation
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set Filter Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace HasFDerivAt

theorem norm_cutoff_adjustment_sub_le {f g : E → F} {ψ : E → ℝ} {x : E}
    {f' g' : E →L[ℝ] F} {ψ' : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (hψ : HasFDerivAt ψ ψ' x) :
    ‖fderiv ℝ (fun y => f y + ψ y • (g y - f y)) x - f'‖ ≤
      |ψ x| * ‖g' - f'‖ + ‖ψ'‖ * ‖g x - f x‖ := by
  change ‖fderiv ℝ (f + ψ • (g - f)) x - f'‖ ≤ _
  rw [(hf.add (hψ.smul (hg.sub hf))).fderiv, add_sub_cancel_left]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul, Real.norm_eq_abs,
    ContinuousLinearMap.norm_smulRight_apply]; rfl)

theorem norm_cutoff_adjustment_sub_le_of_bounds {f g : E → F} {ψ : E → ℝ} {x : E}
    {f' g' : E →L[ℝ] F} {ψ' : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (hψ : HasFDerivAt ψ ψ' x) {a b d : ℝ}
    (hψx : |ψ x| ≤ 1) (hd : ‖g' - f'‖ ≤ d)
    (hb : ‖ψ'‖ ≤ b) (ha : ‖g x - f x‖ ≤ a) :
    ‖fderiv ℝ (fun y => f y + ψ y • (g y - f y)) x - f'‖ ≤ d + b * a := by
  apply (hf.norm_cutoff_adjustment_sub_le hg hψ).trans
  exact add_le_add
    ((mul_le_mul_of_nonneg_right hψx (norm_nonneg _)).trans (by simpa using hd))
    (mul_le_mul hb ha (norm_nonneg _) ((norm_nonneg _).trans hb))

theorem norm_cutoff_postcomp_sub_le {f : E → F} {P : F → F} {ψ : F → ℝ} {x : E}
    {f' : E →L[ℝ] F} {P' A : F →L[ℝ] F} {ψ' : F →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x) (hP : HasFDerivAt P P' (f x))
    (hψ : HasFDerivAt ψ ψ' (f x)) {a b d e L ρ : ℝ} (hρ : 0 < ρ)
    (hψx : |ψ (f x)| ≤ 1) (ha : ‖P (f x) - f x‖ ≤ a * ρ)
    (hb : ‖ψ'‖ ≤ b / ρ) (hL : ‖f'‖ ≤ L) (hd : ‖P' - A‖ ≤ d)
    (he : ‖(ContinuousLinearMap.id ℝ F - A).comp f'‖ ≤ e) :
    ‖fderiv ℝ (fun y => f y + ψ (f y) • (P (f y) - f y)) x - f'‖ ≤
      a * b * L + d * L + e := by
  have hdiff : P'.comp f' - f' = (P' - A).comp f' -
      (ContinuousLinearMap.id ℝ F - A).comp f' := by
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp]
    abel
  have hpbound : ‖P'.comp f' - f'‖ ≤ d * L + e := by
    rw [hdiff]
    exact (norm_sub_le _ _).trans (add_le_add
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hd hL (norm_nonneg _) ((norm_nonneg _).trans hd))) he)
  have hψbound : ‖ψ'.comp f'‖ ≤ b / ρ * L :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hb hL (norm_nonneg _) ((norm_nonneg _).trans hb))
  have h := hf.norm_cutoff_adjustment_sub_le_of_bounds (hP.comp x hf)
    (hψ.comp x hf) hψx hpbound hψbound ha
  apply h.trans_eq
  field_simp
  ring

theorem surjective_cutoff_adjustment [CompleteSpace F]
    {f g : E → F} {ψ : E → ℝ} {x : E}
    {f' g' : E →L[ℝ] F} {ψ' : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x)
    (hψ : HasFDerivAt ψ ψ' x) (R : F →L[ℝ] E)
    (hR : f'.comp R = ContinuousLinearMap.id ℝ F) {a b d : ℝ}
    (hψx : |ψ x| ≤ 1) (hd : ‖g' - f'‖ ≤ d)
    (hb : ‖ψ'‖ ≤ b) (ha : ‖g x - f x‖ ≤ a)
    (hsmall : (d + b * a) * ‖R‖ < 1) :
    Function.Surjective (fderiv ℝ (fun y => f y + ψ y • (g y - f y)) x) := by
  apply ContinuousLinearMap.surjective_of_norm_sub_mul_lt_one _ f' R hR
  exact (mul_le_mul_of_nonneg_right
    (hf.norm_cutoff_adjustment_sub_le_of_bounds hg hψ hψx hd hb ha)
    (norm_nonneg R)).trans_lt hsmall

theorem norm_projected_cutoff_sub_le
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {f : E → F} {P : Q → Q} {ψ : F → ℝ} {x : E}
    {f' : E →L[ℝ] F} {P' A : Q →L[ℝ] Q} {ψ' : F →L[ℝ] ℝ}
    (π : F →L[ℝ] Q) (ι : Q →L[ℝ] F) (hπ : ‖π‖ ≤ 1) (hι : ‖ι‖ ≤ 1)
    (hf : HasFDerivAt f f' x) (hP : HasFDerivAt P P' (π (f x)))
    (hψ : HasFDerivAt ψ ψ' (f x)) {a b d e L ρ : ℝ} (hρ : 0 < ρ)
    (hψx : |ψ (f x)| ≤ 1) (ha : ‖P (π (f x)) - π (f x)‖ ≤ a * ρ)
    (hb : ‖ψ'‖ ≤ b / ρ) (hL : ‖f'‖ ≤ L) (hd : ‖P' - A‖ ≤ d)
    (he : ‖(ContinuousLinearMap.id ℝ Q - A).comp (π.comp f')‖ ≤ e) :
    ‖fderiv ℝ (fun y => f y + ψ (f y) • ι (P (π (f y)) - π (f y))) x - f'‖ ≤
      a * b * L + d * L + e := by
  have hqL : ‖π.comp f'‖ ≤ L := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul_of_nonneg_right hπ (norm_nonneg _)).trans (by simpa using hL))
  have hdiff : P'.comp (π.comp f') - π.comp f' =
      (P' - A).comp (π.comp f') -
        (ContinuousLinearMap.id ℝ Q - A).comp (π.comp f') := by
    simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp]
    abel
  have hd' : ‖ι.comp (P'.comp (π.comp f') - π.comp f')‖ ≤ d * L + e := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply ((mul_le_mul_of_nonneg_right hι (norm_nonneg _)).trans_eq (one_mul _)).trans
    rw [hdiff]
    exact (norm_sub_le _ _).trans (add_le_add
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hd hqL (norm_nonneg _) ((norm_nonneg _).trans hd))) he)
  have ha' : ‖ι (P (π (f x)) - π (f x))‖ ≤ a * ρ :=
    (ι.le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right hι (norm_nonneg _)).trans (by simpa using ha))
  have hb' : ‖ψ'.comp f'‖ ≤ b / ρ * L :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hb hL (norm_nonneg _) ((norm_nonneg _).trans hb))
  have hπf := π.hasFDerivAt.comp x hf
  have hg := hf.add (ι.hasFDerivAt.comp x ((hP.comp x hπf).sub hπf))
  have h := hf.norm_cutoff_adjustment_sub_le_of_bounds hg (hψ.comp x hf) hψx
    (by simpa only [add_sub_cancel_left] using hd') hb'
    (by simpa only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, add_sub_cancel_left] using ha')
  simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply, add_sub_cancel_left] at h
  apply h.trans_eq
  field_simp
  ring

end HasFDerivAt

namespace ContDiff

theorem cutoff_adjustment {n : ℕ∞ω} {ψ : E → ℝ} {f g : E → F} {U : Set E}
    (hf : ContDiff ℝ n f) (hg : ContDiffOn ℝ n g U) (hψ : ContDiff ℝ n ψ)
    (hU : IsOpen U) (hs : tsupport ψ ⊆ U) :
    ContDiff ℝ n (fun x => f x + ψ x • (g x - f x)) := by
  apply hf.add
  apply contDiffOn_univ.mp
  exact DifferentialGeometry.Analysis.contDiffOn_cutoff_smul hU hψ hs
    (by simpa only [univ_inter] using hg.sub hf.contDiffOn)

end ContDiff
