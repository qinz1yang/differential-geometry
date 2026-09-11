import DifferentialGeometry.Topology.VectorField.CollarExtension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Sign.Basic

set_option autoImplicit false

open ContinuousLinearMap Set
open scoped Manifold

noncomputable section

namespace DifferentialGeometry.VectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasFDerivAt_collarExtension {T : E → E} {b : E → ℝ} {ρ : ℝ → ℝ}
    {x : E} {t ρ' : ℝ} {T' : E →L[ℝ] E} {b' : E →L[ℝ] ℝ}
    (hT : HasFDerivAt T T' x) (hb : HasFDerivAt b b' x) (hρ : HasDerivAt ρ ρ' t) :
    HasFDerivAt (collarExtension (I := 𝓘(ℝ, E)) T b ρ)
      ((T'.comp (fst ℝ E ℝ)).prod
        (((1 - ρ t) • b').comp (fst ℝ E ℝ) + (ρ' * (1 - b x)) • snd ℝ E ℝ)) (x, t) := by
  have hf : HasFDerivAt (@Prod.fst E ℝ) (fst ℝ E ℝ) (x, t) := hasFDerivAt_fst
  have hs : HasFDerivAt (@Prod.snd E ℝ) (snd ℝ E ℝ) (x, t) := hasFDerivAt_snd
  have hT' := hT.comp (x, t) hf
  have hb' := hb.comp (x, t) hf
  have hρ' := hρ.comp_hasFDerivAt (x, t) hs
  have h := hT'.prodMk (((hρ'.const_sub 1).mul hb').add hρ')
  have heq : (1 - ρ t) • b'.comp (fst ℝ E ℝ) +
        b x • -(ρ' • snd ℝ E ℝ) + ρ' • snd ℝ E ℝ =
      ((1 - ρ t) • b').comp (fst ℝ E ℝ) + (ρ' * (1 - b x)) • snd ℝ E ℝ := by
    apply ContinuousLinearMap.ext
    intro v
    change (1 - ρ t) * b' v.1 + b x * -(ρ' * v.2) + ρ' * v.2 =
      (1 - ρ t) * b' v.1 + (ρ' * (1 - b x)) * v.2
    ring
  change HasFDerivAt (collarExtension (I := 𝓘(ℝ, E)) T b ρ)
    ((T'.comp (fst ℝ E ℝ)).prod
      ((1 - ρ t) • b'.comp (fst ℝ E ℝ) + b x • -(ρ' • snd ℝ E ℝ) +
        ρ' • snd ℝ E ℝ)) (x, t) at h
  rw [heq] at h
  exact h

theorem fderiv_collarExtension_apply {T : E → E} {b : E → ℝ} {ρ : ℝ → ℝ}
    {x : E} {t : ℝ} (hT : DifferentiableAt ℝ T x) (hb : DifferentiableAt ℝ b x)
    (hρ : DifferentiableAt ℝ ρ t) (v : E × ℝ) :
    fderiv ℝ (collarExtension (I := 𝓘(ℝ, E)) T b ρ) (x, t) v =
      (fderiv ℝ T x v.1,
        (1 - ρ t) * fderiv ℝ b x v.1 + deriv ρ t * (1 - b x) * v.2) := by
  rw [(hasFDerivAt_collarExtension hT.hasFDerivAt hb.hasFDerivAt hρ.hasDerivAt).fderiv]
  rfl

private theorem det_prod_fst_add_snd [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (ℓ : E →L[ℝ] ℝ) (c : ℝ) :
    LinearMap.det (((A.comp (fst ℝ E ℝ)).prod
      (ℓ.comp (fst ℝ E ℝ) + c • snd ℝ E ℝ)).toLinearMap) =
      LinearMap.det A.toLinearMap * c := by
  classical
  let B := Module.finBasis ℝ E
  let e := Module.Basis.singleton Unit ℝ
  let L := (A.comp (fst ℝ E ℝ)).prod (ℓ.comp (fst ℝ E ℝ) + c • snd ℝ E ℝ)
  have hmatrix : LinearMap.toMatrix (B.prod e) (B.prod e) L.toLinearMap =
      Matrix.fromBlocks (LinearMap.toMatrix B B A.toLinearMap) 0
        (LinearMap.toMatrix B e ℓ.toLinearMap)
        (LinearMap.toMatrix e e (LinearMap.mulLeft ℝ c)) := by
    ext (i | i) (j | j) <;> simp [LinearMap.toMatrix, L]
  change LinearMap.det L.toLinearMap = _
  rw [← LinearMap.det_toMatrix (B.prod e), hmatrix, Matrix.det_fromBlocks_zero₁₂,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix, LinearMap.det_mulLeft]

theorem det_fderiv_collarExtension [FiniteDimensional ℝ E]
    {T : E → E} {b : E → ℝ} {ρ : ℝ → ℝ} {x : E} {t : ℝ}
    (hT : DifferentiableAt ℝ T x) (hb : DifferentiableAt ℝ b x)
    (hρ : DifferentiableAt ℝ ρ t) :
    LinearMap.det (fderiv ℝ (collarExtension (I := 𝓘(ℝ, E)) T b ρ) (x, t)).toLinearMap =
      deriv ρ t * (1 - b x) * LinearMap.det (fderiv ℝ T x).toLinearMap := by
  rw [(hasFDerivAt_collarExtension hT.hasFDerivAt hb.hasFDerivAt hρ.hasDerivAt).fderiv]
  rw [det_prod_fst_add_snd, mul_comm]

private theorem collar_normal_factor_pos {T : E → E} {b : E → ℝ} {x : E} {t : ℝ}
    (hboundary : T x = 0 → b x ≠ 0)
    (hzero : collarExtension (I := 𝓘(ℝ, E)) T b collarTransition (x, t) = 0) :
    0 < deriv collarTransition t * (1 - b x) := by
  have hρ := contDiff_collarTransition.differentiable (by simp) t
  have hpos := collarExtension_normal_deriv_pos hboundary hzero
  rw [(hasDerivAt_collarExtension_normal (T := T) (b := b) hρ.hasDerivAt).deriv] at hpos
  exact hpos

theorem sign_det_fderiv_collarExtension [FiniteDimensional ℝ E]
    {T : E → E} {b : E → ℝ} {x : E} {t : ℝ}
    (hT : DifferentiableAt ℝ T x) (hb : DifferentiableAt ℝ b x)
    (hboundary : T x = 0 → b x ≠ 0)
    (hzero : collarExtension (I := 𝓘(ℝ, E)) T b collarTransition (x, t) = 0) :
    SignType.sign (LinearMap.det
      (fderiv ℝ (collarExtension (I := 𝓘(ℝ, E)) T b collarTransition) (x, t)).toLinearMap) =
      SignType.sign (LinearMap.det (fderiv ℝ T x).toLinearMap) := by
  rw [det_fderiv_collarExtension hT hb (contDiff_collarTransition.differentiable (by simp) t),
    sign_mul, sign_pos (collar_normal_factor_pos hboundary hzero), one_mul]

theorem det_fderiv_collarExtension_ne_zero_iff [FiniteDimensional ℝ E]
    {T : E → E} {b : E → ℝ} {x : E} {t : ℝ}
    (hT : DifferentiableAt ℝ T x) (hb : DifferentiableAt ℝ b x)
    (hboundary : T x = 0 → b x ≠ 0)
    (hzero : collarExtension (I := 𝓘(ℝ, E)) T b collarTransition (x, t) = 0) :
    LinearMap.det
      (fderiv ℝ (collarExtension (I := 𝓘(ℝ, E)) T b collarTransition) (x, t)).toLinearMap ≠ 0 ↔
      LinearMap.det (fderiv ℝ T x).toLinearMap ≠ 0 := by
  rw [det_fderiv_collarExtension hT hb (contDiff_collarTransition.differentiable (by simp) t)]
  exact mul_ne_zero_iff.trans (and_iff_right (collar_normal_factor_pos hboundary hzero).ne')

end DifferentialGeometry.VectorField
