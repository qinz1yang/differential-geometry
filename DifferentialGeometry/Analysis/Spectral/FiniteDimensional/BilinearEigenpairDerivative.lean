import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

noncomputable section

namespace Poincare.Analysis

theorem bijective_fderiv_bilinear_normalized_eigenpair
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u v : E, B u v = B v u)
    (hA : ∀ u v : E, B (A u) v = B u (A v))
    (μ : ℝ) (w : E) (hw : B w w = 1) (heigen : A w = μ • w)
    (hsimple : Module.End.eigenspace A.toLinearMap μ = Submodule.span ℝ {w}) :
    Function.Bijective (fderiv ℝ
      (fun q : ℝ × E ↦ ((B q.2 q.2 - 1) / 2, A q.2 - q.1 • q.2)) (μ, w)) := by
  let S := ContinuousLinearMap.snd ℝ ℝ E
  let F := ContinuousLinearMap.fst ℝ ℝ E
  let K := ((B w).comp S).prod (A.comp S - (μ • S + F.smulRight w))
  have hker (q : ℝ × E) (hq : K q = 0) : q = 0 := by
    have hor : B w q.2 = 0 := congrArg Prod.fst hq
    have heq : A q.2 = q.1 • w + μ • q.2 := by
      have h := sub_eq_zero.mp (congrArg Prod.snd hq)
      change A q.2 = μ • q.2 + q.1 • w at h
      rwa [add_comm] at h
    have hs := hA w q.2
    rw [heigen, map_smul, smul_apply, heq, map_add, map_smul, map_smul, hw, hor] at hs
    have hfirst : q.1 = 0 := by simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, add_zero] using hs.symm
    rw [hfirst, zero_smul, zero_add] at heq
    have hmem : q.2 ∈ Submodule.span ℝ {w} := hsimple ▸ Module.End.mem_eigenspace_iff.mpr heq
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hc0 := hor
    rw [← hc, map_smul, hw] at hc0
    have hc' : c = 0 := by simpa only [smul_eq_mul, mul_one] using hc0
    have hsecond : q.2 = 0 := by simpa only [hc', zero_smul] using hc.symm
    exact Prod.ext hfirst hsecond
  have hinj : Function.Injective K := by
    intro a b hab
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hab, sub_self]
  have hbij : Function.Bijective K := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have hf : HasFDerivAt (fun q : ℝ × E ↦ (B q.2 q.2 - 1) / 2)
      ((B w).comp S) (μ, w) := by
    have h := (((B.hasFDerivAt.comp (μ, w)
      (show HasFDerivAt (Prod.snd : ℝ × E → E) S (μ, w) from hasFDerivAt_snd)).clm_apply
      (show HasFDerivAt (Prod.snd : ℝ × E → E) S (μ, w) from hasFDerivAt_snd)).sub_const 1).mul_const (1 / 2 : ℝ)
    convert h using 1 <;> first
      | rfl
      | (funext q; simp [div_eq_mul_inv])
      | (apply ContinuousLinearMap.ext
         intro q
         change B w q.2 = (1 / 2 : ℝ) * (B w q.2 + B q.2 w)
         rw [hB q.2 w]
         ring)
  have hg : HasFDerivAt (fun q : ℝ × E ↦ A q.2 - q.1 • q.2)
      (A.comp S - (μ • S + F.smulRight w)) (μ, w) :=
    (A.hasFDerivAt.comp (μ, w) (show HasFDerivAt (Prod.snd : ℝ × E → E) S (μ, w) from
      hasFDerivAt_snd)).sub ((show HasFDerivAt (Prod.fst : ℝ × E → ℝ) F (μ, w) from
      hasFDerivAt_fst).smul hasFDerivAt_snd)
  rw [(hf.prodMk hg).fderiv]
  exact hbij

end Poincare.Analysis
