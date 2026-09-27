import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
open scoped InnerProductSpace

namespace DifferentialGeometry.Analysis

theorem bijective_fderiv_normalized_eigenpair
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (μ : ℝ) (w : E)
    (hw : ‖w‖ = 1) (heigen : A w = μ • w)
    (hsimple : Module.End.eigenspace A.toLinearMap μ = Submodule.span ℝ {w}) :
    Function.Bijective (fderiv ℝ
      (fun q : ℝ × E ↦ ((‖q.2‖ ^ 2 - 1) / 2, A q.2 - q.1 • q.2)) (μ, w)) := by
  let S := ContinuousLinearMap.snd ℝ ℝ E
  let F := ContinuousLinearMap.fst ℝ ℝ E
  let K : (ℝ × E) →L[ℝ] (ℝ × E) := ((innerSL ℝ w).comp S).prod
    (A.comp S - (μ • S + F.smulRight w))
  have hzero (q : ℝ × E) (hq : K q = 0) : q = 0 := by
    have hor : ⟪w, q.2⟫_ℝ = 0 := congrArg Prod.fst hq
    have heq : A q.2 = q.1 • w + μ • q.2 := by
      have h := sub_eq_zero.mp (congrArg Prod.snd hq)
      change A q.2 = μ • q.2 + q.1 • w at h
      rwa [add_comm] at h
    have hs := hA.isSymmetric w q.2
    change ⟪A w, q.2⟫_ℝ = ⟪w, A q.2⟫_ℝ at hs
    rw [heigen, heq, real_inner_smul_left, inner_add_right,
      real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hw, hor] at hs
    have hfirst : q.1 = 0 := by simpa using hs.symm
    rw [hfirst, zero_smul, zero_add] at heq
    have hmem : q.2 ∈ Submodule.span ℝ {w} := hsimple ▸ Module.End.mem_eigenspace_iff.mpr heq
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hc0 := hor
    rw [← hc, real_inner_smul_right, real_inner_self_eq_norm_sq, hw] at hc0
    have hc' : c = 0 := by simpa using hc0
    have hsecond : q.2 = 0 := by simpa only [hc', zero_smul] using hc.symm
    exact Prod.ext hfirst hsecond
  have hinj : Function.Injective K := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  have hbij : Function.Bijective K := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  have hfst : HasFDerivAt (fun q : ℝ × E ↦ (‖q.2‖ ^ 2 - 1) / 2)
      ((innerSL ℝ w).comp S) (μ, w) := by
    convert (((show HasFDerivAt (Prod.snd : ℝ × E → E) S (μ, w) from
      hasFDerivAt_snd).norm_sq).sub_const 1).mul_const (1 / 2 : ℝ) using 1 <;>
      first | rfl | (funext q; simp [div_eq_mul_inv]) |
        (apply ContinuousLinearMap.ext; intro q; norm_num [smul_smul]; ring)
  have hsnd : HasFDerivAt (fun q : ℝ × E ↦ A q.2 - q.1 • q.2)
      (A.comp S - (μ • S + F.smulRight w)) (μ, w) :=
    (A.hasFDerivAt.comp (μ, w) (show HasFDerivAt (Prod.snd : ℝ × E → E) S (μ, w) from
      hasFDerivAt_snd)).sub ((show HasFDerivAt (Prod.fst : ℝ × E → ℝ) F (μ, w) from
        hasFDerivAt_fst).smul hasFDerivAt_snd)
  rw [(hfst.prodMk hsnd).fderiv]
  exact hbij

end DifferentialGeometry.Analysis
