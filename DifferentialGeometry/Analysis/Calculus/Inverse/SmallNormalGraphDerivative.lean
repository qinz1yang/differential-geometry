import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open scoped Topology

namespace DifferentialGeometry.Analysis

variable {E N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

theorem fderiv_normal_graph_relation
    {g : E → N} {e : E × N → N} {x : E}
    (hg : DifferentiableAt ℝ g x) (he : DifferentiableAt ℝ e (x, g x))
    (hrel : ∀ᶠ t in 𝓝 x, g t + e (t, g t) = 0) (v : E) :
    fderiv ℝ g x v + fderiv ℝ (fun t : E => e (t, g x)) x v +
      fderiv ℝ (fun z : N => e (x, z)) (g x) (fderiv ℝ g x v) = 0 := by
  let D : E →L[ℝ] N := fderiv ℝ g x
  let J : (E × N) →L[ℝ] N := fderiv ℝ e (x, g x)
  let T : E →L[ℝ] N := fderiv ℝ (fun t : E => e (t, g x)) x
  let B : N →L[ℝ] N := fderiv ℝ (fun z : N => e (x, z)) (g x)
  have hT : J.comp (ContinuousLinearMap.inl ℝ E N) = T := by
    exact (he.hasFDerivAt.comp x
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const (g x) x))).fderiv.symm
  have hB : J.comp (ContinuousLinearMap.inr ℝ E N) = B := by
    exact (he.hasFDerivAt.comp (g x)
      ((hasFDerivAt_const x (g x)).prodMk (hasFDerivAt_id (g x)))).fderiv.symm
  have hsplit (a : E) (b : N) : J (a, b) = T a + B b := by
    have hdecomp : (a, b) = (a, (0 : N)) + ((0 : E), b) := by simp
    rw [hdecomp, map_add]
    have hTa := DFunLike.congr_fun hT a
    have hBb := DFunLike.congr_fun hB b
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply] using congrArg₂ (· + ·) hTa hBb
  have htotal : HasFDerivAt (fun t : E => g t + e (t, g t))
      (D + J.comp ((ContinuousLinearMap.id ℝ E).prod D)) x := by
    exact hg.hasFDerivAt.add (he.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hg.hasFDerivAt))
  have hconst : HasFDerivAt (fun t : E => g t + e (t, g t)) (0 : E →L[ℝ] N) x :=
    (hasFDerivAt_const (0 : N) x).congr_of_eventuallyEq hrel
  have hzero := DFunLike.congr_fun (htotal.unique hconst) v
  change D v + J (v, D v) = 0 at hzero
  rw [hsplit, ← add_assoc] at hzero
  exact hzero

theorem norm_fderiv_normal_graph_le
    {g : E → N} {e : E × N → N} {x : E}
    (hg : DifferentiableAt ℝ g x) (he : DifferentiableAt ℝ e (x, g x))
    (hrel : ∀ᶠ t in 𝓝 x, g t + e (t, g t) = 0)
    (hsmall : ‖fderiv ℝ (fun z : N => e (x, z)) (g x)‖ < 1) :
    ‖fderiv ℝ g x‖ ≤
      ‖fderiv ℝ (fun t : E => e (t, g x)) x‖ /
        (1 - ‖fderiv ℝ (fun z : N => e (x, z)) (g x)‖) := by
  let D : E →L[ℝ] N := fderiv ℝ g x
  let T : E →L[ℝ] N := fderiv ℝ (fun t : E => e (t, g x)) x
  let B : N →L[ℝ] N := fderiv ℝ (fun z : N => e (x, z)) (g x)
  have hidentity : D = -(T + B.comp D) := by
    ext v
    have h := fderiv_normal_graph_relation hg he hrel v
    change D v + T v + B (D v) = 0 at h
    rw [add_assoc] at h
    change D v = -(T v + B (D v))
    exact eq_neg_of_add_eq_zero_left h
  have habsorb : ‖D‖ ≤ ‖T‖ + ‖B‖ * ‖D‖ := by
    calc
      ‖D‖ = ‖T + B.comp D‖ := by
        simpa only [norm_neg] using congrArg norm hidentity
      _ ≤ ‖T‖ + ‖B.comp D‖ := norm_add_le _ _
      _ ≤ ‖T‖ + ‖B‖ * ‖D‖ := add_le_add le_rfl (ContinuousLinearMap.opNorm_comp_le B D)
  have hpos : 0 < 1 - ‖B‖ := sub_pos.mpr hsmall
  change ‖D‖ ≤ ‖T‖ / (1 - ‖B‖)
  apply (le_div_iff₀ hpos).mpr
  nlinarith

end DifferentialGeometry.Analysis
