import DifferentialGeometry.Analysis.Calculus.Inverse.GraphPartialDerivativeBounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {N E : Type*}
  [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isUnit_id_add_and_norm_inverse_le_two
    (B : N →L[ℝ] N) (hB : ‖B‖ ≤ 1 / 2) :
    IsUnit (ContinuousLinearMap.id ℝ N + B) ∧
      ‖Ring.inverse (ContinuousLinearMap.id ℝ N + B)‖ ≤ 2 := by
  have hu : IsUnit (ContinuousLinearMap.id ℝ N + B) := by
    have hn : ‖-B‖ < 1 := by rw [norm_neg]; linarith
    simpa only [sub_neg_eq_add, ContinuousLinearMap.one_def] using
      (isUnit_one_sub_of_norm_lt_one hn)
  refine ⟨hu, ?_⟩
  let V := Ring.inverse (ContinuousLinearMap.id ℝ N + B)
  have hmul : (ContinuousLinearMap.id ℝ N + B) * V = 1 :=
    Ring.mul_inverse_cancel _ hu
  have hsum : V + B * V = 1 := by
    simpa only [add_mul, ← ContinuousLinearMap.one_def, one_mul] using hmul
  have heq : V = 1 - B * V := (eq_sub_iff_add_eq).mpr hsum
  have hOne : ‖(1 : N →L[ℝ] N)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have habsorb : ‖V‖ ≤ 1 + (1 / 2 : ℝ) * ‖V‖ := by
    calc
      ‖V‖ = ‖1 - B * V‖ := congrArg norm heq
      _ ≤ ‖(1 : N →L[ℝ] N)‖ + ‖B * V‖ := norm_sub_le _ _
      _ ≤ 1 + ‖B‖ * ‖V‖ := add_le_add hOne (norm_mul_le B V)
      _ ≤ 1 + (1 / 2 : ℝ) * ‖V‖ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hB (norm_nonneg V))
  change ‖V‖ ≤ 2
  linarith

theorem normal_graph_fderiv_eventually_eq_inverse
    (e : N × E → N) (g : E → N) (x : E)
    (he : ContDiffAt ℝ 1 e (g x, x)) (hg : ContDiffAt ℝ 1 g x)
    (hrel : ∀ᶠ y in 𝓝 x, g y + e (g y, y) = 0)
    (hsmall : ‖fderiv ℝ (fun n : N => e (n, x)) (g x)‖ ≤ 1 / 2) :
    let A : E → N →L[ℝ] N := fun y => ContinuousLinearMap.id ℝ N +
      (fderiv ℝ e (g y, y)).comp (ContinuousLinearMap.inl ℝ N E)
    let B : E → E →L[ℝ] N := fun y =>
      (fderiv ℝ e (g y, y)).comp (ContinuousLinearMap.inr ℝ N E)
    (∀ᶠ y in 𝓝 x, IsUnit (A y)) ∧ ‖Ring.inverse (A x)‖ ≤ 2 ∧
      fderiv ℝ g =ᶠ[𝓝 x] (fun y => -(Ring.inverse (A y)).comp (B y)) := by
  dsimp only
  let A : E → N →L[ℝ] N := fun y => ContinuousLinearMap.id ℝ N +
    (fderiv ℝ e (g y, y)).comp (ContinuousLinearMap.inl ℝ N E)
  let B : E → E →L[ℝ] N := fun y =>
    (fderiv ℝ e (g y, y)).comp (ContinuousLinearMap.inr ℝ N E)
  let J : E → (N × E) →L[ℝ] N := fun y =>
    ContinuousLinearMap.fst ℝ N E + fderiv ℝ e (g y, y)
  have hslice : (fderiv ℝ e (g x, x)).comp (ContinuousLinearMap.inl ℝ N E) =
      fderiv ℝ (fun n : N => e (n, x)) (g x) := by
    exact ((he.differentiableAt (by norm_num)).hasFDerivAt.comp (g x)
      ((hasFDerivAt_id (g x)).prodMk (hasFDerivAt_const x (g x)))).fderiv.symm
  have hunitbound := isUnit_id_add_and_norm_inverse_le_two
    ((fderiv ℝ e (g x, x)).comp (ContinuousLinearMap.inl ℝ N E))
    (by rw [hslice]; exact hsmall)
  have hgraph : ContDiffAt ℝ 1 (fun y => (g y, y)) x := hg.prodMk contDiffAt_id
  have hd : ContDiffAt ℝ 0 (fderiv ℝ e) (g x, x) :=
    he.fderiv_right (by norm_num : (0 : ℕ∞ω) + 1 ≤ 1)
  have hDe : ContDiffAt ℝ 0 (fun y => fderiv ℝ e (g y, y)) x :=
    hd.comp (f := fun y => (g y, y)) x (hgraph.of_le (show (0 : ℕ∞ω) ≤ 1 by norm_num))
  let T : ((N × E) →L[ℝ] N) →L[ℝ] N →L[ℝ] N :=
    (ContinuousLinearMap.compL ℝ N (N × E) N).flip (ContinuousLinearMap.inl ℝ N E)
  have hAc : ContinuousAt A x :=
    (contDiffAt_const.add (T.contDiff.contDiffAt.comp x hDe)).continuousAt
  have hunits : ∀ᶠ y in 𝓝 x, IsUnit (A y) :=
    hAc (Units.isOpen.mem_nhds hunitbound.1)
  refine ⟨hunits, hunitbound.2, ?_⟩
  have hge : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 g y := hg.eventually (by simp)
  have hee : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 e (g y, y) :=
    hgraph.continuousAt (he.eventually (by simp))
  have hJinl (y : E) : (J y).comp (ContinuousLinearMap.inl ℝ N E) = A y := by
    ext v
    simp [J, A, ContinuousLinearMap.comp_apply]
  have hJinr (y : E) : (J y).comp (ContinuousLinearMap.inr ℝ N E) = B y := by
    ext v
    simp [J, B, ContinuousLinearMap.comp_apply]
  have hform := implicit_fderiv_eventually_eq
    (fun n : N => fun y : E => n + e (n, y)) g x (fderiv ℝ g) J
    (by
      filter_upwards [hge] with y hy
      exact (hy.differentiableAt (by norm_num)).hasFDerivAt)
    (by
      filter_upwards [hee] with y hy
      exact (ContinuousLinearMap.fst ℝ N E).hasFDerivAt.add
        (hy.differentiableAt (by norm_num)).hasFDerivAt)
    hrel (by
      filter_upwards [hunits] with y hy
      rw [hJinl]
      exact hy)
  filter_upwards [hform] with y hy
  simpa only [hJinl, hJinr] using hy

end DifferentialGeometry.Analysis
