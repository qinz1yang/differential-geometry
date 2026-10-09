import DifferentialGeometry.Analysis.Calculus.Inverse.GraphPartialDerivativeBounds
import DifferentialGeometry.Analysis.Calculus.Inverse.GraphImplicitSuccessor
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

variable {N E : Type*}
  [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [CompleteSpace N] in
private theorem graph_partial_uniform_envelope
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : N × E → N) (g : E → N) (x : E) (m : ℕ)
    (he : ContDiffAt ℝ (m + 1 : ℕ) e (g x, x))
    (hg : ContDiffAt ℝ (m + 1 : ℕ) g x)
    (C D δ : ℝ) (hC0 : 0 ≤ C) (hD1 : 1 ≤ D) (hδ0 : 0 ≤ δ)
    (hC : ∀ i, 1 ≤ i → i ≤ m + 1 →
      ‖iteratedFDeriv ℝ i e (g x, x)‖ ≤ C * δ)
    (hD : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i g x‖ ≤ D ^ i)
    (L : V →L[ℝ] N × E) (hL : ‖L‖ ≤ 1) (i : ℕ) (hi : i ≤ m) :
    ‖iteratedFDeriv ℝ i (fun y => (fderiv ℝ e (g y, y)).comp L) x‖ ≤
      ((m.factorial : ℝ) * C * D ^ m) * δ := by
  have h := norm_iteratedFDeriv_partial_along_graph_le
    (N := N) (E := E) (F := N) (K := V) e g x i L hL (C * δ) D
    (he.of_le (by exact_mod_cast (Nat.add_le_add_right hi 1)))
    (hg.of_le (by exact_mod_cast (hi.trans (Nat.le_succ m))))
    (fun j hj hji => hC j hj (hji.trans (Nat.add_le_add_right hi 1)))
    (fun j hj hji => hD j hj (hji.trans hi)) hD1
  apply h.trans
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  have hfac : (i.factorial : ℝ) ≤ (m.factorial : ℝ) :=
    Nat.cast_le.mpr (Nat.factorial_le hi)
  have hpow : D ^ i ≤ D ^ m := pow_le_pow_right₀ hD1 hi
  calc
    (i.factorial : ℝ) * (C * δ) * D ^ i ≤
        (m.factorial : ℝ) * (C * δ) * D ^ m := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hfac (mul_nonneg hC0 hδ0)) hpow
        (pow_nonneg hD0 _) (by positivity)
    _ = ((m.factorial : ℝ) * C * D ^ m) * δ := by ring

theorem norm_iteratedFDeriv_normal_graph_succ_le
    (e : N × E → N) (g : E → N) (x : E) (m : ℕ)
    (he : ContDiffAt ℝ (m + 1 : ℕ) e (g x, x))
    (hg : ContDiffAt ℝ (m + 1 : ℕ) g x)
    (hrel : ∀ᶠ y in 𝓝 x, g y + e (g y, y) = 0)
    (hsmall : ‖fderiv ℝ (fun n : N => e (n, x)) (g x)‖ ≤ 1 / 2)
    (C D δ : ℝ) (hC0 : 0 ≤ C) (hD1 : 1 ≤ D) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hC : ∀ i, 1 ≤ i → i ≤ m + 1 →
      ‖iteratedFDeriv ℝ i e (g x, x)‖ ≤ C * δ)
    (hD : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i g x‖ ≤ D ^ i) :
    let K : ℝ := (m.factorial : ℝ) * C * D ^ m
    ‖iteratedFDeriv ℝ (m + 1) g x‖ ≤
      ((2 : ℝ) ^ m * ((m.factorial : ℝ) *
        ((m.factorial : ℝ) * (2 : ℝ) ^ (m + 1)) * (max K 1) ^ m) * K) * δ := by
  dsimp only
  let K : ℝ := (m.factorial : ℝ) * C * D ^ m
  let a : E → N →L[ℝ] N := fun y =>
    (fderiv ℝ e (g y, y)).comp (ContinuousLinearMap.inl ℝ N E)
  let A : E → N →L[ℝ] N := fun y => ContinuousLinearMap.id ℝ N + a y
  let B : E → E →L[ℝ] N := fun y =>
    (fderiv ℝ e (g y, y)).comp (ContinuousLinearMap.inr ℝ N E)
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hDA1 : 1 ≤ max K 1 := le_max_right _ _
  have hregular : ContDiffAt ℝ m (fun y => fderiv ℝ e (g y, y)) x := by
    have hd : ContDiffAt ℝ m (fderiv ℝ e) (g x, x) :=
      he.fderiv_right (by exact_mod_cast (le_refl (m + 1)))
    exact hd.comp (f := fun y => (g y, y)) x
      ((hg.of_le (by exact_mod_cast (Nat.le_succ m))).prodMk contDiffAt_id)
  let LN : ((N × E) →L[ℝ] N) →L[ℝ] N →L[ℝ] N :=
    (ContinuousLinearMap.compL ℝ N (N × E) N).flip (ContinuousLinearMap.inl ℝ N E)
  let LE : ((N × E) →L[ℝ] N) →L[ℝ] E →L[ℝ] N :=
    (ContinuousLinearMap.compL ℝ E (N × E) N).flip (ContinuousLinearMap.inr ℝ N E)
  have ha : ContDiffAt ℝ m a x := LN.contDiff.contDiffAt.comp x hregular
  have hA : ContDiffAt ℝ m A x := contDiffAt_const.add ha
  have hB : ContDiffAt ℝ m B x := LE.contDiff.contDiffAt.comp x hregular
  have hnormaljets (i : ℕ) (hi : i ≤ m) :
      ‖iteratedFDeriv ℝ i a x‖ ≤ K * δ := by
    change ‖iteratedFDeriv ℝ i
      (fun y => (fderiv ℝ e (g y, y)).comp (ContinuousLinearMap.inl ℝ N E)) x‖ ≤
        ((m.factorial : ℝ) * C * D ^ m) * δ
    exact graph_partial_uniform_envelope (N := N) (E := E) (V := N)
      e g x m he hg C D δ hC0 hD1 hδ0 hC hD
      (ContinuousLinearMap.inl ℝ N E) (ContinuousLinearMap.norm_inl_le_one ℝ N E) i hi
  have hBjets (i : ℕ) (hi : i ≤ m) : ‖iteratedFDeriv ℝ i B x‖ ≤ K * δ := by
    change ‖iteratedFDeriv ℝ i
      (fun y => (fderiv ℝ e (g y, y)).comp (ContinuousLinearMap.inr ℝ N E)) x‖ ≤
        ((m.factorial : ℝ) * C * D ^ m) * δ
    exact graph_partial_uniform_envelope (N := N) (E := E) (V := E)
      e g x m he hg C D δ hC0 hD1 hδ0 hC hD
      (ContinuousLinearMap.inr ℝ N E) (ContinuousLinearMap.norm_inr_le_one ℝ N E) i hi
  have hAjets (i : ℕ) (hi : 1 ≤ i) (him : i ≤ m) :
      ‖iteratedFDeriv ℝ i A x‖ ≤ (max K 1) ^ i := by
    have hidentity : iteratedFDeriv ℝ i A x = iteratedFDeriv ℝ i a x := by
      change iteratedFDeriv ℝ i (fun y => ContinuousLinearMap.id ℝ N + a y) x = _
      rw [fun_iteratedFDeriv_add_apply contDiffAt_const
        (ha.of_le (by exact_mod_cast him)),
        iteratedFDeriv_const_of_ne (by omega : i ≠ 0), Pi.zero_apply, zero_add]
    rw [hidentity]
    calc
      ‖iteratedFDeriv ℝ i a x‖ ≤ K * δ :=
        hnormaljets i him
      _ ≤ K := (mul_le_mul_of_nonneg_left hδ1 hK0).trans_eq (mul_one K)
      _ ≤ max K 1 := le_max_left _ _
      _ = (max K 1) ^ 1 := (pow_one _).symm
      _ ≤ (max K 1) ^ i := pow_le_pow_right₀ hDA1 hi
  have hactual := normal_graph_fderiv_eventually_eq_inverse e g x
    (he.of_le (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m))))
    (hg.of_le (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le m)))) hrel hsmall
  have hunits : ∀ᶠ y in 𝓝 x, IsUnit (A y) := hactual.1
  have hinverse : ‖Ring.inverse (A x)‖ ≤ 2 := hactual.2.1
  have hformula : fderiv ℝ g =ᶠ[𝓝 x]
      (fun y => -(Ring.inverse (A y)).comp (B y)) := hactual.2.2
  have h := norm_iteratedFDeriv_implicit_succ_le g A B x m 2 (max K 1) (K * δ)
    hformula hA hB hunits hinverse (zero_le_one.trans hDA1) hAjets hBjets
  simpa only [K, show max (2 : ℝ) 1 = 2 by norm_num, max_eq_left hDA1, max_assoc, max_self, mul_assoc] using h

end DifferentialGeometry.Analysis
