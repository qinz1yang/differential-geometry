import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace DifferentialGeometry.Analysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}

private def iteratedDerivOnInterval (hf : ContDiff ℝ ∞ f) (j : ℕ) (a b : ℝ) :
    C(Icc a b, F) :=
  ⟨fun x => iteratedDeriv j f x,
    (hf.continuous_iteratedDeriv j
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).comp continuous_subtype_val⟩

def intervalDerivativeNorm (hf : ContDiff ℝ ∞ f) (m : ℕ) (a b : ℝ) : ℝ :=
  ∑ j : Fin (m + 1), ‖iteratedDerivOnInterval hf j a b‖

theorem intervalDerivativeNorm_nonneg (hf : ContDiff ℝ ∞ f) (m : ℕ) (a b : ℝ) :
    0 ≤ intervalDerivativeNorm hf m a b :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem norm_iteratedDeriv_le_intervalDerivativeNorm (hf : ContDiff ℝ ∞ f)
    {m j : ℕ} (hj : j ≤ m) {a b x : ℝ} (hx : x ∈ Icc a b) :
    ‖iteratedDeriv j f x‖ ≤ intervalDerivativeNorm hf m a b := by
  calc
    _ ≤ ‖iteratedDerivOnInterval hf j a b‖ :=
      ContinuousMap.norm_coe_le_norm _ ⟨x, hx⟩
    _ ≤ _ := by
      have h := Finset.single_le_sum
        (f := fun k : Fin (m + 1) => ‖iteratedDerivOnInterval hf k a b‖)
        (a := ⟨j, Nat.lt_succ_iff.mpr hj⟩) (s := Finset.univ)
        (fun k _ => norm_nonneg _) (Finset.mem_univ _)
      exact h

theorem intervalDerivativeNorm_le (hf : ContDiff ℝ ∞ f) (m : ℕ) (a b : ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ j ≤ m, ∀ x ∈ Icc a b, ‖iteratedDeriv j f x‖ ≤ C) :
    intervalDerivativeNorm hf m a b ≤ (m + 1 : ℕ) * C := by
  calc
    _ ≤ ∑ _j : Fin (m + 1), C := by
      apply Finset.sum_le_sum
      intro j _
      apply (ContinuousMap.norm_le _ hC).mpr
      intro x
      exact hbound j (Nat.lt_succ_iff.mp j.isLt) x x.property
    _ = _ := by simp

theorem exists_pos_intervalDerivativeNorm_lt (hf : ContDiff ℝ ∞ f) (m : ℕ) (x : ℝ)
    (hzero : ∀ j ≤ m, iteratedDeriv j f x = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : ℝ, 0 ≤ A → A ≤ δ →
      intervalDerivativeNorm hf m (x - A) x < ε := by
  let C : ℝ := ε / (2 * (m + 1 : ℕ))
  have hm : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hC : 0 < C := div_pos hε (mul_pos (by norm_num) hm)
  have hev : ∀ᶠ y in 𝓝 x, ∀ j : Fin (m + 1), ‖iteratedDeriv j f y‖ < C := by
    apply eventually_all.mpr
    intro j
    have hc : ContinuousAt (fun y => ‖iteratedDeriv j f y‖) x :=
      (hf.continuous_iteratedDeriv j
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).norm.continuousAt
    apply hc.eventually_lt_const
    simpa only [hzero j (Nat.lt_succ_iff.mp j.isLt), norm_zero] using hC
  obtain ⟨d, hd, hnear⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨d / 2, half_pos hd, fun A hA hAd => ?_⟩
  have hbound : ∀ j ≤ m, ∀ y ∈ Icc (x - A) x, ‖iteratedDeriv j f y‖ ≤ C := by
    intro j hj y hy
    apply (hnear (y := y) ?_ ⟨j, Nat.lt_succ_iff.mpr hj⟩).le
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hy.2)]
    linarith [hy.1]
  apply (intervalDerivativeNorm_le hf m (x - A) x hC.le hbound).trans_lt
  dsimp only [C]
  have heq : (m + 1 : ℕ) * (ε / (2 * (m + 1 : ℕ))) = ε / 2 := by field_simp
  rw [heq]
  exact half_lt_self hε

end DifferentialGeometry.Analysis
