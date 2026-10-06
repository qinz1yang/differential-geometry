import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import DifferentialGeometry.Analysis.Calculus.Derivative.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff Interval

namespace DifferentialGeometry.Analysis

private theorem global_polar_blowup (g : ℂ → ℝ) (hg : ContDiff ℝ ∞ g)
    (a : ℂ) (m : ℕ) (hj : ∀ k < m + 1, iteratedFDeriv ℝ k g a = 0) :
    ∃ W : (ℝ × ℝ) → ℝ, ContDiff ℝ ∞ W ∧
      (∀ r θ : ℝ, g (a + r • Complex.exp ((θ : ℂ) * Complex.I)) =
        r ^ (m + 1) * W (r, θ)) ∧
      (∀ θ : ℝ, W (0, θ) = ((m + 1).factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ (m + 1) g a (fun _ => Complex.exp ((θ : ℂ) * Complex.I))) ∧
      (∀ r : ℝ, Function.Periodic (fun θ => W (r, θ)) (2 * Real.pi)) := by
  let c : ℝ → ℂ := fun θ => Complex.exp ((θ : ℂ) * Complex.I)
  have hc : ContDiff ℝ ∞ c :=
    Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  let f : (ℝ × ℝ) → ℝ → ℝ := fun p t =>
    (1 - t) ^ m * iteratedFDeriv ℝ (m + 1) g (a + t • (p.1 • c p.2))
      (fun _ => c p.2)
  let W : (ℝ × ℝ) → ℝ := fun p => (m.factorial : ℝ)⁻¹ * ∫ t in (0 : ℝ)..1, f p t
  have hd : ContDiff ℝ ∞ (iteratedFDeriv ℝ (m + 1) g) :=
    hg.iteratedFDeriv_right (by simp)
  have heval : ContDiff ℝ ∞ (fun p : (ℂ [×(m + 1)]→L[ℝ] ℝ) × (Fin (m + 1) → ℂ) =>
      p.1 p.2) := by
    exact contDiffOn_univ.mp
      (ContinuousLinearMap.id ℝ (ℂ [×(m + 1)]→L[ℝ] ℝ)).cpolynomialOn_uncurry_of_multilinear.contDiffOn
  have hf : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => f p.1 p.2) := by
    have harg : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => a + p.2 • (p.1.1 • c p.1.2)) := by
      fun_prop
    have hvec : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => fun _ : Fin (m + 1) => c p.1.2) := by
      fun_prop
    exact (by fun_prop : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => (1 - p.2) ^ m)).mul
      (heval.comp ((hd.comp harg).prodMk hvec))
  have hW : ContDiff ℝ ∞ W :=
    contDiff_const.mul (contDiffOn_univ.mp
      (Calculus.contDiffOn_paramIntervalIntegral f hf.contDiffOn))
  refine ⟨W, hW, ?_, ?_, ?_⟩
  · intro r θ
    have ht := map_add_eq_sum_add_integral_iteratedFDeriv
      (f := g) (x := a) (y := r • c θ) (n := m)
      (fun t _ => (hg.of_le (by simp)).contDiffAt)
    have hsum : ∑ k ∈ Finset.range (m + 1), (k.factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ k g a (fun _ => r • c θ) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp [hj k (Finset.mem_range.mp hk)]
    rw [hsum, zero_add] at ht
    have hscale (t : ℝ) :
        iteratedFDeriv ℝ (m + 1) g (a + t • (r • c θ)) (fun _ => r • c θ) =
          r ^ (m + 1) * iteratedFDeriv ℝ (m + 1) g (a + t • (r • c θ)) (fun _ => c θ) := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using
        (iteratedFDeriv ℝ (m + 1) g (a + t • (r • c θ))).map_smul_univ
          (fun _ => r) (fun _ => c θ)
    simp_rw [hscale, smul_eq_mul] at ht
    have hint : (∫ t in (0 : ℝ)..1, (1 - t) ^ m *
        (r ^ (m + 1) * iteratedFDeriv ℝ (m + 1) g (a + t • (r • c θ)) (fun _ => c θ))) =
        r ^ (m + 1) * ∫ t in (0 : ℝ)..1, f (r, θ) t := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      dsimp [f]
      ring
    rw [hint] at ht
    change g (a + r • c θ) = r ^ (m + 1) * W (r, θ)
    rw [ht]
    dsimp [W]
    ring
  · intro θ
    have hint : (∫ t in (0 : ℝ)..1, (1 - t) ^ m) = ((m + 1 : ℕ) : ℝ)⁻¹ := by
      rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ m) 1]
      simp [integral_pow]
    change (m.factorial : ℝ)⁻¹ * (∫ t in (0 : ℝ)..1, f (0, θ) t) = _
    simp only [f, zero_smul, smul_zero, add_zero]
    rw [intervalIntegral.integral_mul_const, hint]
    simp only [Nat.factorial_succ, Nat.cast_mul, smul_eq_mul, mul_inv_rev]
    ring
  · intro r θ
    have hcperiod : c (θ + 2 * Real.pi) = c θ := by
      simpa only [c, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat] using
        Complex.exp_mul_I_periodic (θ : ℂ)
    dsimp [W, f]
    rw [hcperiod]

/-- A smooth function whose lower jets vanish has a smooth signed polar blowup.
The value at radius zero is its centered leading Taylor term, with the exact factorial factor. -/
theorem exists_smooth_polar_blowup_of_vanishing_jets
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {a : ℂ} (ha : a ∈ Ω)
    {n : ℕ} (hn : 1 ≤ n) {v : ℂ → ℝ} (hv : ContDiffOn ℝ ∞ v Ω)
    (hj : ∀ k < n, iteratedFDeriv ℝ k v a = 0) :
    ∃ ε : ℝ, ∃ W : (ℝ × ℝ) → ℝ, 0 < ε ∧ closedBall a ε ⊆ Ω ∧
      ContDiffOn ℝ ∞ W {p : ℝ × ℝ | |p.1| < ε} ∧
      (∀ r θ : ℝ, |r| < ε → v (a + r • Complex.exp ((θ : ℂ) * Complex.I)) =
        r ^ n * W (r, θ)) ∧
      (∀ θ : ℝ, W (0, θ) = (n.factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ n v a (fun _ => Complex.exp ((θ : ℂ) * Complex.I))) ∧
      (∀ r : ℝ, |r| < ε → Function.Periodic (fun θ => W (r, θ)) (2 * Real.pi)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨g, hg, _, hgv⟩ := exists_contDiffOn_cutoff_extension
    (S := (univ : Set ℂ)) hΩ (by simpa only [univ_inter] using hv) ha
  have hgd : ContDiff ℝ ∞ g := contDiffOn_univ.mp hg
  have hgjet (k : ℕ) : iteratedFDeriv ℝ k g a = iteratedFDeriv ℝ k v a :=
    (hgv.iteratedFDeriv ℝ k).self_of_nhds
  obtain ⟨W, hW, heq, hzero, hper⟩ := global_polar_blowup g hgd a m
    (fun k hk => (hgjet k).trans (hj k hk))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hΩ.mem_nhds ha) hgv)
  refine ⟨δ / 2, W, half_pos hδ, ?_, hW.contDiffOn, ?_, ?_, fun r _ => hper r⟩
  · exact (fun z hz => (hball (closedBall_subset_ball (half_lt_self hδ) hz)).1)
  · intro r θ hr
    have hx : a + r • Complex.exp ((θ : ℂ) * Complex.I) ∈ ball a δ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs]
      exact hr.trans (half_lt_self hδ)
    exact (hball hx).2.symm.trans (heq r θ)
  · intro θ
    rw [hzero, hgjet]

end DifferentialGeometry.Analysis
