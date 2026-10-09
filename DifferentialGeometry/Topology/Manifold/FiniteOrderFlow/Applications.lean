import DifferentialGeometry.Topology.Manifold.FiniteOrderFlow.Euclidean
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Concrete consumers of the finite-order flow: moving a point on the line

A point moving along a `C^{m+1}` path `c` with `|c t| < 1` is the fibre `f_t ⁻¹' {0}` of
`f_t(x) = x - c t`. The time-lifting field `V t x = c'(t) b(x)`, with a smooth bump `b = 1` on
`[-1, 1]` and supported in `[-2, 2]`, is only jointly `C^m` (one derivative is lost, as in
LFR03's `C^r → C^{r-1}`), satisfies `DF (1, V) = 0` on the strip `|x| < 1` around the trace, and
its flow is a compactly supported `C^m` isotopy of `ℝ` carrying `c s` to `c t`. The instance
`c t = sin t / 2` is fully explicit.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.ODE

/-- **Moving a point by a compactly supported finite-order isotopy.** For a `C^{m+1}` path
`c : ℝ → ℝ` (`1 ≤ m`) with `|c t| < 1`, there is a family of `C^m` diffeomorphisms `Φ s t` of `ℝ`,
jointly `C^m`, with `Φ s s = id`, equal to the identity on `|x| > 2`, and `Φ s t (c s) = c t`. -/
theorem exists_isotopy_moving_point_Ck {m : ℕ} (hm : 1 ≤ m) {c : ℝ → ℝ}
    (hc : ContDiff ℝ (m + 1) c) (hc1 : ∀ t, |c t| < 1) :
    ∃ Φ : ℝ → ℝ → ℝ ≃ₘ^m⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ,
      ContDiff ℝ m (fun q : (ℝ × ℝ) × ℝ => Φ q.1.1 q.1.2 q.2) ∧
      (∀ s, Φ s s = Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ m) ∧
      (∀ s t x, 2 < |x| → Φ s t x = x) ∧
      ∀ s t, Φ s t (c s) = c t := by
  obtain ⟨hcd, -, hdc⟩ := contDiff_succ_iff_deriv.1 hc
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let V : ℝ → ℝ → ℝ := fun t x => deriv c t * b x
  have hV : ContDiff ℝ m (fun q : ℝ × ℝ => V q.1 q.2) :=
    (hdc.comp contDiff_fst).mul (b.contDiff.comp contDiff_snd)
  have hsupp : ∀ t x, x ∉ closedBall (0 : ℝ) 2 → V t x = 0 := by
    intro t x hx
    have hx' : b.rOut ≤ dist x 0 := le_of_lt (not_le.1 (by simpa [mem_closedBall] using hx))
    simp only [V, b.zero_of_le_dist hx', mul_zero]
  let F : ℝ × ℝ → ℝ := fun p => p.2 - c p.1
  have hFc : Continuous F := continuous_snd.sub (hcd.continuous.comp continuous_fst)
  let O : Set (ℝ × ℝ) := {p | |p.2| < 1}
  have hO : IsOpen O := isOpen_lt (continuous_abs.comp continuous_snd) continuous_const
  have hXO : F ⁻¹' {0} ⊆ O := by
    intro p hp
    have hp' : p.2 = c p.1 := sub_eq_zero.1 hp
    change |p.2| < 1
    rw [hp']
    exact hc1 p.1
  have hFd : ∀ p : ℝ × ℝ, HasFDerivAt F
      (ContinuousLinearMap.snd ℝ ℝ ℝ - deriv c p.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    fun p => (hasFDerivAt_snd).sub
      ((hcd p.1).hasDerivAt.comp_hasFDerivAt p hasFDerivAt_fst)
  have htransport : ∀ p ∈ O, fderiv ℝ F p ((1 : ℝ), V p.1 p.2) = 0 := by
    intro p hp
    have hb : b p.2 = 1 := b.one_of_mem_closedBall (by
      simpa [mem_closedBall, Real.dist_eq] using (le_of_lt hp : |p.2| ≤ 1))
    rw [(hFd p).fderiv]
    simp [V, hb]
  obtain ⟨Φ, hΦ, hself, hid, hval, -⟩ :=
    exists_compactSupport_isotopy_fibre_Ck_euclidean hm hV (isCompact_closedBall 0 2) hsupp hFc
      hO hXO (fun p _ => (hFd p).differentiableAt) htransport
  refine ⟨Φ, hΦ, hself, fun s t x hx => hid s t x ?_, fun s t => ?_⟩
  · simpa [mem_closedBall, Real.dist_eq] using hx
  · have h := hval s t (c s) (by simp [F])
    have h0 : F (s, c s) = 0 := by simp [F]
    rw [h0] at h
    exact sub_eq_zero.1 h

/-- **The explicit instance** `c t = sin t / 2`: for every `m ≥ 1` a compactly supported jointly
`C^m` isotopy of `ℝ`, the identity on `|x| > 2`, carries `sin s / 2` to `sin t / 2`. -/
theorem exists_isotopy_moving_sin_half {m : ℕ} (hm : 1 ≤ m) :
    ∃ Φ : ℝ → ℝ → ℝ ≃ₘ^m⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ,
      ContDiff ℝ m (fun q : (ℝ × ℝ) × ℝ => Φ q.1.1 q.1.2 q.2) ∧
      (∀ s, Φ s s = Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ m) ∧
      (∀ s t x, 2 < |x| → Φ s t x = x) ∧
      ∀ s t, Φ s t (Real.sin s / 2) = Real.sin t / 2 := by
  refine exists_isotopy_moving_point_Ck hm ((Real.contDiff_sin.div_const 2).of_le le_top)
    fun t => ?_
  rw [abs_div, abs_two]
  linarith [Real.abs_sin_le_one t]

end DifferentialGeometry.Analysis.ODE
