import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalBall
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import DifferentialGeometry.Geometry.Metric.Distance.MetricLocality

/-!
# Whole-ball Shi estimates by recentring (chapters 9–10, adapter A11a)

The terminal Shi estimate `shi_curvDerivNorm_terminal_of_terminal_ball`
(`Estimates/Shi/Derivatives/TerminalBall.lean`) bounds the derivatives of the curvature at the
centre of a compact closed ball.  Recentring it at every point `q` of the ball `B(p, s)`, on the
closed ball `B̄(q, s/2) ⊆ B̄(p, 3s/2)` (closed in the compact `B̄(p, 3s/2)`), with the left end
`a' = t - τ s²/2`, the constant `K = C₀/s²` and the radius `R = s/2`, gives a bound on the whole
ball whose constant does not depend on `q` (the ratio `β = 1/2` is uniform).

Only `Ioo` regularity on the original window is used: after the shift, `Ico a' t ⊆ Ioo (t - τ s²) t`.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace FILL910

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.CheegerGromovCompactness

section Shi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- The constant bookkeeping of A11a: the terminal Shi constant with `K = C₀/s²`,
`b - a = τ s²/2` and `R = s/2` is the scale-free coefficient times `s^{-(m+2)}`. -/
theorem shiLocalUniformBound_recentred_eq (n m : ℕ) {τ s C₀ : ℝ} (hτ : 0 < τ) (hs : 0 < s) :
    shiLocalUniformBound n m (C₀ / s ^ 2 * (τ * s ^ 2 / 2))
        (s / 2 * Real.sqrt (C₀ / s ^ 2) /
          (4 * Real.exp ((n : ℝ) ^ 2 * (C₀ / s ^ 2) * (τ * s ^ 2 / 2)))) *
        (C₀ / s ^ 2) / Real.sqrt (τ * s ^ 2 / 2) ^ m =
      shiLocalUniformBound n m (C₀ * τ / 2)
          (Real.sqrt C₀ / (8 * Real.exp ((n : ℝ) ^ 2 * (C₀ * τ / 2)))) *
        C₀ / Real.sqrt (τ / 2) ^ m / s ^ (m + 2) := by
  have hs0 : s ≠ 0 := hs.ne'
  have e1 : C₀ / s ^ 2 * (τ * s ^ 2 / 2) = C₀ * τ / 2 := by
    field_simp
  have e2 : s / 2 * Real.sqrt (C₀ / s ^ 2) = Real.sqrt C₀ / 2 := by
    rw [Real.sqrt_div' C₀ (sq_nonneg s), Real.sqrt_sq hs.le]
    field_simp
  have e3 : (n : ℝ) ^ 2 * (C₀ / s ^ 2) * (τ * s ^ 2 / 2) = (n : ℝ) ^ 2 * (C₀ * τ / 2) := by
    rw [mul_assoc, e1]
  have e4 : Real.sqrt (τ * s ^ 2 / 2) = Real.sqrt (τ / 2) * s := by
    rw [show τ * s ^ 2 / 2 = τ / 2 * s ^ 2 by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hs.le]
  have e5 : Real.sqrt C₀ / 2 / (4 * Real.exp ((n : ℝ) ^ 2 * (C₀ * τ / 2))) =
      Real.sqrt C₀ / (8 * Real.exp ((n : ℝ) ^ 2 * (C₀ * τ / 2))) := by
    rw [div_div]
    ring
  have hq : 0 < Real.sqrt (τ / 2) := Real.sqrt_pos.mpr (by positivity)
  rw [e1, e2, e3, e4, e5, mul_pow]
  field_simp
  ring

/-- A11a (I11, M): whole-ball Shi by recentring with the uniform ratio `β = 1/2`.
For `q ∈ B(p, s)` apply `shi_curvDerivNorm_terminal_of_terminal_ball` on the closed ball
`B̄_{g(t)}(q, s/2) ⊆ B̄_{g(t)}(p, 3s/2)` (closed in a compact set), with left end
`a' = t - τ s²/2`, `K = C₀/s²` and `b - a' = τ s²/2`.  The constant does not depend on `q`. -/
theorem A11a_shi_whole_ball_of_uniform_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {t τ s C₀ : ℝ} (hτ : 0 < τ) (hs : 0 < s) (hC₀ : 0 < C₀)
    (hcarrier : Icc (t - τ * s ^ 2) t ⊆ D.carrier)
    (hregular : Ioo (t - τ * s ^ 2) t ⊆ D.regular)
    (p : M) (hcompact : IsCompact (riemannianClosedBallOf (S.base.metric t) p (3 * s / 2)))
    (hcurv : ∀ u ∈ Icc (t - τ * s ^ 2) t,
      ∀ y ∈ riemannianClosedBallOf (S.base.metric t) p (3 * s / 2),
        curvDerivNormSq (I := I) 0 (S.base.metric u) y ≤ (C₀ / s ^ 2) ^ 2)
    (m : ℕ) :
    ∀ q ∈ riemannianBallOf (S.base.metric t) p s,
      curvDerivNorm (I := I) m (S.base.metric t) q ≤
        shiLocalUniformBound (Module.finrank ℝ E) m (C₀ * τ / 2)
            (Real.sqrt C₀ / (8 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * (C₀ * τ / 2)))) *
          C₀ / Real.sqrt (τ / 2) ^ m / s ^ (m + 2) := by
  intro q hq
  have hs2 : 0 < τ * s ^ 2 := by positivity
  have hlt : t - τ * s ^ 2 / 2 < t := by linarith
  have hK : 0 < C₀ / s ^ 2 := by positivity
  have hR : 0 < s / 2 := by positivity
  have hsub : riemannianClosedBallOf (S.base.metric t) q (s / 2) ⊆
      riemannianClosedBallOf (S.base.metric t) p (3 * s / 2) :=
    riemannianClosedBallOf_subset_of_add_radius_le _ hs.le hR.le (by linarith)
      (show riemannianEDistOf (S.base.metric t) p q ≤ ENNReal.ofReal s from le_of_lt hq)
  have hcpt : IsCompact (riemannianClosedBallOf (S.base.metric t) q (s / 2)) :=
    hcompact.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _) hsub
  have hIcc : Icc (t - τ * s ^ 2 / 2) t ⊆ Icc (t - τ * s ^ 2) t :=
    Icc_subset_Icc (by linarith) le_rfl
  have h := shi_curvDerivNorm_terminal_of_terminal_ball S hS hlt hK hR (hIcc.trans hcarrier)
    (fun u hu => hregular ⟨by linarith [hu.1], hu.2⟩) q hcpt
    (fun u hu y hy => hcurv u (hIcc hu) y (hsub hy)) m
  have hba : t - (t - τ * s ^ 2 / 2) = τ * s ^ 2 / 2 := by ring
  rw [hba, shiLocalUniformBound_recentred_eq _ m hτ hs] at h
  exact h

end Shi

end FILL910
