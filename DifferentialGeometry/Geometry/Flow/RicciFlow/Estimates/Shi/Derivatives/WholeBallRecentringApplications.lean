import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.WholeBallRecentring

/-!
# Consumer of A11a: one constant for all orders up to `N`

The consumer side of I11 (design §(c) I11, step 6): a finite budget of derivative orders
`m ≤ N` is controlled by one constant `B`, chosen from `(N, τ, C₀)` and the dimension before the
flow, the window, the centre and the scale.  It is the sum of the A11a coefficients.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff ENNReal

namespace FILL910

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- Whole-ball Shi for all orders `m ≤ N` with one constant, chosen before the flow. -/
theorem exists_shi_whole_ball_bound_of_order_le (N : ℕ) {τ C₀ : ℝ} (hτ : 0 < τ)
    (hC₀ : 0 < C₀) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D), IsSolutionOn S →
      ∀ {t s : ℝ}, 0 < s →
      Icc (t - τ * s ^ 2) t ⊆ D.carrier → Ioo (t - τ * s ^ 2) t ⊆ D.regular →
      ∀ p : M, IsCompact (riemannianClosedBallOf (S.base.metric t) p (3 * s / 2)) →
      (∀ u ∈ Icc (t - τ * s ^ 2) t,
        ∀ y ∈ riemannianClosedBallOf (S.base.metric t) p (3 * s / 2),
          curvDerivNormSq (I := I) 0 (S.base.metric u) y ≤ (C₀ / s ^ 2) ^ 2) →
      ∀ m ≤ N, ∀ q ∈ riemannianBallOf (S.base.metric t) p s,
        curvDerivNorm (I := I) m (S.base.metric t) q ≤ B / s ^ (m + 2) := by
  let c : ℕ → ℝ := fun m =>
    shiLocalUniformBound (Module.finrank ℝ E) m (C₀ * τ / 2)
        (Real.sqrt C₀ / (8 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * (C₀ * τ / 2)))) *
      C₀ / Real.sqrt (τ / 2) ^ m
  have hc : ∀ m, 0 ≤ c m := fun m =>
    div_nonneg (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hC₀.le)
      (pow_nonneg (Real.sqrt_nonneg _) _)
  refine ⟨∑ i ∈ Finset.range (N + 1), c i, Finset.sum_nonneg fun i _ => hc i, ?_⟩
  intro D S hS t s hs hcarrier hregular p hcompact hcurv m hm q hq
  have h := A11a_shi_whole_ball_of_uniform_bound S hS hτ hs hC₀ hcarrier hregular p hcompact
    hcurv m q hq
  have hle : c m ≤ ∑ i ∈ Finset.range (N + 1), c i :=
    Finset.single_le_sum (fun i _ => hc i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  exact h.trans (div_le_div_of_nonneg_right hle (by positivity))

end FILL910
