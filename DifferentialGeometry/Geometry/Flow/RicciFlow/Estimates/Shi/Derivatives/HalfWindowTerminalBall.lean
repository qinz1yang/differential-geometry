import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.TerminalBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LaplacianInputRegularWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Background

/-!
# Half-window jets at a centre (chapters 9–10, A13b item L1/L1′)

`shi_curvDerivNorm_on_terminal_ball` (`TerminalBall.lean:373`) bounds every derivative of the
curvature on the half window `[(a+b)/2, b]` and on the terminal ball of radius `R/4`.  Taking
`a = b − τ`, `R = r₀` and evaluating at the centre gives:

* `FILL910.shi_curvDerivNorm_half_window`: the bound at the centre `x` on `[b − τ/2, b]`, with the
  constant of `:373` (internal time `τ/4`, radius `r₀/(4 exp(n² K τ))`);
* `FILL910.exists_half_window_curvDerivNorm_bound`: in dimension three, on the window `[−τ, 0]`, one
  bound per order that depends only on `τ`, `K` and `r₀` (not on the manifold, the flow or the centre);
  `K` has no sign condition (the proof uses `|K| + 1`).

No comparison of the metrics at different times and no curvature sign are used: the only inputs are
the curvature bound on the terminal ball for all times of the window and the compactness of that
ball.  This is the `hjets` route of A13b
(`docs/geometrization/chapter13/design-a13b-fixed-scale-flow-limit-20261004.md` §0.3, §5).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace FILL910

universe u

open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

section HalfWindow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

/-- L1.  Curvature bound `K` on `[b - τ, b] × B̄_{g(b)}(x, r₀)` and a compact terminal ball give
every-order jets at the centre `x` on the half window `[b - τ/2, b]`.  Internal time `τ/4`, radius
`r₀/(4L)` with `L = exp(n² K τ)`, exactly as in `:373`. -/
theorem shi_curvDerivNorm_half_window
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b τ K r₀ : ℝ} (hτ : 0 < τ) (hK : 0 < K) (hr₀ : 0 < r₀)
    (hcarrier : Icc (b - τ) b ⊆ D.carrier) (hregular : Ioo (b - τ) b ⊆ D.regular)
    (x : M) (hcompact : IsCompact (riemannianClosedBallOf (S.base.metric b) x r₀))
    (hcurv : ∀ s ∈ Icc (b - τ) b, ∀ y ∈ riemannianClosedBallOf (S.base.metric b) x r₀,
      curvDerivNormSq (I := I) 0 (S.base.metric s) y ≤ K ^ 2) (m : ℕ) :
    ∀ s ∈ Icc (b - τ / 2) b,
      curvDerivNorm (I := I) m (S.base.metric s) x ≤
        shiLocalUniformBound (Module.finrank ℝ E) m (K * (τ / 4))
            ((r₀ / (4 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * τ))) * Real.sqrt K /
              (4 * Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * K * (τ / 4)))) *
          K / Real.sqrt (τ / 4) ^ m := by
  intro s hs
  have hab : b - τ < b := by linarith
  have key := shi_curvDerivNorm_on_terminal_ball S hS (a := b - τ) (b := b) hab hK hr₀
    hcarrier hregular x hcompact hcurv
  dsimp only at key
  have h1 : b - (b - τ) = τ := by ring
  have h2 : (b - τ + b) / 2 = b - τ / 2 := by ring
  have hx : x ∈ riemannianClosedBallOf (S.base.metric b) x (r₀ / 4) := by
    rw [riemannianClosedBallOf, mem_ofPred_eq, riemannianEDistOf_self]
    exact bot_le
  have hb := key m s (by rw [h2]; exact hs) x hx
  rw [h1] at hb
  exact hb

end HalfWindow

/-- L1′.  One bound per order, uniform in the manifold, the flow on `[-τ, 0]` and the centre.  `K` has
no sign condition (the proof uses `|K| + 1`). -/
theorem exists_half_window_curvDerivNorm_bound {τ K r₀ : ℝ} (hτ : 0 < τ) (hr₀ : 0 < r₀) :
    ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
        (g : ℝ → SmoothRiemannianMetric ThreeModel M),
        IsSolutionOn ({ base.metric := g } : SolutionOn (I := ThreeModel) (M := M)
          (RealTimeInterval.closed (-τ) 0 (neg_nonpos.mpr hτ.le))) →
        ∀ x : M, IsCompact (riemannianClosedBallOf (g 0) x r₀) →
        (∀ s ∈ Icc (-τ) 0, ∀ y ∈ riemannianClosedBallOf (g 0) x r₀,
          curvDerivNormSq 0 (g s) y ≤ K ^ 2) →
        ∀ m : ℕ, ∀ s ∈ Icc (-(τ / 2)) 0, curvDerivNorm m (g s) x ≤ B m := by
  have hK' : 0 < |K| + 1 := by positivity
  refine ⟨fun m => shiLocalUniformBound (Module.finrank ℝ ThreeSpace) m ((|K| + 1) * (τ / 4))
      ((r₀ / (4 * Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * (|K| + 1) * τ))) *
          Real.sqrt (|K| + 1) /
        (4 * Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * (|K| + 1) * (τ / 4)))) *
      (|K| + 1) / Real.sqrt (τ / 4) ^ m, fun m => ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (shiLocalUniformBound_nonneg _ _ _ _) hK'.le)
      (pow_nonneg (Real.sqrt_nonneg _) _)
  intro M _ _ _ _ _ g hsol x hcompact hcurv m s hs
  have hKK : K ^ 2 ≤ (|K| + 1) ^ 2 := by
    rw [← sq_abs K]
    exact pow_le_pow_left₀ (abs_nonneg K) (by linarith) 2
  have h0 : (0 : ℝ) - τ = -τ := by ring
  exact shi_curvDerivNorm_half_window ({ base.metric := g } :
      SolutionOn (I := ThreeModel) (M := M)
        (RealTimeInterval.closed (-τ) 0 (neg_nonpos.mpr hτ.le))) hsol (b := 0) hτ hK' hr₀
    (fun v hv => ⟨by linarith [hv.1], hv.2⟩) (fun v hv => ⟨by linarith [hv.1], hv.2⟩) x
    hcompact (fun v hv y hy => (hcurv v ⟨by linarith [hv.1], hv.2⟩ y hy).trans hKK) m s
    ⟨by linarith [hs.1], hs.2⟩

end FILL910
