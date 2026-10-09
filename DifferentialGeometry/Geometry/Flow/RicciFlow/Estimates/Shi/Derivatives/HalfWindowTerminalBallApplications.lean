import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.HalfWindowTerminalBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionShiWholeBall

/-!
# Half-window jets on a ball of an open subset (consumer of L1′; the `hjets` step of A13b)

A flow `h` on an open set `W` of a compact three-manifold, on the window `[−τ, 0]`, with
`h 0 = g.restrictOpen W` and `|Rm| ≤ K` on all of `W`, has every-order jets on the half window
`[−τ/2, 0]` at every point of `W` whose ambient distance to `y` is at most `ρ`, provided the ambient
closed ball `B̄_g(y, ρ + 1)` lies in `W`.  The bound depends only on `τ` and `K`.

Proof: recentring at each point `x` with radius `1`.  The intrinsic closed ball `B̄_{h 0}(x, 1)` is
compact because the ambient one lies in `W` (`isCompact_riemannianClosedBallOf_restrictOpen_of_subset`,
lifting + closedness), then `exists_half_window_curvDerivNorm_bound` with `r₀ = 1`.  In A13b this is
applied with `W = W k n = B(y n, k + 3)`, `ρ = k + 1`, `τ = τ k`, `K = K k`
(`docs/geometrization/chapter13/design-a13b-fixed-scale-flow-limit-20261004.md` §5).
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace FILL910

universe u

open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

/-- The `hjets` shape of A13b: half-window jets on the ambient ball `B̄_g(y, ρ)` for a flow on an open
set `W ⊇ B̄_g(y, ρ + 1)` of a compact three-manifold, uniformly in the manifold, the flow and `y`. -/
theorem exists_half_window_curvDerivNorm_bound_on_ball {τ K ρ : ℝ} (hτ : 0 < τ) (hρ : 0 ≤ ρ) :
    ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧
      ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold ThreeModel ∞ M] [T2Space M] [CompactSpace M]
        (g : SmoothRiemannianMetric ThreeModel M) (W : Opens M)
        (h : ℝ → SmoothRiemannianMetric ThreeModel W) (y : M),
        IsSolutionOn ({ base.metric := h } : SolutionOn (I := ThreeModel) (M := W)
          (RealTimeInterval.closed (-τ) 0 (neg_nonpos.mpr hτ.le))) →
        h 0 = g.restrictOpen W →
        (∀ s ∈ Icc (-τ) 0, ∀ x : W, curvDerivNormSq 0 (h s) x ≤ K ^ 2) →
        riemannianClosedBallOf g y (ρ + 1) ⊆ W →
        ∀ m : ℕ, ∀ s ∈ Icc (-(τ / 2)) 0, ∀ x : W, (x : M) ∈ riemannianClosedBallOf g y ρ →
          curvDerivNorm m (h s) x ≤ B m := by
  obtain ⟨B, hB0, hB⟩ := exists_half_window_curvDerivNorm_bound.{u} (K := K) hτ one_pos
  refine ⟨B, hB0, ?_⟩
  intro M _ _ _ _ _ g W h y hsol h0 hcurv hsub m s hs x hx
  let _ : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)
  have hcpt : IsCompact (riemannianClosedBallOf (h 0) x 1) := by
    rw [h0]
    exact isCompact_riemannianClosedBallOf_restrictOpen_of_subset g W x 1
      ((riemannianClosedBallOf_subset_of_add_radius_le g hρ zero_le_one le_rfl hx).trans hsub)
  exact hB h hsol x hcpt (fun s' hs' z _ => hcurv s' hs' z) m s hs

end FILL910
