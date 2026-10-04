import DifferentialGeometry.Geometry.Collapse.EdgeScaledSmoothing

/-!
# Consumer of LFR27: the edge collar smoothing at a constant scale

`exists_edge_scaled_smoothing` (LFR27) applied with the constant scale `ρ ≡ 1` (Lipschitz constant `0`):
the smoothed distance `F` itself has the constant core profile `H = Δ ψ(F/Δ)`, smooth on
`B(p, 20Δ) ∩ {d_A < 10.25Δ}` with exactly the sublevels of `F` above `2Δ`, and the nearest-direction
gradient bound on the collar. The coarse-border chart and curvature hypotheses are those of LFR25.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem exists_edge_unit_scale_smoothing (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Q : M → WithLp 2 (ℝ × ℝ)} {p : M} {A : Set M} {Δ τ κ ε μ : ℝ}
    (hA : IsClosed A) (hΔ : 0 < Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000) (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball p (200 * Δ), dist (Q x) z ≤ τ * Δ)
    (hpA : p ∈ A)
    (hborder : ∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ)
    (hbordercover : ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A ∩ ball p (190 * Δ), dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hκ : 0 ≤ κ) (hκΔ : κ * Δ ≤ 1 / 100)
    (hsec : ∀ z ∈ ball p (1000 * Δ), SectionalBoundedBelowAt g z (-κ ^ 2))
    (hε : 0 < ε) (hε1 : ε < 1 / 100) (hμ : 0 < μ) (hμ1 : μ < 1 / 100)
    (hθ : 30 * Real.sqrt τ < ε ^ 2 / 20) :
    ∃ F : M → ℝ, (∀ x, 0 ≤ F x) ∧ (∀ x, |F x - infDist x A| < μ * Δ) ∧
      (∀ x ∈ closedBall p (20 * Δ), 3 / 4 * Δ ≤ infDist x A → infDist x A ≤ 21 / 2 * Δ →
        ∀ v ∈ minimizingDirectionsTo g hEnorm A x,
          Real.sqrt (g.inner x (gradFun g F x + v) (gradFun g F x + v)) < ε) ∧
      (∀ x ∈ ball p (20 * Δ), infDist x A < 41 / 4 * Δ →
        ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => Δ * edgeSublevelProfile (F y / Δ)) x) ∧
      ∀ s, 2 * Δ ≤ s → ∀ x, (Δ * edgeSublevelProfile (F x / Δ) ≤ s ↔ F x ≤ s) := by
  obtain ⟨F, -, -, -, -, hnn, -, hclose, -, hgrad, -, hsm, hsub, -, -⟩ :=
    exists_edge_scaled_smoothing (ρ := fun _ => (1 : ℝ)) (Λ := 0) g hEnorm hA hΔ hτ hτsmall hQp
      hdist hheight hcover hpA hborder hbordercover hκ hκΔ hsec hε hε1 hμ hμ1 hθ
      (LipschitzWith.const 1) rfl contMDiffOn_const (by simp)
  simp only [div_one] at hsm hsub
  exact ⟨F, hnn, hclose, fun x hx h1 h2 v hv => hgrad x ⟨hx, h1, h2⟩ v hv, hsm, hsub⟩

end DifferentialGeometry.Geometry.Collapse
