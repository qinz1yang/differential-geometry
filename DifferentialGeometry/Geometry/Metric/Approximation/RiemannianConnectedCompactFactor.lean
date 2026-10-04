import DifferentialGeometry.Geometry.Metric.Approximation.ConnectedCompactFactor
import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianExtraction
import DifferentialGeometry.Geometry.Metric.RiemannianShortCurves

/-!
# LFR16, metric part, for actual Riemannian sources

Blueprint 207A, LFR16 (A:26159–26203). Complete smooth Riemannian manifolds in the aligned block
(`g i`, `hmetric`) with sectional curvature `≥ -κ i` on `B(p i, ρ i)`, `κ i → 0`, `ρ i → ∞`, and
Kleiner–Lott approximations of the sources by `ℝ × Z i` with errors tending to zero and residual
factors of diameter at most `D`: a subsequence has a complete proper pointed limit `Y`, connected,
isometric to `ℝ × W` with `W` the limit of the residual factors, compact, connected and of
diameter at most `D`. The limit producer is X71's `exists_pointed_limit_of_growing_sectional_lower_bound`;
the almost minimizing curves are `exists_arbitrarily_short_riemannian_curve`.
-/

set_option autoImplicit false

open Set Metric Filter DifferentialGeometry
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian

namespace GC.MetricGeometry

universe u

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : ℕ → Type u} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, T2Space (TangentBundle I (X i))]
  [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]

/-- **LFR16, metric part, Riemannian binding.** -/
theorem exists_connected_compact_factor_of_growing_sectional_lower_bound
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) {κ ρ : ℕ → ℝ}
    (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop)
    (hsec : ∀ i, ∀ y ∈ ball (p i) (ρ i), SectionalBoundedBelowAt (g i) y (-κ i))
    {Z : ℕ → Type*} [∀ i, MetricSpace (Z i)] (b : ∀ i, Z i) {δ : ℕ → ℝ}
    (f : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 ((0 : ℝ), b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) {D : ℝ} (hD : ∀ i, ∀ x y : Z i, dist x y ≤ D) :
    ∃ (Y W : Type) (mY : MetricSpace Y) (mW : MetricSpace W), letI := mY; letI := mW
      ∃ (q : Y) (w : W) (φ : ℕ → ℕ), StrictMono φ ∧ CompleteSpace Y ∧ ProperSpace Y ∧
        ConnectedSpace Y ∧ PointedGHConverges (fun i => p (φ i)) q ∧
        CompactSpace W ∧ ConnectedSpace W ∧ (∀ x y : W, dist x y ≤ D) ∧
        PointedGHConverges (fun i => b (φ i)) w ∧
        ∃ e : Y ≃ᵢ WithLp 2 (ℝ × W), e q = WithLp.toLp 2 ((0 : ℝ), w) := by
  obtain ⟨Y, mY, q, φ, hφ, hcY, hpY, hconv, -⟩ :=
    exists_pointed_limit_of_growing_sectional_lower_bound g hmetric p hκ hκzero hρ hsec
  let := mY
  have hcurves : ∀ n, ∀ a c : X (φ n), ∀ ε : ℝ, 0 < ε →
      ∃ γ : unitInterval → X (φ n), Continuous γ ∧ γ 0 = a ∧ γ 1 = c ∧
        eVariationOn γ univ < ENNReal.ofReal (dist a c + ε) :=
    fun n a c _ hε => DifferentialGeometry.Geometry.Metric.exists_arbitrarily_short_riemannian_curve
      (g (φ n)) (hmetric (φ n)) a c hε
  obtain ⟨W, mW, w, ψ, hψ, -, -, hcpt, hconnW, hdiam, hb, hx, e, he⟩ :=
    hconv.exists_connected_compact_factor_of_approximate_products hcurves
      (fun i => f (φ i)) (hδ.comp hφ.tendsto_atTop) (fun i => hD (φ i))
  let := mW
  exact ⟨Y, W, mY, mW, q, w, φ ∘ ψ, hφ.comp hψ, hcY, hpY,
    hconv.connectedSpace_of_short_curves hcurves, hx, hcpt, hconnW, hdiam, hb, e, he⟩

end GC.MetricGeometry
