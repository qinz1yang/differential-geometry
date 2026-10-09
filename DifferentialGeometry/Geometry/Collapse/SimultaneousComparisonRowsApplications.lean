import DifferentialGeometry.Geometry.Collapse.SimultaneousComparisonRows

/-!
# Consumers of the F8 comparison rows

* `lcp05_nearest_directions_close`: under LCP05's hypotheses, any two nearest directions to the
  closed set at a tested point are `30√τ`-close (A:30177, "simultaneously to all nearest points and
  minimizing directions").
* `lcp03_prefix_scaled_le`: under LCP03's hypotheses, at every scale the normalized radial
  coordinate along the chosen outward segment never exceeds the normalized prefix length, and on
  every inward prefix it is nonpositive.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Real
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Edge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- Any two nearest directions at a tested point are `30√τ`-close (LCP05). -/
theorem lcp05_nearest_directions_close (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Q : M → WithLp 2 (ℝ × ℝ)} {p : M} {A : Set M} {Δ τ κ : ℝ}
    (hΔ : 0 < Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000) (hQp : Q p = 0)
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
    {x : M} (hx : x ∈ ball p (30 * Δ)) (hlo : Δ / 2 ≤ infDist x A)
    (hhi : infDist x A ≤ 12 * Δ) {v v' : TangentSpace I x}
    (hv : v ∈ minimizingDirectionsTo g hEnorm A x) (hv' : v' ∈ minimizingDirectionsTo g hEnorm A x) :
    Real.sqrt (g.inner x (v - v') (v - v')) < 30 * Real.sqrt τ := by
  obtain ⟨-, h⟩ := lcp05_edge_nearest_directions g hEnorm hΔ hτ hτsmall hQp hdist hheight hcover
    hpA hborder hbordercover hκ hκΔ hsec
  obtain ⟨-, hdiam, hlt⟩ := h x hx hlo hhi
  exact (hdiam v hv v' hv').trans_lt hlt

end Edge

section Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- Along the chosen outward segment the normalized radial coordinate is at most the normalized
prefix length, and on every inward prefix it is nonpositive (LCP03). -/
theorem lcp03_prefix_scaled_le {σ : ℝ} (hσ : 0 < σ) (hσone : σ < 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace H M]
        [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)]
        [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M), IsMetricNorm g → ∀ p : M,
      (∀ y ∈ ball p 400, SectionalBoundedBelowAt g y (-((1 / 60) ^ 2))) →
      ∀ (C : Type v) [MetricSpace C] (o : C), RadialConeData o →
      ∀ {δ : ℝ}, KleinerLottApprox p o δ →
        δ < min (1 / 600 : ℝ) (min (1 / 60) ((1 - cos θ) / 600)) →
      ∀ q : M, 1 / 10 ≤ dist p q → dist p q ≤ 10 →
      ∃ z : M, dist q z = dist p q ∧
        (∀ x : M, 0 < dist q x → dist q x + dist x z = dist q z → ∀ lam : ℝ, 0 < lam →
          lam * (dist p x - dist p q) ≤ lam * dist q x) ∧
        ∀ x : M, dist q x + dist x p = dist q p → ∀ lam : ℝ, 0 ≤ lam →
          lam * (dist p x - dist p q) ≤ 0 := by
  obtain ⟨θ, hθ, hθone, h⟩ := lcp03_original_radial_calibration.{u, v} (E := E) (H := H)
    (I := I) hσ hσone
  refine ⟨θ, hθ, hθone, ?_⟩
  intro M _ _ _ _ _ _ _ _ g hEnorm p hsec C _ o hC δ φ hδ q hq1 hq2
  obtain ⟨z, hz, -, hout, hin⟩ := h M g hEnorm p hsec C o hC φ hδ q hq1 hq2
  refine ⟨z, hz, fun x hx hxz lam hlam => ((hout x hx hxz).2.2 lam hlam).2, ?_⟩
  intro x hx lam hlam
  rw [hin x hx lam]
  have := mul_nonneg hlam dist_nonneg (a := lam) (b := dist q x)
  linarith

end Radial

end DifferentialGeometry.Geometry.Collapse
