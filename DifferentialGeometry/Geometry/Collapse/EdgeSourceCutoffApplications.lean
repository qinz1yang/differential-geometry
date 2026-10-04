import DifferentialGeometry.Geometry.Collapse.EdgeSourceCutoff

/-!
# Consumer: LFR27's smoothing comes with LFR28's source cutoff

W4-F7d1's LFR27 producer `exists_edge_scaled_smoothing` composed with `exists_edge_source_cutoff`:
for every tangential coordinate `f` smooth on `B(p, 100Δ)` with value error `μΔ`, the cutoff
built from `(f, F/ρ)` is smooth, compactly supported, equal to one at the centre and supported in
`B(p, 13Δ)`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian

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

/-- One LFR27 smoothing; for every tangential coordinate, a smooth source cutoff equal to one at
the centre with support in `B(p, 13Δ)`. -/
theorem exists_edge_scaled_smoothing_with_source_cutoff (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Q : M → WithLp 2 (ℝ × ℝ)} {p : M} {A : Set M} {ρ : M → ℝ}
    {Λ : ℝ≥0} {Δ τ κ ε μ : ℝ}
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
    (hθ : 30 * Real.sqrt τ < ε ^ 2 / 20)
    (hρ : LipschitzWith Λ ρ) (hρp : ρ p = 1)
    (hρs : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ρ (ball p (100 * Δ))) (hlam : 100 * Δ * Λ < 1 / 100) :
    ∃ F : M → ℝ, (∀ x, |F x - infDist x A| < μ * Δ) ∧
      ∀ f : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f (ball p (100 * Δ)) →
        (∀ x ∈ ball p (100 * Δ), |f x - (Q x).fst| ≤ μ * Δ) →
        ∃ ζ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
          (|f p| ≤ 8 * Δ → ζ p = 1) ∧ tsupport ζ ⊆ ball p (13 * Δ) := by
  obtain ⟨F, O, hO, hCO, hFO, hF0, hFL, hval, -⟩ :=
    exists_edge_scaled_smoothing g hEnorm hA hΔ hτ hτsmall hQp hdist hheight hcover hpA hborder
      hbordercover hκ hκΔ hsec hε hε1 hμ hμ1 hθ hρ hρp hρs hlam
  refine ⟨F, hval, fun f hfs hf => ?_⟩
  obtain ⟨ζ, hζs, hζc, -, -, hζ1, hζsupp⟩ := exists_edge_source_cutoff g hEnorm hΔ hτsmall.le
    hμ1.le hQp hdist hheight hpA hborder hf hfs (fun x => (hval x).le) hFL.continuous hO hCO
    hFO hρ hρp hρs hlam.le
  refine ⟨ζ, hζs, hζc, fun hfp => ?_, hζsupp.trans inter_subset_left⟩
  have hp : p ∈ ball p (100 * Δ) := mem_ball_self (by positivity)
  have hdp : infDist p A = 0 := infDist_zero_of_mem hpA
  have hFp : F p / ρ p ≤ 8 * Δ := by
    rw [hρp, div_one]
    have h := (abs_lt.mp (hval p)).2
    rw [hdp] at h
    nlinarith
  exact hζ1 p hp hfp hFp

end DifferentialGeometry.Geometry.Collapse
