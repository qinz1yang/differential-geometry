import DifferentialGeometry.Geometry.Collapse.EdgeTangentialPinning
import DifferentialGeometry.Geometry.Collapse.RankOneValueCoordinatesApplications

/-!
# Consumer: the LFR19 edge coordinate is pinned to every anchor direction

LFR19 with the LFR36 parameters (`exists_edge_tangential_coordinate`) composed with the
tangential half of (LFR36.2) (`exists_edge_tangential_pinning`), on a fixed complete smooth
manifold: one coordinate, smooth near `B̄(p, 100Δ)` with value error `μΔ`, whose gradient is
`ι`-close to EVERY minimizing direction toward every point of almost unit coordinate slope.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- One LFR19 edge coordinate pinned to every almost-unit-slope direction. -/
theorem exists_pinned_edge_tangential_coordinate (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {Y : Type*} [MetricSpace Y] (p : M) (y₀ : Y)
    {ι μ : ℝ} (hι : 0 < ι) (hμ : 0 < μ) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ Δ : ℝ, 1 ≤ Δ → ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b < b₀ →
      ∀ α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) b,
      (∀ z ∈ Metric.ball p b⁻¹, SectionalBoundedBelowAt g z (-b ^ 2)) →
      ∃ f : M → ℝ, ∃ O : Set M, IsOpen O ∧ Metric.closedBall p (100 * Δ) ⊆ O ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f O ∧ f p = 0 ∧
        (∀ x ∈ Metric.ball p (100 * Δ), |f x - (α.toFun x).fst| < μ * Δ) ∧
        ∀ y ∈ Metric.ball p (16 * Δ), ∀ a : M, Δ / 80 ≤ dist y a → dist y a ≤ 40 * Δ →
          (1 - θ) * dist y a ≤ (α.toFun a).fst - (α.toFun y).fst →
          ∀ v : TangentSpace I y, g.inner y v v = 1 →
          intrinsicGeodesic g hEnorm y v (dist y a) = a →
          ∀ X : TangentSpace I y,
            |mvfderiv (I := I) f y X - g.inner y v X| ≤ ι * Real.sqrt (g.inner y X X) := by
  obtain ⟨σ₀, hσ₀, hpin⟩ := exists_edge_tangential_pinning hι
  set σ : ℝ := min σ₀ (1 / 2) with hσdef
  have hσ : 0 < σ := lt_min hσ₀ (by norm_num)
  have hσσ₀ : σ ≤ σ₀ := min_le_left _ _
  have hσone : σ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨σ₀, hσ₀, fun Δ hΔ => ?_⟩
  obtain ⟨β₀, hβ₀, hcoord⟩ := exists_edge_tangential_coordinate hΔ hμ hσ hσone
  obtain ⟨b₁, hb₁, hpinΔ⟩ := hpin Δ (by linarith)
  refine ⟨min β₀ b₁, lt_min hβ₀ hb₁, fun b hb hbsmall α hsec => ?_⟩
  obtain ⟨f, O, hO, hCO, hf, hfp, hfl, hvalue, htest⟩ :=
    hcoord b hb (hbsmall.trans_le (min_le_left _ _)) E H I M g hEnorm Y p y₀ α hsec
  refine ⟨f, O, hO, hCO, hf, hfp, hvalue, fun y hy a ha1 ha2 hD v hv hva X => ?_⟩
  have hyO : y ∈ O := hCO (mem_closedBall.mpr (by
    have : dist y p < 16 * Δ := hy
    linarith))
  have hfy : MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    ((hf y hyO).contMDiffAt (hO.mem_nhds hyO)).mdifferentiableAt (by simp)
  exact hpinΔ σ σ₀ b hσ.le hσσ₀ le_rfl hb (hbsmall.trans_le (min_le_right _ _)) E H I M g
    hEnorm Y p y₀ α hsec f hfl htest y hy hfy a ha1 ha2 hD v hv hva X

end DifferentialGeometry.Geometry.Collapse
