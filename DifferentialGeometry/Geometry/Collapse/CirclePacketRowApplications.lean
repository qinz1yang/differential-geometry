import DifferentialGeometry.Geometry.Collapse.CirclePacketRow

/-!
# Consumer of the LFR07 row form

`lfr07_enclosures_and_cutoff_of_residual`: at accuracy `γ = 1/20`, one threshold `β₀` gives, on every
complete Riemannian manifold with a sufficiently accurate splitting and the supplied residual
estimate, a single `η` whose zero set lies in `B(q, 2)` and a smooth compactly supported cutoff equal
to one on `{|η| ≤ 8}` (read off `lfr07_exists_circle_packet_of_residual`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe uE uH u w

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The LFR07 row form at `γ = 1/20`: the zero set of the produced `η` lies in `B(q, 2)` and there is
a smooth compactly supported cutoff, equal to one where `|η| ≤ 8`, supported in `B(q, 200)`. -/
theorem lfr07_enclosures_and_cutoff_of_residual :
    ∃ β₀ : ℝ, 0 < β₀ ∧
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type u) [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (_hEnorm : IsMetricNorm (I := I) g)
        (Y : Type w) [MetricSpace Y] (q : M) (a : Y),
      ∀ {β : ℝ}, β ≤ β₀ →
      ∀ F : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ²), a)) β,
      (∀ y ∈ ball q β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
      (∀ x ∈ ball q 200, dist (F.toFun x).snd a < 1) →
      ∃ η : M → ℝ², η q = 0 ∧ (∀ x ∈ ball q 200, η x = 0 → x ∈ ball q 2) ∧
        ∃ ζ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
          (∀ x ∈ ball q 200, ‖η x‖ ≤ 8 → ζ x = 1) ∧ ∀ x, ζ x ≠ 0 → x ∈ ball q 200 := by
  obtain ⟨β₀, hβ₀, -, hrow⟩ :=
    lfr07_exists_circle_packet_of_residual.{uE, uH, u, w} (γ := 1 / 20) (by norm_num)
      (by norm_num)
  refine ⟨β₀, hβ₀, ?_⟩
  intro E instNorm instSpace instFinite instNe H instTop I instBoundary
    M m instChart instManifold instSigma instComplete instRB instRiem instContinuous
    g hEnorm Y mY q a β hβ F hsec hres
  obtain ⟨η, -, -, hq, -, -, -, h2, -, -, ζ, hζ, hc, -, hζ1, hsupp⟩ :=
    hrow E H I M g hEnorm Y q a hβ F hsec hres
  exact ⟨η, hq, h2, ζ, hζ, hc, hζ1, fun x hx => (hsupp x hx).1⟩

end DifferentialGeometry.Geometry.Collapse
