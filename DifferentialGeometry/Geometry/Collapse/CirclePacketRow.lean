import DifferentialGeometry.Geometry.Collapse.SimultaneousCircleProduction

/-!
# LFR07 as a row: the circle packet from a supplied residual-factor estimate

Blueprint 207A, LFR07 (`cor:collapse-rank-two-circle-packet`, A:25322–25357): retain LC83's tested
residual-factor estimate, choose the SAME splitting accurate enough for LFR06 after the fixed
rescaling; then the rank-two coordinates, both LC83 enclosures, the proper trivial circle bundle over
`B(0, 100)` and its smooth cutoff all exist.

* `lfr07_exists_circle_packet_of_residual`: the row with the residual estimate SUPPLIED, as the
  blueprint words it. It composes the rank-two coordinate producer
  `exists_large_ball_rankTwo_coordinate_parameters` (LFR06 after the fixed `201` rescaling) with the
  packet kernel `circlePacket_of_rank_two_coordinates` and the circle fibre identification
  `circleFiber_local_model_circle`, all on the same `η`. The accuracy `γ` of `η` against the
  `ℝ²`-coordinate of the splitting is arbitrary in `(0, 1/10)`; triviality is over every `B(0, R)`,
  `R < 100` (LC83's form).

The stronger producer `exists_early_simultaneous_circle_packet_parameters` (Codex X77) derives the
residual estimate from the collapsed model instead of assuming it.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe uE uH u w

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **LFR07 (row form, residual estimate supplied).** For every accuracy `0 < γ < 1/10` there is
`β₀ > 0` such that: on a complete Riemannian manifold `(M, g)` with a pointed `β`-approximation
`F : (M, q) → ℝ² × Y`, `β ≤ β₀`, curvature `≥ -β²` on `B(q, β⁻¹)`, and the tested residual estimate
`d((F x).snd, a) < 1` on `B(q, 200)`, there is a smooth rank-two `2`-Lipschitz `η` with `η q = 0` and
`|η - (F ·).fst| < γ` on `B(q, 200)`, both LC83 enclosures hold, `η` gives the proper trivial circle
packet over `B(0, 100)` (circle fibres in dimension three), and `Φ_{8,9}(|η|)` is a smooth compactly
supported cutoff. -/
theorem lfr07_exists_circle_packet_of_residual {γ : ℝ} (hγ : 0 < γ) (hγone : γ < 1 / 10) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ 1 / 1000 ∧
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
      ∃ η : M → ℝ², ∃ hη : ContMDiffOn I 𝓘(ℝ, ℝ²) ∞ η (ball q 200),
      ∃ hrank : ∀ x ∈ ball q 200, Surjective (mfderiv I 𝓘(ℝ, ℝ²) η x),
        η q = 0 ∧ LipschitzOnWith 2 η (ball q 200) ∧
        (∀ x ∈ ball q 200, ‖η x - (F.toFun x).fst‖ < γ) ∧
        (∀ x ∈ ball q 200, ‖η x‖ < 100 → x ∈ ball q 102) ∧
        (∀ x ∈ ball q 200, η x = 0 → x ∈ ball q 2) ∧
        (let f := diskPreimageMap (ball q 200) isOpen_ball η hη.continuousOn 100
        ContMDiff I 𝓘(ℝ, ℝ²) ∞ f ∧
          (∀ x, Surjective (mfderiv I 𝓘(ℝ, ℝ²) f x)) ∧ IsProperMap f ∧ Surjective f ∧
          (∀ z, IsCompact (f ⁻¹' {z}) ∧ IsConnected (f ⁻¹' {z})) ∧
          ∀ R (hR : 0 < R) (hRr : R < 100),
            let y₀ : planeBallOpens 100 := ⟨0, zero_mem_planeBallOpens (hR.trans hRr)⟩
            letI := regularFiberChartedSpace f y₀ (contMDiff_diskPreimageMap isOpen_ball hη 100)
              (fun x _point => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
            let U : TopologicalSpace.Opens
                (diskPreimageOpens (ball q 200) isOpen_ball η hη.continuousOn 100) :=
              ⟨f ⁻¹' planeBallInner 100 R,
                (planeBallInner 100 R).isOpen.preimage
                  (continuous_diskPreimageMap isOpen_ball hη.continuousOn 100)⟩
            ∃ (hy : y₀ ∈ planeBallInner 100 R) (Θ : Diffeomorph
                (𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ).prod 𝓘(ℝ, ℝ²)) I
                ({x // f x = y₀} × planeBallInner 100 R) U ∞),
              (∀ z, f (Θ z).1 = z.2.1) ∧ (∀ x, (Θ (x, ⟨y₀, hy⟩)).1 = x.1)) ∧
        (Module.finrank ℝ E = 3 → ∀ z : planeBallOpens 100,
          let f := diskPreimageMap (ball q 200) isOpen_ball η hη.continuousOn 100
          letI := regularFiberChartedSpace f z (contMDiff_diskPreimageMap isOpen_ball hη 100)
            (fun x _point => surjective_mfderiv_diskPreimageMap isOpen_ball hη hrank 100 x)
          Nonempty (Circle ≃ₘ⟮𝓡 1,
            𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ²) → ℝ)⟯ {x // f x = z})) ∧
        ∃ ζ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ HasCompactSupport ζ ∧
          (∀ x, ζ x ∈ Icc 0 1) ∧ (∀ x ∈ ball q 200, ‖η x‖ ≤ 8 → ζ x = 1) ∧
          ∀ x, ζ x ≠ 0 → x ∈ ball q 200 ∧ ‖η x‖ < 9 := by
  obtain ⟨β₀, hβ₀, hβ₀small, hcoordinates⟩ :=
    exists_large_ball_rankTwo_coordinate_parameters.{uE, uH, u, w} hγ hγone
  refine ⟨β₀, hβ₀, hβ₀small, ?_⟩
  intro E instNorm instSpace instFinite instNe H instTop I instBoundary
    M m instChart instManifold instSigma instComplete instRB instRiem instContinuous
    g hEnorm Y mY q a β hβ F hsec hres
  obtain ⟨η, hη, hq, hrank, hlip, hclose⟩ :=
    hcoordinates E H I M g hEnorm Y q a hβ F hsec
  have hβsmall : β ≤ 1 / 200 := hβ.trans (hβ₀small.trans (by norm_num))
  have hclose' : ∀ x ∈ ball q 200, ‖η x - (F.toFun x).fst‖ < 1 / 10 :=
    fun x hx => (hclose x hx).trans hγone
  obtain ⟨h102, h2, hbundle, ζ, hζ, hc, hζ01, hζ1, hsupp⟩ :=
    circlePacket_of_rank_two_coordinates g hEnorm F hβsmall hres hη hrank hlip hq hclose'
  refine ⟨η, hη, hrank, hq, hlip, hclose, h102, h2, hbundle, ?_,
    ζ, hζ, hc, hζ01, hζ1, hsupp⟩
  intro hdim3 z
  exact circleFiber_local_model_circle g hEnorm hdim3 hη hrank hlip hq h102 h2 z

end DifferentialGeometry.Geometry.Collapse
