import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryRowBindingsApplicationsIdx
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroProducerV2ApplicationsIdx
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroTransportApplicationsIdx
import DifferentialGeometry.Geometry.Collapse.StaticCounterexamples

/-!
# The four index-shifted small consumers at BBR03's counterexample sequence (lane BDRY-IDX4)

Non-vacuity of `bsa04_standing_eventually_IDX4`, `bsa06_scaled_ball_interior_eventually_IDX4`,
`eventually_zero_shell_rank_scale_boundary_BZ1_IDX4` and
`eventually_zero_shell_coordinate_original_BZ1_IDX4`: the accepted forms take sequences at `δ_n`
for ALL `n`, an EMPTY hypothesis (`isEmpty_boundarySequence_ratio_IDX`); the restated forms take
sequences at `δ_{n+1}`, the TYPE produced by BBR03's framework
`exists_boundary_counterexample_sequence_of_no_threshold` (`StaticCounterexamples.lean`,
B:10624–10625). Each is applied there without an adapter.

* `bsa04_standing_eventually_bbr03_IDX4`, `bsa06_scaled_ball_interior_eventually_bbr03_IDX4`;
* `eventually_zero_shell_rank_scale_boundary_bbr03_IDX4`,
  `eventually_zero_shell_coordinate_original_bbr03_IDX4`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function Manifold
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry GC.Endpoint
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Hyperbolic
open GC.MetricGeometry

universe u

/-- **BSA04.a consumer at BBR03's counterexample sequence (non-vacuity of
`bsa04_standing_eventually_IDX4`).** For `0 < δ₀ ≤ δStar`, `K ≥ 2` and every certificate `Good`
without a nonempty-boundary threshold, a counterexample sequence at the ratios `δ_{n+1}`
(collapsed, derivative-controlled, no member satisfying `Good`) with the standing inequality at
every point on a tail. -/
theorem bsa04_standing_eventually_bbr03_IDX4 :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K → ∀ (A : ℝ → ℝ)
      (Good : ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier) (w : ℝ),
          NearlyCuspidalBoundary W g K w → Prop),
        (¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
          ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
            (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
            boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
            Good W g w₀ B) →
      ∃ (W : ℕ → CompactCarrier.{u}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) ∧
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) ∧
        (∀ n, ¬ Good (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)) ∧
      ∀ᶠ n : ℕ in atTop, ∀ p : (W n).Carrier,
        ENNReal.ofReal (2 * n * firstVolumeScale (g n) p (n : ℝ)⁻¹) <
          curvatureRadius (g n) p := by
  obtain ⟨δS, hδS, hP⟩ := bsa04_standing_eventually_IDX4.{u}
  refine ⟨δS, hδS, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK A Good hno
  obtain ⟨W, hW, g, B, hseq⟩ :=
    exists_boundary_counterexample_sequence_of_no_threshold.{u} K A hδ₀ Good hno
  exact ⟨W, hW, g, B, fun n => (hseq n).1, fun n => (hseq n).2.1, fun n => (hseq n).2.2,
    hP hδ₀ hδ₀S K hK A W g B (fun n => (hseq n).1) (fun n => (hseq n).2.1)⟩

/-- **BSA06 consumer at BBR03's counterexample sequence (non-vacuity of
`bsa06_scaled_ball_interior_eventually_IDX4`).** For `0 < δ₀ ≤ δStar`, `K ≥ 2`, `A > 0` and every
certificate `Good` without a nonempty-boundary threshold, a counterexample sequence at the ratios
`δ_{n+1}` (collapsed, derivative-controlled, no member satisfying `Good`) on which, for every
buffer `b`, the scaled balls `B(p, b ρ_n(p))` at centers with `d > 10` lie in the interior on one
tail. -/
theorem bsa06_scaled_ball_interior_eventually_bbr03_IDX4 :
    ∃ δStar > 0, ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar → ∀ (K : ℕ), 2 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ (Good : ∀ (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier) (w : ℝ),
          NearlyCuspidalBoundary W g K w → Prop),
        (¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
          ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
            (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
            boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
            Good W g w₀ B) →
      ∃ (W : ℕ → CompactCarrier.{u}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) ∧
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) ∧
        (∀ n, ¬ Good (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)) ∧
        ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < euclideanThreeUnitBallVolume / 4 → ∀ b : ℝ,
          ∃ ρ : ∀ n, (W n).Carrier → ℝ, ∀ᶠ n : ℕ in atTop, (∀ p, 0 < ρ n p) ∧
            ∀ p : (W n).Carrier, ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) p →
              riemannianBallOf (g n) p (b * ρ n p) ⊆ (W n).model.interior (W n).Carrier := by
  obtain ⟨δS, hδS, hP⟩ := bsa06_scaled_ball_interior_eventually_IDX4.{u}
  refine ⟨δS, hδS, ?_⟩
  intro δ₀ hδ₀ hδ₀S K hK A hA Good hno
  obtain ⟨W, hW, g, B, hseq⟩ :=
    exists_boundary_counterexample_sequence_of_no_threshold.{u} K A hδ₀ Good hno
  exact ⟨W, hW, g, B, fun n => (hseq n).1, fun n => (hseq n).2.1, fun n => (hseq n).2.2,
    hP hδ₀ hδ₀S K hK A hA W g B (fun n => (hseq n).1) (fun n => (hseq n).2.1)⟩

section Completion

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

/-- **The zero-shell rank / scale consumer at BBR03's counterexample sequence (non-vacuity of
`eventually_zero_shell_rank_scale_boundary_BZ1_IDX4`).** Same prefix; for `0 < δ₀ ≤ δStar` and every
certificate `Good` without a nonempty-boundary threshold, a connected counterexample sequence at
the ratios `δ_{n+1}` (collapsed, derivative-controlled, no member satisfying `Good`) on which, for
every choice of completions `ĝ_n`, the zero-shell rank and scale clauses hold on one tail. -/
theorem eventually_zero_shell_rank_scale_boundary_bbr03_IDX4 :
    ∃ δStar > 0, ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {β : ℕ → ℝ}, 0 < β 1 → β 1 < 1 → ∀ {ζ cap : ℝ}, β 1 < ζ → ζ < 1 → 0 < cap →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ {T : ℝ}, 0 < T → 20 * Λ' ≤ T →
      ∀ {e : ℝ}, 0 < e → e < 1 / 40 →
      ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
      ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (Good : ∀ (W : CompactCarrier.{0}) (g : SmoothRiemannianMetric W.model W.Carrier) (w : ℝ),
          NearlyCuspidalBoundary W g K w → Prop),
        (¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
          ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
            (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
            boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
            Good W g w₀ B) →
      ∃ (W : ℕ → CompactCarrier.{0}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) ∧
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) ∧
        (∀ n, ¬ Good (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)) ∧
      ∀ (ĝ : ∀ n, SmoothRiemannianMetric (𝓡 3) ((W n).pieceInterior ⊤)),
        (∀ n, RiemannianMetricComplete (I := 𝓡 3) (ĝ n)) →
        (∀ n (x : (W n).pieceInterior ⊤), ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x →
          (ĝ n).inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x) →
        (∀ n (x : (W n).pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
          (pieceInteriorMetric (W n) (g n) ⊤).inner x v v ≤ (ĝ n).inner x v v) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ n in atTop,
        letI := inducedMetricSpace (ĝ n)
        ∀ (ρ : (W n).Carrier → ℝ) (hρ : ∀ p, 0 < ρ p), Continuous ρ →
        (∀ p, ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
        (∀ (i : Fin (B n).count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
          ρ (((B n).collar i).toFun q) ≤ β 1 ^ 3 / 2000) →
        ∃ (N C : (W n).pieceInterior ⊤ → Type) (_ : ∀ a, MetricSpace (N a))
          (_ : ∀ a, ChartedSpace E3 (N a)) (_ : ∀ a, MetricSpace (C a)) (o : ∀ a, C a),
          ∃ F : ZeroModelFamilyOn I3 ((W n).pieceInterior ⊤) (ĝ n) (fun x => ρ x)
            (fun x => hρ x) β N C o δ εr e T V
            {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x}
            {x | ENNReal.ofReal 20 ≤ distanceToBoundary (W n) (g n) x},
          (∀ c (hc : c ∈ F.centres), ∀ q, (F.zero c hc).radius / 10 ≤ dist c q →
            dist c q ≤ 10 * (F.zero c hc).radius →
            @splittingRank.{0, 0} ((W n).pieceInterior ⊤)
              ((inducedMetricSpace (ĝ n)).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q β 3 ≠ 0) ∧
          ∀ c (hc : c ∈ F.centres), ∀ q, dist c q ≤ 10 * (F.zero c hc).radius →
            ρ q ≤ 20 * (F.zero c hc).radius / T := by
  obtain ⟨δS, hδS, hP⟩ := eventually_zero_shell_rank_scale_boundary_BZ1_IDX4
  refine ⟨δS, hδS, fun K hK A hA β hβ hβ1 ζ cap hβζ hζ1 hcap => ?_⟩
  obtain ⟨εr, δ', Λ', hεr, hεrcap, hδ', hΛ', hP⟩ := hP K hK A hA hβ hβ1 hβζ hζ1 hcap
  refine ⟨εr, δ', Λ', hεr, hεrcap, hδ', hΛ', ?_⟩
  intro T hT hTΛ e he he1 Λ w hΛ hw hwc δ₀ hδ₀ hδ₀S Good hno
  obtain ⟨W, hW, g, B, hseq⟩ :=
    exists_boundary_counterexample_sequence_of_no_threshold.{0} K A hδ₀ Good hno
  exact ⟨W, hW, g, B, fun n => (hseq n).1, fun n => (hseq n).2.1, fun n => (hseq n).2.2,
    hP hT hTΛ he he1 hΛ hw hwc hδ₀ hδ₀S W g B (fun n => (hseq n).1) (fun n => (hseq n).2.1)⟩

/-- **The original-coordinate consumer at BBR03's counterexample sequence (non-vacuity of
`eventually_zero_shell_coordinate_original_BZ1_IDX4`).** Same prefix; for `0 < δ₀ ≤ δStar` and
every certificate `Good` without a nonempty-boundary threshold, a connected counterexample sequence
at the ratios `δ_{n+1}` (collapsed, derivative-controlled, no member satisfying `Good`) on which,
for every choice of completions `ĝ_n`, the original-metric shell coordinate and the enlarged
curvature hold on one tail. -/
theorem eventually_zero_shell_coordinate_original_bbr03_IDX4 :
    ∃ δStar > 0, ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {β : ℕ → ℝ}, 0 < β 1 → β 1 < 1 → ∀ {ζ cap : ℝ}, β 1 < ζ → ζ < 1 → 0 < cap →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ {T : ℝ}, 0 < T → 20 * Λ' ≤ T →
      ∀ {e : ℝ}, 0 < e → e < 1 / 40 →
      ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
      ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (Good : ∀ (W : CompactCarrier.{0}) (g : SmoothRiemannianMetric W.model W.Carrier) (w : ℝ),
          NearlyCuspidalBoundary W g K w → Prop),
        (¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
          ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
            (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
            boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
            Good W g w₀ B) →
      ∃ (W : ℕ → CompactCarrier.{0}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) ∧
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) ∧
        (∀ n, ¬ Good (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)) ∧
      ∀ (ĝ : ∀ n, SmoothRiemannianMetric (𝓡 3) ((W n).pieceInterior ⊤)),
        (∀ n, RiemannianMetricComplete (I := 𝓡 3) (ĝ n)) →
        (∀ n (x : (W n).pieceInterior ⊤), ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x →
          (ĝ n).inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x) →
        (∀ n (x : (W n).pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
          (pieceInteriorMetric (W n) (g n) ⊤).inner x v v ≤ (ĝ n).inner x v v) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ n in atTop,
        letI := inducedMetricSpace (ĝ n)
        ∀ (ρ : (W n).Carrier → ℝ) (hρ : ∀ p, 0 < ρ p), Continuous ρ →
        (∀ p, ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
        (∀ (i : Fin (B n).count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
          ρ (((B n).collar i).toFun q) ≤ β 1 ^ 3 / 2000) →
        ∃ (N C : (W n).pieceInterior ⊤ → Type) (_ : ∀ a, MetricSpace (N a))
          (_ : ∀ a, ChartedSpace E3 (N a)) (_ : ∀ a, MetricSpace (C a)) (o : ∀ a, C a),
          ∃ F : ZeroModelFamilyOn I3 ((W n).pieceInterior ⊤) (ĝ n) (fun x => ρ x)
            (fun x => hρ x) β N C o δ εr e T V
            {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x}
            {x | ENNReal.ofReal 20 ≤ distanceToBoundary (W n) (g n) x},
          (∀ c (hc : c ∈ F.centres), ∀ q, (F.zero c hc).radius / 10 ≤ dist c q →
            dist c q ≤ 10 * (F.zero c hc).radius →
            ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
              ∃ (z : Zf) (Fk : @KleinerLottApprox ((W n).pieceInterior ⊤)
                (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
                ((inducedMetricSpace (ĝ n)).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
                q (WithLp.toLp 2 (0, z)) (β 1)),
                ∀ x ∈ @Metric.ball _ ((inducedMetricSpace (ĝ n)).rescale (ρ q)⁻¹
                    (inv_pos.mpr (hρ q))).toPseudoMetricSpace q (β 1)⁻¹,
                  (@KleinerLottApprox.toFun ((W n).pieceInterior ⊤)
                    (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
                    ((inducedMetricSpace (ĝ n)).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q)))
                    inferInstance q (WithLp.toLp 2 (0, z)) (β 1) Fk x).fst = WithLp.toLp 2
                    (Function.const (Fin 1) ((ρ q)⁻¹ *
                      ((riemannianEDistOf (g n) c.val x.val).toReal -
                        (riemannianEDistOf (g n) c.val q.val).toReal)))) ∧
          ∀ c (hc : c ∈ F.centres),
            ∀ y ∈ riemannianBallOf (g n) c.val (400 * (F.zero c hc).radius),
              SectionalBoundedBelowAt (g n) y
                (-((1 / 60) ^ 2 * ((F.zero c hc).radius)⁻¹ ^ 2)) := by
  obtain ⟨δS, hδS, hP⟩ := eventually_zero_shell_coordinate_original_BZ1_IDX4
  refine ⟨δS, hδS, fun K hK A hA β hβ hβ1 ζ cap hβζ hζ1 hcap => ?_⟩
  obtain ⟨εr, δ', Λ', hεr, hεrcap, hδ', hΛ', hP⟩ := hP K hK A hA hβ hβ1 hβζ hζ1 hcap
  refine ⟨εr, δ', Λ', hεr, hεrcap, hδ', hΛ', ?_⟩
  intro T hT hTΛ e he he1 Λ w hΛ hw hwc δ₀ hδ₀ hδ₀S Good hno
  obtain ⟨W, hW, g, B, hseq⟩ :=
    exists_boundary_counterexample_sequence_of_no_threshold.{0} K A hδ₀ Good hno
  exact ⟨W, hW, g, B, fun n => (hseq n).1, fun n => (hseq n).2.1, fun n => (hseq n).2.2,
    hP hT hTΛ he he1 hΛ hw hwc hδ₀ hδ₀S W g B (fun n => (hseq n).1) (fun n => (hseq n).2.1)⟩

end Completion

end DifferentialGeometry.Geometry.Collapse
