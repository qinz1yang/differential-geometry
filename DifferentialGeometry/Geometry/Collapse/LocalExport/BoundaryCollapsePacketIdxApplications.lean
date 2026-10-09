import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCollapsePacketIdx
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace

/-!
# Consumers of the index-shifted T2 / T3: non-vacuity (lane BDRY-IDX)

The accepted T2 / T3 (`eventually_nonempty_boundaryLocalPackets_BDRY1`,
`lc88_boundary_collapse_packet_BDRY1`) quantify over sequences at `δ_n` for ALL `n`. That hypothesis
is uninhabited (finding of lane FC39-BQ, recorded here in compiled form):
* `boundaryCounterexampleRatio_zero_IDX`: `δ_0 = 0`;
* `isEmpty_nearlyCuspidalBoundary_zero_IDX`: nearly cuspidal data at ratio `0` do not exist;
* `isEmpty_boundarySequence_ratio_IDX`: hence `∀ n, NearlyCuspidalBoundary (W n) (g n) K (δ_n)` is
  EMPTY for every `W`, `g`, `K` and `δ₀ > 0`.

The restated T2 / T3 (`…_BDRY1_IDX`) take sequences at `δ_{n+1}`. Non-vacuity:
* `exists_boundarySequence_succ_of_members_IDX`: the new hypothesis is inhabited as soon as the
  per-member data exist at every index `m ≥ 1` (members at ratio `δ_m`, `m ≥ 1`, are the actual
  BSA04 / BBR03 counterexamples; no member at ratio `δ_0` is needed);
* `eventually_nonempty_boundaryLocalPackets_bbr03_IDX`, `lc88_boundary_collapse_packet_bbr03_IDX`:
  T2 / T3 APPLIED to BBR03's counterexample sequence
  (`exists_boundary_counterexample_sequence_of_no_threshold`, StaticCounterexamples.lean): same
  prefix as T2 / T3; for every certificate `Good` without a threshold, the BBR03 sequence (members
  at `δ_{n+1}`, none with `Good`) carries the full T2 / T3 conclusion on one tail — the form in
which
  BBR03's contradiction (B:10624–10644) consumes the producer. No adapter between the two shapes.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The counterexample ratio at index `0` is `0` (`1 / 0 = 0`; lane FC39-BQ). -/
theorem boundaryCounterexampleRatio_zero_IDX {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    boundaryCounterexampleRatio δ₀ 0 = 0 := by
  have hω := euclideanThreeUnitBallVolume_pos
  unfold boundaryCounterexampleRatio
  have h8 : (0 : ℝ) ≤ euclideanThreeUnitBallVolume / 8 := div_nonneg hω.le (by norm_num)
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    div_zero, min_eq_right h8, min_eq_right hδ₀.le]

/-- Nearly cuspidal boundary data at ratio `0` do not exist: the component diameter would be `0`,
but the collar embeds a whole torus slice (lane FC39-BQ). -/
theorem isEmpty_nearlyCuspidalBoundary_zero_IDX (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) :
    IsEmpty (NearlyCuspidalBoundary W g K 0) := by
  refine ⟨fun B => ?_⟩
  let i : Fin B.count := ⟨0, B.count_pos⟩
  let a : Circle := Circle.exp Real.pi
  let b : Circle := 1
  have hab : a ≠ b := by
    intro h
    have h' := congrArg (fun z : Circle => (z : ℂ)) h
    simp only [a, b, Circle.coe_exp, Circle.coe_one] at h'
    rw [Complex.exp_pi_mul_I] at h'
    norm_num at h'
  let t₁ : Torus := (a, 1)
  let t₂ : Torus := (b, 1)
  have hmem : ∀ t : Torus, (t, halfZero) ∈ cuspDomain := fun t => by
    change (halfZero : EuclideanHalfSpace 1).val 0 < cuspDepth
    simp [halfZero, halfPoint, cuspDepth]
  have himg : ∀ t : Torus, (B.collar i).toFun (t, halfZero) ∈ B.component i := fun t =>
    (B.collar i).boundary_image.subset ⟨t, rfl⟩
  have hd := B.diameter i _ (himg t₁) _ (himg t₂)
  rw [ENNReal.ofReal_zero, nonpos_iff_eq_zero] at hd
  let := inducedEMetricSpace g
  have heq : (B.collar i).toFun (t₁, halfZero) = (B.collar i).toFun (t₂, halfZero) :=
    edist_eq_zero.mp hd
  have hinj := (B.collar i).isEmbedding.injective
  have := @hinj ⟨(t₁, halfZero), hmem t₁⟩ ⟨(t₂, halfZero), hmem t₂⟩ heq
  have h1 := congrArg (fun p : cuspDomain => p.1.1.1) this
  exact hab h1

/-- **The accepted sequence hypothesis is empty.** For `δ₀ > 0`, no sequence of carriers has nearly
cuspidal boundary data at `δ_n` for ALL `n` (index `0` fails). This is why every accepted
per-sequence boundary producer stated at `δ_n` is vacuous. -/
theorem isEmpty_boundarySequence_ratio_IDX {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (K : ℕ)
    (W : ℕ → CompactCarrier.{u}) (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier) :
    IsEmpty (∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)) := by
  refine ⟨fun B => ?_⟩
  have h0 := B 0
  rw [boundaryCounterexampleRatio_zero_IDX hδ₀] at h0
  exact (isEmpty_nearlyCuspidalBoundary_zero_IDX (W 0) (g 0) K).false h0

/-- **The new sequence hypothesis is inhabited from per-member data at `m ≥ 1`.** If at every index
`m ≥ 1` some connected carrier has nearly cuspidal boundary data, static collapse and derivative
control at `δ_m`, then a sequence `(W, g, B)` at `δ_{n+1}` with the full hypotheses of
`eventually_nonempty_boundaryLocalPackets_BDRY1_IDX` / `lc88_boundary_collapse_packet_BDRY1_IDX`
exists (member `n` := the datum at `m = n + 1`). -/
theorem exists_boundarySequence_succ_of_members_IDX (K : ℕ) (A : ℝ → ℝ) (δ₀ : ℝ)
    (h : ∀ m : ℕ, 1 ≤ m → ∃ (W : CompactCarrier.{u}) (_ : ConnectedSpace W.Carrier)
      (g : SmoothRiemannianMetric W.model W.Carrier)
      (_ : NearlyCuspidalBoundary W g K (boundaryCounterexampleRatio δ₀ m)),
      boundaryVolumeCollapsed W g (boundaryCounterexampleRatio δ₀ m) ∧
        curvatureDerivativesControlled g K A (boundaryCounterexampleRatio δ₀ m)) :
    ∃ (W : ℕ → CompactCarrier.{u}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
      (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
      (_ : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
      (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) ∧
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀
            (n + 1))) := by
  choose W hW g B hg using fun n : ℕ => h (n + 1) (Nat.le_add_left 1 n)
  exact ⟨W, hW, g, B, fun n => (hg n).1, fun n => (hg n).2⟩

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **T2 applied to BBR03's counterexample sequence (non-vacuity of T2_IDX).** The prefix of
`eventually_nonempty_boundaryLocalPackets_BDRY1_IDX`; then for `0 < δ₀ ≤ δStar` and every
certificate `Good` WITHOUT a nonempty-boundary threshold, the BBR03 counterexample sequence
(members at `δ_{n+1}`, none with `Good`) carries T2's full conclusion on one tail. -/
theorem eventually_nonempty_boundaryLocalPackets_bbr03_IDX
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ δStar : ℝ, 0 < δStar ∧
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ Lmax : ℝ, 0 < Lmax →
      ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ Good : ∀ (W : CompactCarrier.{0}) (g : SmoothRiemannianMetric W.model W.Carrier) (w : ℝ),
          NearlyCuspidalBoundary W g K w → Prop,
        (¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
          ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
            (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
            boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
              Good W g w₀ B) →
      ∃ (W : ℕ → CompactCarrier.{0}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, ¬ Good (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)) ∧
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ n in atTop,
        ∃ ρ : (W n).Carrier → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
          ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ ρ ∧
          (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
          (∀ p, firstVolumeScale (g n) p w / 2 < ρ p ∧
            ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
          (∀ (i : Fin (B n).count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
            ρ (((B n).collar i).toFun q) ≤ β 1 ^ 3 / 2000) ∧
          letI := interiorChartedT_BDRY1 (W n)
          haveI := interiorManifoldT_BDRY1 (W n)
          ∃ _ : ConnectedSpace ((W n).pieceInterior ⊤),
          ∃ ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) ((W n).pieceInterior ⊤),
          ∃ O : Set ((W n).pieceInterior ⊤), IsOpen O ∧
            {x : (W n).pieceInterior ⊤ | ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x} ⊆ O ∧
            (∀ x ∈ O, ĝ.inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x) ∧
            (∀ (x : (W n).pieceInterior ⊤) (v : TangentSpace 𝓘(ℝ, E3) x),
              (pieceInteriorMetric (W n) (g n) ⊤).inner x v v ≤ ĝ.inner x v v) ∧
            letI := inducedMetricSpace ĝ
            ∃ _ : CompleteSpace ((W n).pieceInterior ⊤),
            ∃ F : LocalPacketsOn ((W n).pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
                (fun x => ρ x) (fun x => hρpos x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
                T V {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x}
                {x | ENNReal.ofReal 20 ≤ distanceToBoundary (W n) (g n) x},
              -- ranks on U₀ = {D > 5}
              (∀ x : (W n).pieceInterior ⊤,
                ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) x →
                scaledSplittingRank.{0, 0} (fun y : (W n).pieceInterior ⊤ => ρ y)
                    (fun y => hρpos y) β x =
                  @scaledSplittingRank.{0, 0} (W n).Carrier (inducedMetricSpace (g n)) ρ hρpos β
                    x) ∧
              -- every per-centre consumer domain is an actual g-ball with the distances of W
              (∀ j : (W n).pieceInterior ⊤,
                ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) j →
                Subtype.val '' Metric.ball j
                    (4 * (2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * ρ j) =
                  riemannianBallOf (g n) j.val
                    (4 * (2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * ρ j) ∧
                ∀ y ∈ Metric.ball j ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * ρ j),
                  ∀ z ∈ Metric.ball j ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * ρ j),
                    riemannianEDistOf (g n) y.val z.val = edist y z) ∧
              -- the zero balls are actual g-balls of W
              (letI := F.instMetricN
              letI := F.instChartedN
              letI := F.instMetricC
              ∀ z (hz : z ∈ F.zero.centres),
                Subtype.val '' Metric.ball z (F.zero.zero z hz).radius =
                  riemannianBallOf (g n) z.val (F.zero.zero z hz).radius) ∧
              -- weak-edge distance locality on the active edge domains
              (∀ j ∈ F.edge.centres, ∀ x ∈ Metric.ball j (200 * Δ * ρ j),
                Metric.infDist x (closure {y : (W n).pieceInterior ⊤ |
                    @isEdgePoint.{0, 0} _ ((inducedMetricSpace ĝ).rescale (ρ y)⁻¹
                      (inv_pos.mpr (hρpos y))) y Δ b' s'}) =
                  @Metric.infDist (W n).Carrier (inducedMetricSpace (g n)).toPseudoMetricSpace
                    x.val (@closure (W n).Carrier _ {y : (W n).Carrier |
                      @isEdgePoint.{0, 0} _ ((inducedMetricSpace (g n)).rescale (ρ y)⁻¹
                        (inv_pos.mpr (hρpos y))) y Δ b' s'})) := by
  obtain ⟨δS, hδS, a₂, ha₂, hP⟩ := eventually_nonempty_boundaryLocalPackets_BDRY1_IDX hσs hσs1 K hK
      A hA
  refine ⟨δS, hδS, a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hP⟩ := hP γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hP⟩ := hP βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, hP⟩ := hP β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 s b' s' i1 i2 i3 i4 i5
    i6 i7 i8 => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, hP⟩ := hP σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 s b' s' i1 i2 i3
    i4 i5 i6 i7 i8
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 => ?_⟩
  obtain ⟨w₀, hw₀, hP⟩ := hP σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5
  refine ⟨w₀, hw₀, fun w hw hww hwc b hb l1 l2 l3 l4 => ?_⟩
  obtain ⟨b₀, hb₀, hP⟩ := hP w hw hww hwc b hb l1 l2 l3 l4
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβ11 hβ3 ζ hζ1 hζ2 => ?_⟩
  obtain ⟨εr, δ', Λ', hεr, hεr1, hδ', hΛ', hP⟩ := hP β hβ2 hβ1 hβ1b hβ11 hβ3 ζ hζ1 hζ2
  refine ⟨εr, δ', Λ', hεr, hεr1, hδ', hΛ', fun T hT hTΛ e he he1 Lmax hLmax δ₀ hδ₀ hδ₀S Good
    hno => ?_⟩
  obtain ⟨W, hW, g, B, hseq⟩ :=
    exists_boundary_counterexample_sequence_of_no_threshold K A hδ₀ Good hno
  exact ⟨W, hW, g, B, fun n => (hseq n).2.2, hP T hT hTΛ e he he1 Lmax hLmax δ₀ hδ₀ hδ₀S W g B
    (fun n => (hseq n).1) (fun n => (hseq n).2.1)⟩

/-- **T3 (the LC88 row) applied to BBR03's counterexample sequence (non-vacuity of T3_IDX).** The
prefix of `lc88_boundary_collapse_packet_BDRY1_IDX`; then for `0 < δ₀ ≤ δStar` and every certificate
`Good` WITHOUT a nonempty-boundary threshold, the BBR03 counterexample sequence (members at
`δ_{n+1}`, none with `Good`) carries T3's full conclusion on one tail (export packet with
`P.cusp = B n`, the data of T2, product OR separation). -/
theorem lc88_boundary_collapse_packet_bbr03_IDX
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ δStar : ℝ, 0 < δStar ∧
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∀ εB : ℝ, 0 < εB → εB ≤ 1 / 1000 → εB ≤ β 1 ^ 2 / 1000 →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ Lmax : ℝ, 0 < Lmax →
      ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ Good : ∀ (W : CompactCarrier.{0}) (g : SmoothRiemannianMetric W.model W.Carrier) (w : ℝ),
          NearlyCuspidalBoundary W g K w → Prop,
        (¬ ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
          ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
            (g : SmoothRiemannianMetric W.model W.Carrier) (B : NearlyCuspidalBoundary W g K w₀),
            boundaryVolumeCollapsed W g w₀ → curvatureDerivativesControlled g K A w₀ →
              Good W g w₀ B) →
      ∃ (W : ℕ → CompactCarrier.{0}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, ¬ Good (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)) ∧
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ n in atTop,
        ∃ P : BoundaryExportPacket (W n) (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1)) εB,
        P.cusp = B n ∧
        ∃ ρ : (W n).Carrier → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
          ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ ρ ∧
          (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
          (∀ p, firstVolumeScale (g n) p w / 2 < ρ p ∧
            ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
          (∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
            ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000) ∧
          letI := interiorChartedT_BDRY1 (W n)
          haveI := interiorManifoldT_BDRY1 (W n)
          ∃ _ : ConnectedSpace ((W n).pieceInterior ⊤),
          ∃ ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) ((W n).pieceInterior ⊤),
          ∃ O : Set ((W n).pieceInterior ⊤), IsOpen O ∧
            {x : (W n).pieceInterior ⊤ | ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x} ⊆ O ∧
            (∀ x ∈ O, ĝ.inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x) ∧
            (∀ (x : (W n).pieceInterior ⊤) (v : TangentSpace 𝓘(ℝ, E3) x),
              (pieceInteriorMetric (W n) (g n) ⊤).inner x v v ≤ ĝ.inner x v v) ∧
            letI := inducedMetricSpace ĝ
            ∃ _ : CompleteSpace ((W n).pieceInterior ⊤),
            ∃ F : LocalPacketsOn ((W n).pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
                (fun x => ρ x) (fun x => hρpos x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
                T V {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x}
                {x | ENNReal.ofReal 20 ≤ distanceToBoundary (W n) (g n) x},
              (∀ x : (W n).pieceInterior ⊤,
                ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) x →
                scaledSplittingRank.{0, 0} (fun y : (W n).pieceInterior ⊤ => ρ y)
                    (fun y => hρpos y) β x =
                  @scaledSplittingRank.{0, 0} (W n).Carrier (inducedMetricSpace (g n)) ρ hρpos β
                    x) ∧
              (letI := F.instMetricN
              letI := F.instChartedN
              letI := F.instMetricC
              (∀ z (hz : z ∈ F.zero.centres),
                Subtype.val '' Metric.ball z (F.zero.zero z hz).radius =
                  riemannianBallOf (g n) z.val (F.zero.zero z hz).radius) ∧
              ((∃ (i j : Fin P.cusp.count), i ≠ j ∧
                ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (W n).model (Torus × Icc (0 : ℝ) 1)
                  (W n).Carrier ∞,
                  (∀ p, D p ∈ P.cusp.component i ↔ p.2.1 = 0) ∧
                    ∀ p, D p ∈ P.cusp.component j ↔ p.2.1 = 1) ∨
              ((∀ i j : Fin P.cusp.count, i ≠ j →
                Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
                  ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}) ∧
                Disjoint {x | P.level i x ≤ 90} {y | P.level j y ≤ 90} ∧
                ∀ x y, P.level i x ≤ 90 → P.level j y ≤ 90 →
                  ENNReal.ofReal 1 ≤ riemannianEDistOf (g n) x y) ∧
              (∀ z (hz : z ∈ F.zero.centres) (i : Fin P.cusp.count),
                Disjoint (riemannianBallOf (g n) z.val (F.zero.zero z hz).radius)
                  ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) ∧
              Disjoint (⋃ z, ⋃ hz : z ∈ F.zero.centres,
                  riemannianBallOf (g n) z.val (F.zero.zero z hz).radius)
                (⋃ i, tsupport (P.toBoundaryCollarPacket.block i))))) := by
  obtain ⟨δS, hδS, a₂, ha₂, hP⟩ := lc88_boundary_collapse_packet_BDRY1_IDX hσs hσs1 K hK A hA
  refine ⟨δS, hδS, a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hP⟩ := hP γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hP⟩ := hP βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, hP⟩ := hP β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 s b' s' i1 i2 i3 i4 i5
    i6 i7 i8 => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, hP⟩ := hP σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 s b' s' i1 i2 i3
    i4 i5 i6 i7 i8
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 => ?_⟩
  obtain ⟨w₀, hw₀, hP⟩ := hP σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5
  refine ⟨w₀, hw₀, fun w hw hww hwc b hb l1 l2 l3 l4 => ?_⟩
  obtain ⟨b₀, hb₀, hP⟩ := hP w hw hww hwc b hb l1 l2 l3 l4
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβ11 hβ3 ζ hζ1 hζ2 εB hεB hεB1 hεBβ => ?_⟩
  obtain ⟨εr, δ', Λ', hεr, hεr1, hδ', hΛ', hP⟩ := hP β hβ2 hβ1 hβ1b hβ11 hβ3 ζ hζ1 hζ2 εB hεB
    hεB1 hεBβ
  refine ⟨εr, δ', Λ', hεr, hεr1, hδ', hΛ', fun T hT hTΛ e he he1 Lmax hLmax δ₀ hδ₀ hδ₀S Good
    hno => ?_⟩
  obtain ⟨W, hW, g, B, hseq⟩ :=
    exists_boundary_counterexample_sequence_of_no_threshold K A hδ₀ Good hno
  exact ⟨W, hW, g, B, fun n => (hseq n).2.2, hP T hT hTΛ e he he1 Lmax hLmax δ₀ hδ₀ hδ₀S W g B
    (fun n => (hseq n).1) (fun n => (hseq n).2.1)⟩

end DifferentialGeometry.Geometry.Collapse
