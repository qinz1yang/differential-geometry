import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCollapsePacket
import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.SupportListsZero

/-!
# BCG01 on the LC88 boundary packet: zero exclusion and the four-family cover (lane BCG-1, G1)

Blueprint 207B, BCG01 (`B:8727–8820`), bound to the ONE boundary family of LC88 (T3,
`lc88_boundary_collapse_packet_BDRY1`): the export packet `P` (`P.cusp = B n`), the ORIGINAL scale
`ρ` on `W_n`, the completion `ĝ` and the packets `F : LocalPacketsOn` on `(W°, d_ĝ, ρ ∘ val)` with
`U₁ = {D > 10}`, `U₂ = {D ≥ 20}`. The physical scale is `r_∂ = β₁³/1000` (T3's collar smallness is
`ρ ≤ β₁³/2000`), `L = 10⁶Δ`, and BCG01's `r_∂ < 1/(1000L)` is the parameter request
`β₁³·10⁶Δ < 1`.

* `LocalPacketsOn.four_family_cover_BCG1`: at every point of `U₁ ∩ U₂` the four families cover
  (zero tenth balls, circle `B(j, 2ρ_j)`, slim `B(j, 2Δρ_j)`, edge `d(x, j) < 2Δρ_j`).
* `bcg01_boundary_support_lists_BCG1`: T3's prefix (plus the request), on one tail: T3's
  conclusion with T2's two transport clauses kept (consumer domains, weak-edge locality; the
  proof re-runs T3's on T2), the four-family cover on `D ≥ 35`, and in the nonproduct case, for
  every reference domain `D_a = B_g(p, C ρ(p))` (`C ≤ .95L`) meeting the `b`th closed boundary
  support: `ρ(p) < 2r_∂`, `D_a ⊂ e_b{19 < z < 91} ∩ {19 < η_b < 91}` (the SAME height `η_b` of
  `P`), no other boundary support meets `D_a`, and NO zero ball of `F` meets `D_a` (BCP05).

Not here (sheet `build-logs/resume/sheet-BCG-1.md`): the edge-collar clause and BCG02's slim case
need the enriched family (design `build-logs/resume/design-BCG-1-boundary-enrichment.md`); the
interior part of `‖DF‖` needs CGP01/CGP02 on `LocalPacketsOn`.
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **The four-family cover of `LocalPacketsOn`** at a point of `U₁ ∩ U₂`: the exhaustion on `U₂`
and the zero tenth-ball cover of `U₁ ∩ Z₀`. -/
theorem LocalPacketsOn.four_family_cover_BCG1 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ} {U₁ U₂ : Set X}
    (F : LocalPacketsOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      U₁ U₂)
    {x : X} (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂) :
    (letI := F.instMetricN
     letI := F.instChartedN
     letI := F.instMetricC
     ∃ z, ∃ hz : z ∈ F.zero.centres, x ∈ ball z ((F.zero.zero z hz).radius / 10)) ∨
    (∃ j ∈ F.circle.centres, x ∈ ball j (2 * ρ j)) ∨
    (∃ j ∈ F.slim.centres, x ∈ ball j (2 * (Δ * ρ j))) ∨
    ∃ j ∈ F.edge.centres, dist x j < 2 * Δ * ρ j := by
  rcases F.exhaustion x hx₂ with h0 | h
  · left
    let _ := F.instMetricN
    let _ := F.instChartedN
    let _ := F.instMetricC
    obtain ⟨z, hz⟩ := mem_iUnion.mp (F.zero.covers_stratum ⟨hx₁, h0⟩)
    obtain ⟨hz, hx⟩ := mem_iUnion.mp hz
    exact ⟨z, hz, hx⟩
  · exact Or.inr h

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **BCG01 on the LC88 boundary packet.** T3's prefix with BCG01's physical-scale request
`β₁³·10⁶Δ < 1` (`r_∂ = β₁³/1000 < 1/(1000L)`, `L = 10⁶Δ`). On one tail: T3's packet, scale,
completion and packets with T2's consumer-domain and weak-edge clauses, the four-family cover on
`D ≥ 35`, and in the nonproduct case BCG01 for every reference domain `B_g(p, Cρ(p))`, `C ≤ .95L`:
`ρ(p) < 2r_∂`, the band inclusion for the SAME height `η_b`, uniqueness of the meeting support, and
the exclusion of every zero ball (BCP05). -/
theorem bcg01_boundary_support_lists_BCG1
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
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} → β 1 ^ 3 * (1000000 * Δ) < 1 →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∀ εB : ℝ, 0 < εB → εB ≤ 1 / 1000 → εB ≤ β 1 ^ 2 / 1000 →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ Lmax : ℝ, 0 < Lmax →
      ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ n)) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ n in atTop,
        ∃ P : BoundaryExportPacket (W n) (g n) K A (boundaryCounterexampleRatio δ₀ n) εB,
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
              (letI := F.instMetricN
              letI := F.instChartedN
              letI := F.instMetricC
              -- the zero balls are actual g-balls of W
              (∀ z (hz : z ∈ F.zero.centres),
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
                        (inv_pos.mpr (hρpos y))) y Δ b' s'})) ∧
              -- BCG01: the four-family cover on `D ≥ 35`
              (∀ x : (W n).pieceInterior ⊤,
                ENNReal.ofReal 35 ≤ distanceToBoundary (W n) (g n) x →
                (∃ z, ∃ hz : z ∈ F.zero.centres,
                  x ∈ Metric.ball z ((F.zero.zero z hz).radius / 10)) ∨
                (∃ j ∈ F.circle.centres, x ∈ Metric.ball j (2 * ρ j)) ∨
                (∃ j ∈ F.slim.centres, x ∈ Metric.ball j (2 * (Δ * ρ j))) ∨
                ∃ j ∈ F.edge.centres, dist x j < 2 * Δ * ρ j) ∧
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
                (⋃ i, tsupport (P.toBoundaryCollarPacket.block i)) ∧
              -- BCG01 on every reference domain meeting a boundary support
              ∀ (p : (W n).Carrier) (C : ℝ), C ≤ 95 / 100 * (1000000 * Δ) →
                ∀ bb : Fin P.cusp.count,
                (∃ x ∈ tsupport (P.toBoundaryCollarPacket.block bb),
                  riemannianEDistOf (g n) p x < ENNReal.ofReal (C * ρ p)) →
                ρ p < β 1 ^ 3 / 500 ∧
                (∀ y ∈ riemannianBallOf (g n) p (C * ρ p), ∃ q ∈ cuspDomain,
                  (P.cusp.collar bb).toFun q = y ∧ 19 < q.2.val 0 ∧ q.2.val 0 < 91 ∧
                  19 < P.height bb y ∧ P.height bb y < 91) ∧
                (∀ bb' : Fin P.cusp.count, (∃ x ∈ tsupport (P.toBoundaryCollarPacket.block bb'),
                  riemannianEDistOf (g n) p x < ENNReal.ofReal (C * ρ p)) → bb' = bb) ∧
                ∀ z (hz : z ∈ F.zero.centres),
                  Disjoint (riemannianBallOf (g n) p (C * ρ p))
                    (riemannianBallOf (g n) z.val (F.zero.zero z hz).radius)))) := by
  obtain ⟨δ2, hδ2, a₂, ha₂, hT2⟩ :=
    eventually_nonempty_boundaryLocalPackets_BDRY1 hσs hσs1 K hK A hA
  obtain ⟨δP, hδP, hpair⟩ := bsa06_pair_BDRY2.{0}
  obtain ⟨δC, hδC, hcurv⟩ := bsa04_row.{0}
  refine ⟨min δ2 (min δP δC), lt_min hδ2 (lt_min hδP hδC), a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hT2⟩ := hT2 γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hT2⟩ := hT2 βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔpos : 0 < Δ := lt_trans (div_pos (by norm_num) hβ₂) hΔ
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, hT2⟩ := hT2 β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 s b' s' i1 i2 i3 i4 i5
    i6 i7 i8 => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, hT2⟩ := hT2 σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 s b' s' i1 i2 i3
    i4 i5 i6 i7 i8
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 => ?_⟩
  obtain ⟨w₀, hw₀, hT2⟩ := hT2 σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5
  refine ⟨w₀, hw₀, fun w hw hww hwc b hb l1 l2 l3 l4 => ?_⟩
  obtain ⟨b₀, hb₀, hT2⟩ := hT2 w hw hww hwc b hb l1 l2 l3 l4
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβ11 hβ3 hreq ζ hζ1 hζ2 εB hεB hεB1 hεBβ => ?_⟩
  obtain ⟨εr, δ', Λ', hεr, hεr1, hδ', hΛ', hT2⟩ := hT2 β hβ2 hβ1 hβ1b hβ11 hβ3 ζ hζ1 hζ2
  refine ⟨εr, δ', Λ', hεr, hεr1, hδ', hΛ', fun T hT hTΛ e he he1 Lmax hLmax δ₀ hδ₀ hδ₀S W _ g B
    hcoll hder => ?_⟩
  obtain ⟨V, hTV, δ, hδ, hδδ', hev⟩ := hT2 T hT hTΛ e he he1 Lmax hLmax δ₀ hδ₀
    (hδ₀S.trans (min_le_left _ _)) W g B hcoll hder
  refine ⟨V, hTV, δ, hδ, hδδ', ?_⟩
  have hV0 : 0 ≤ V := hT.le.trans hTV
  obtain ⟨hw', hw'c⟩ := lpa01_volume_bounds_BDRY5 hΛ hw hwc
  have hβsq : 0 < β 1 ^ 2 / 1000 := by positivity
  have hnR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hev, hnR.eventually_ge_atTop 3,
    hnR.eventually_ge_atTop (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))⁻¹,
    hnR.eventually_ge_atTop (300 * V + 1), hnR.eventually_ge_atTop (1 / (16 * (β 1 ^ 2 / 1000))),
    hnR.eventually_ge_atTop (6408 / 16)] with n hn hn3 hnw hn300 hnβ hn6408
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith only [hn3])
  have hn0 : (0 : ℝ) < n := by linarith only [hn3]
  have hK2 : 2 ≤ K := le_trans (by norm_num) hK
  have hδβ : boundaryCounterexampleRatio δ₀ n ≤ β 1 ^ 2 / 1000 :=
    boundaryCounterexampleRatio_le_of_BDRY5 δ₀ hβsq hn1 (one_le_sixteen_mul_of_ge_BDRY5 hβsq hnβ)
  have hδ6408 : boundaryCounterexampleRatio δ₀ n ≤ 1 / 6408 :=
    boundaryCounterexampleRatio_le_of_BDRY5 δ₀ (by norm_num) hn1 (by linarith only [hn6408])
  have h300 : 300 * V < n := by linarith only [hn300]
  have hratio0 : 0 ≤ boundaryCounterexampleRatio δ₀ n :=
    (boundaryCounterexampleRatio_pos hδ₀ hn1).le
  have hnw' : (n : ℝ)⁻¹ ≤ w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := (inv_le_comm₀ hn0 hw').mpr hnw
  obtain ⟨ρ, hρpos, hsm, hlip, hlc, hcol, hconn, ĝ, O, hO, hKO, heqO, hle, hcN, F, hrank, hdom,
    hzball, hweak⟩ := hn
  obtain ⟨P, hP⟩ := exists_boundaryExportPacket_cusp_eq_BDRY3 (B n) (hcoll n) (hder n)
    hK2 hδ6408 hεB hεB1 (A := A)
  -- BCP04.a and the curvature scale at every point (the original scale `ρ < 2 r(w')`)
  have hbcp : ∀ p : (W n).Carrier, 0 < distanceToBoundary (W n) (g n) p →
      (n : ℝ) * (distanceToBoundary (W n) (g n) p).toReal /
          ((distanceToBoundary (W n) (g n) p).toReal + 3) <
        (distanceToBoundary (W n) (g n) p).toReal / ρ p := fun p hp =>
    (hpair (W n) (g n) K _ hK2 hratio0
      ((boundaryCounterexampleRatio_le δ₀ n).trans
        (hδ₀S.trans ((min_le_right _ _).trans (min_le_left _ _)))) (B n)
      (hcoll n) (hder n) hA hn3 (boundaryCounterexampleRatio_mul_le δ₀ hn1) hnw' hw'c p (hρpos p)
      (hlc p).2.le).2.2.2 hp
  have hscale : ∀ p : (W n).Carrier,
      ENNReal.ofReal ((n : ℝ) * ρ p) < curvatureRadius (g n) p := by
    intro p
    have hst := (hcurv (W n) (g n) K _ hK2 hratio0
      ((boundaryCounterexampleRatio_le δ₀ n).trans
        (hδ₀S.trans ((min_le_right _ _).trans (min_le_right _ _)))) (B n) (hcoll n) (hder n)
      hn3 (boundaryCounterexampleRatio_mul_le δ₀ hn1) p).1
    exact ofReal_mul_lt_of_scale_BDRY5 hst
      (firstVolumeScale_anti_of_le (g n) p (inv_pos.mpr hn0) hnw') (hlc p).2 hn0
  -- the collar smallness for `P`
  have hcolP : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000 := by
    rw [hP]
    exact hcol
  have hsmall : ∀ (i : Fin P.cusp.count), ∀ q ∈ cuspDomain, q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / (2000 * (1 + 0)) := by
    intro i q _ hq
    have h := hcolP i q hq
    rwa [add_zero, mul_one]
  let instM_BCG1 : MetricSpace ((W n).pieceInterior ⊤) := inducedMetricSpace ĝ
  let _ := F.instMetricN
  let _ := F.instChartedN
  let _ := F.instMetricC
  -- every actual zero ball misses every full enlarged collar (T3's argument)
  have hsep : ∀ z (hz : z ∈ F.zero.centres) (i : Fin P.cusp.count),
      Disjoint (riemannianBallOf (g n) z.val (F.zero.zero z hz).radius)
        ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}) := by
    intro z hz i
    have hz10 : ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) z := F.zero.centres_subset hz
    have hR : (F.zero.zero z hz).radius ≤ V * ρ z := (F.zero.radius_mem z hz).2
    have hRpos : 0 < (F.zero.zero z hz).radius := (F.zero.zero z hz).radius_pos
    have hR5 := ofReal_radius_add_five_le_BDRY5 (W n) (g n) ρ hρpos hbcp h300 z.val hz10 hR
    obtain ⟨y, hyball, hy0⟩ := F.zero.meets_stratum z hz
    have hyg : y.val ∈ riemannianBallOf (g n) z.val (F.zero.zero z hz).radius := by
      rw [← hzball z hz]
      exact ⟨y, hyball, rfl⟩
    have hy5 : ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) y :=
      ofReal_five_lt_distanceToBoundary_BDRY1 (W n) (g n) hRpos.le hR5 hyg
    have hyW : @scaledSplittingRank.{0, 0} (W n).Carrier (inducedMetricSpace (g n)) ρ hρpos β
        y.val = 0 := by
      rw [← hrank y hy5]
      exact hy0
    exact P.zeroBall_disjoint_enlargedCollar_96 i ρ hρpos β ζ 0 hβ1 hζ1 hζ2 le_rfl hδβ hεBβ
      (hsmall i) z.val _ V n hV0 h300 hR (hscale z.val) hz10 ⟨y.val, hyg, hyW⟩
  -- the four-family cover on `D ≥ 35`
  have hcover : ∀ x : (W n).pieceInterior ⊤,
      ENNReal.ofReal 35 ≤ distanceToBoundary (W n) (g n) x →
      (∃ z, ∃ hz : z ∈ F.zero.centres, x ∈ Metric.ball z ((F.zero.zero z hz).radius / 10)) ∨
      (∃ j ∈ F.circle.centres, x ∈ Metric.ball j (2 * ρ j)) ∨
      (∃ j ∈ F.slim.centres, x ∈ Metric.ball j (2 * (Δ * ρ j))) ∨
      ∃ j ∈ F.edge.centres, dist x j < 2 * Δ * ρ j := by
    intro x hx
    have hx₁ : ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x :=
      lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 35)).mpr
        (by norm_num : (10 : ℝ) < 35)) hx
    have hx₂ : ENNReal.ofReal 20 ≤ distanceToBoundary (W n) (g n) x :=
      le_trans (ENNReal.ofReal_le_ofReal (by norm_num : (20 : ℝ) ≤ 35)) hx
    exact F.four_family_cover_BCG1 hx₁ hx₂
  refine ⟨P, hP, ρ, hρpos, hsm, hlip, hlc, hcolP, hconn, ĝ, O, hO, hKO, heqO, hle, hcN, F, hrank,
    hdom, hzball, hweak, hcover, ?_⟩
  rcases P.alternative with hprod | hdisj
  · exact Or.inl hprod
  · refine Or.inr ⟨hdisj, hsep, ?_, ?_⟩
    · apply Set.disjoint_left.mpr
      intro x hx hb
      obtain ⟨z, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hz, hx⟩ := mem_iUnion.mp hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hb
      obtain ⟨q, hq, hqx⟩ := P.toBoundaryCollarPacket.tsupport_block_subset i hi
      have hq92 : q.2.val 0 < 92 := by
        have hh : q.2.val 0 ≤ 90 + εB := hq.2
        linarith only [hh, hεB1]
      exact Set.disjoint_left.mp (hsep z hz i) hx ⟨q, hq92, hqx⟩
    · intro p C hC bb hmeet
      obtain ⟨hL, hΛC, hr, -⟩ := bcg01_parameters_BCG1 hΛ hΔpos hβ1 k3 hC hreq (le_refl _)
      have hεB4 : εB ≤ 1 / 4 := by linarith only [hεB1]
      have hsmallr : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
          ρ ((P.cusp.collar i).toFun q) < β 1 ^ 3 / 1000 := fun i q hq =>
        (bcg01_parameters_BCG1 hΛ hΔpos hβ1 k3 hC hreq (hcolP i q hq)).2.2.2
      obtain ⟨hρp, hband, hzero⟩ := P.toBoundaryCollarPacket.bcg01_zero_exclusion_BCG1 hεB4 hρpos
        hΛ.le hlip hsmallr hL hC hΛC hr hmeet
        (fun z : {z // z ∈ F.zero.centres} => z.1.val)
        (fun z => (F.zero.zero z.1 z.2).radius) (fun z => hsep z.1 z.2 bb)
      refine ⟨by linarith only [hρp], hband, fun bb' hbb' => ?_, fun z hz => hzero ⟨z, hz⟩⟩
      exact P.toBoundaryCollarPacket.subsingleton_supports_meeting_reference_domain hεB4
        (fun i j hij => (hdisj i j hij).1) hρpos hΛ.le hlip hsmallr hL hC hΛC hr p hbb' hmeet

end DifferentialGeometry.Geometry.Collapse
