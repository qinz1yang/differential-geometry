import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalBindingB
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLocalPacketsProducer

/-!
# T2B — the enriched boundary base family on one tail (lane BCG-2, review 51 Q5)

Review 51, question 5 (binding): ONE enhanced T2 producing ONE family, then T3's separation proof
re-run on the SAME output (next module); never a conjunction of two existence statements. This
module is the enhanced T2: the proof of `eventually_nonempty_boundaryLocalPackets_BDRY1` with the
enriched binding `exists_interior_chartFamilyEAB_BCG2` in place of
`exists_interior_chartFamilyEA_BDRY5` (two edge families from one edge threshold chain, LFR19's slim
value, BE-1's circle residual and edge disk packets / sections) and ONE late tail
`n ≥ max(8 Lbig, 2300Δ, 16, 32 C_b, 32 R_β, 32(600Δ + 2b'⁻¹))`.

* `eventually_nonempty_boundaryPacketsB_BCG2` (see its docstring).
Plug points for lane BZ-1 (review 51 P0-B zero certificates, P0-C(i) requested cap) are marked in
the proof; the final boundary family is assembled after BZ-1 delivers.
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

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **T2B: the enriched boundary base family on one tail** (review 51 Q5; T2's shape, ONE family).
T2's prefix with `σs, vs` after `b` (immediately before `b₀`) and BE-1's requests (`ε, μ ≤ 10⁻⁸`,
`100ΔΛ ≤ 10⁻⁸`, `∃ bd₀` after `w`). On one tail: T2's data (ONE original scale `ρ`, ONE completion
`ĝ`), BCP04.a at the index `n`, and ONE `F : LocalPacketsOnB … vs {D > 10} {D ≥ 20} {D > 20}
{D ≥ 35}` with T2's transport clauses (ranks on `{D > 5}`, consumer domains, zero balls as
`g`-balls, weak-edge distance locality on the domains of the inherited AND of the revised edge
family), and the same-chart certificates of BE-1 on the SAME `F` — LFR07's residual on
`F.circle`, LC84 disk packets and EGP05 sections on `F.edgeB` (plug points of the final family,
review 51 P0-B).
PLUG POINTS (BZ-1, review 51 P0-B/P0-C(i)): the zero family is T2's (`εr = 1/8`, zero balls as
`g`-balls); BZ-1's certified zero producer (requested cap, local comparison, shell splitting,
adapted tests, enlarged curvature) replaces the call marked in the proof. -/
theorem eventually_nonempty_boundaryPacketsB_BCG2
    (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ δStar : ℝ, 0 < δStar ∧
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 → ε ≤ 1 / 10 ^ 8 → μ ≤ 1 / 10 ^ 8 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) → 100 * Δ * Λ ≤ 1 / 10 ^ 8 →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 → ∃ bd₀ : ℝ, 0 < bd₀ ∧
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → b < bd₀ →
      ∀ σs vs : ℝ, 0 < σs → σs ≤ 1 / 100 → 0 < vs → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
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
        ∃ ρ : (W n).Carrier → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
          ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ ρ ∧
          (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
          (∀ p, firstVolumeScale (g n) p w / 2 < ρ p ∧
            ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
          (∀ (i : Fin (B n).count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
            ρ (((B n).collar i).toFun q) ≤ β 1 ^ 3 / 2000) ∧
          (∀ p, 0 < distanceToBoundary (W n) (g n) p →
            (n : ℝ) * (distanceToBoundary (W n) (g n) p).toReal /
                ((distanceToBoundary (W n) (g n) p).toReal + 3) <
              (distanceToBoundary (W n) (g n) p).toReal / ρ p) ∧
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
            ∃ F : LocalPacketsOnB ((W n).pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
                (fun x => ρ x) (fun x => hρpos x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
                T V vs {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x}
                {x | ENNReal.ofReal 20 ≤ distanceToBoundary (W n) (g n) x}
                {x | ENNReal.ofReal 20 < distanceToBoundary (W n) (g n) x}
                {x | ENNReal.ofReal 35 ≤ distanceToBoundary (W n) (g n) x},
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
                        (inv_pos.mpr (hρpos y))) y Δ b' s'})) ∧
              -- weak-edge distance locality on the revised (active) edge domains
              (∀ j ∈ F.edgeB.centres, ∀ x ∈ Metric.ball j (200 * Δ * ρ j),
                Metric.infDist x (closure {y : (W n).pieceInterior ⊤ |
                    @isEdgePoint.{0, 0} _ ((inducedMetricSpace ĝ).rescale (ρ y)⁻¹
                      (inv_pos.mpr (hρpos y))) y Δ b' s'}) =
                  @Metric.infDist (W n).Carrier (inducedMetricSpace (g n)).toPseudoMetricSpace
                    x.val (@closure (W n).Carrier _ {y : (W n).Carrier |
                      @isEdgePoint.{0, 0} _ ((inducedMetricSpace (g n)).rescale (ρ y)⁻¹
                        (inv_pos.mpr (hρpos y))) y Δ b' s'})) ∧
              -- BE-1: LFR07's residual enclosure on the circle charts (review 51 A2)
              (∀ j (hj : j ∈ F.circle.centres),
                let c := F.circle.chart j hj
                letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
                ∀ x ∈ Metric.ball j 200, ‖c.coord x‖ ≤ 8 → x ∈ Metric.ball j 10) ∧
              -- BE-1: LC84 disk packets of the revised edge charts (review 51 A1)
              (∀ j (hj : j ∈ F.edgeB.centres),
                let c := F.edgeB.chart j hj
                let Fs := F.edgeB.smoothing
                let A : Set ((W n).pieceInterior ⊤) := closure
                  {y | @isEdgePoint.{0, 0} ((W n).pieceInterior ⊤)
                    ((inducedMetricSpace ĝ).rescale (ρ y)⁻¹ (inv_pos.mpr (hρpos y))) y Δ b' s'}
                let hMc : CompleteSpace ((W n).pieceInterior ⊤) :=
                  ‹CompleteSpace ((W n).pieceInterior ⊤)›
                letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
                letI := radialScaledBundle ĝ (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
                letI : IsContinuousRiemannianBundle E3
                    (fun x : (W n).pieceInterior ⊤ => TangentSpace 𝓘(ℝ, E3) x) :=
                  radialScaledContinuous ĝ (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
                letI : IsRiemannianManifold 𝓘(ℝ, E3) ((W n).pieceInterior ⊤) :=
                  radialScaledManifold (m := inducedMetricSpace ĝ) ĝ
                    (inducedMetricSpace_hmetric ĝ) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
                letI : CompleteSpace ((W n).pieceInterior ⊤) :=
                  ((inducedMetricSpace ĝ).rescale_completeSpace_iff (ρ j)⁻¹
                    (inv_pos.mpr (hρpos j))).mpr hMc
                let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) ((W n).pieceInterior ⊤) :=
                  scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos j)) 2) ĝ
                have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := (W n).pieceInterior ⊤) gR :=
                  isMetricNorm_of_riemannianBundle gR
                ∃ P : EdgeDiskPacket gR hnR Δ σc μ b γc βc A (fun x => ρ x / ρ j)
                  (fun x => Fs x / ρ j), P.toEdgeChart = c) ∧
              -- BE-1: EGP05 sections of the revised edge charts (review 51 A7)
              (∀ j (hj : j ∈ F.edgeB.centres),
                let c := F.edgeB.chart j hj
                let Fs := F.edgeB.smoothing
                let hMc : CompleteSpace ((W n).pieceInterior ⊤) :=
                  ‹CompleteSpace ((W n).pieceInterior ⊤)›
                letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
                letI := radialScaledBundle ĝ (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
                letI : IsContinuousRiemannianBundle E3
                    (fun x : (W n).pieceInterior ⊤ => TangentSpace 𝓘(ℝ, E3) x) :=
                  radialScaledContinuous ĝ (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
                letI : IsRiemannianManifold 𝓘(ℝ, E3) ((W n).pieceInterior ⊤) :=
                  radialScaledManifold (m := inducedMetricSpace ĝ) ĝ
                    (inducedMetricSpace_hmetric ĝ) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
                letI : CompleteSpace ((W n).pieceInterior ⊤) :=
                  ((inducedMetricSpace ĝ).rescale_completeSpace_iff (ρ j)⁻¹
                    (inv_pos.mpr (hρpos j))).mpr hMc
                ∃ sec : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ) → (W n).pieceInterior ⊤, Continuous sec ∧
                  ∀ a : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ), c.coord (sec a) = a ∧
                    Fs (sec a) / ρ j / (ρ (sec a) / ρ j) < Δ / 100 ∧
                      dist (sec a) j < 10 * Δ) := by
  obtain ⟨δZ, hδZ, hZ⟩ := eventually_zeroModelFamilyOn_gBalls_boundary_BDRY3
  obtain ⟨δR, hδR, hR⟩ := bsa06_row_eventually_strict_BDRY4.{0}
  obtain ⟨a₂, ha₂, hbind⟩ := exists_interior_chartFamilyEAB_BCG2 K (by omega) A
  refine ⟨min δZ δR, lt_min hδZ hδR, a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hbind⟩ := hbind γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hbind⟩ := hbind βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔpos : 0 < Δ := lt_trans (div_pos (by norm_num) hβ₂) hΔ
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, hbind⟩ := hbind β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ _ hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b' s'
    hs hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  have hb'pos : 0 < b' := by have := hs.trans hsb'; linarith
  obtain ⟨a₀, b₁, ha₀, hb₁, hbind⟩ := hbind σc ε μ τ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s
    b' s' hs hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 => ?_⟩
  have hΔΛ : 600 * Δ * Λ ≤ 1 := by linarith [mul_pos hΔpos hΛ]
  obtain ⟨w₀, hw₀, hbind⟩ := hbind σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8
  have hvol4 : 0 < euclideanThreeUnitBallVolume / 4 := by
    unfold euclideanThreeUnitBallVolume; positivity
  refine ⟨min w₀ (euclideanThreeUnitBallVolume / 4), lt_min hw₀ hvol4,
    fun w hw hww hwc => ?_⟩
  obtain ⟨bd₀, hbd₀, hbind⟩ := hbind w hw (hww.trans_le (min_le_left _ _))
  refine ⟨bd₀, hbd₀, fun b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs => ?_⟩
  obtain ⟨b₀, hb₀, hbind⟩ := hbind b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβ11 hβ3 ζ _ _ => ?_⟩
  obtain ⟨δ', Λ', hδ', hΛ', hZ⟩ := hZ K hK A hA hβ1 hβ11
  refine ⟨1 / 8, δ', Λ', by norm_num, by norm_num, hδ', hΛ', fun T hT hTΛ e he he1 Lmax _ δ₀
    hδ₀ hδ₀S W _ g B hcoll hder => ?_⟩
  obtain ⟨L₀, hL₀, hbind⟩ := hbind β hβ2 hβ1 hβ1b hβ3 Lmax
  -- ONE completion at cut height `4` for every `n`, before `V`
  have hT1 := fun n => exists_interior_completion_cut_BDRY1 (W n) (g n) (a := 4) (by norm_num)
  choose ĝ O hcomp hO hKO heqO hle using hT1
  have heq4 : ∀ n (x : (W n).pieceInterior ⊤),
      ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x →
        (ĝ n).inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x :=
    fun n x hx => heqO n x (hKO n hx)
  -- the ORIGINAL scale (strict BSA05 / BSA06)
  obtain ⟨ρ, hρev, hρcol⟩ := hR hδ₀ (hδ₀S.trans (min_le_right _ _)) K (by omega) A hA W g B
    hcoll hder hΛ hw (hww.trans_le (min_le_right _ _))
  -- the zero family on the completion
  -- PLUG POINT (BZ-1, review 51 P0-C(i)): requested cap `εr < cap` chosen before the joint zero
  -- witness and `V`; certified zero producer in place of the call below.
  obtain ⟨V, hTV, δ, hδ, hδδ', hzero⟩ := hZ (εr := 1 / 8) (by norm_num) (by norm_num) hT hTΛ he
    he1 hΛ hw hwc hδ₀ (hδ₀S.trans (min_le_left _ _)) W g B hcoll hder ĝ hcomp heq4 hle
  refine ⟨V, hTV, δ, hδ, hδδ', ?_⟩
  have hV0 : 0 ≤ V := (hT.le.trans hTV)
  have hβi1 : 0 < (β 1)⁻¹ := inv_pos.mpr hβ1
  have hbi : 0 < b⁻¹ := inv_pos.mpr hb
  have hb'i : 0 < b'⁻¹ := inv_pos.mpr hb'pos
  -- no `set` here: abstracting a subterm of the (large) goal times out
  have hCb0 : 0 ≤ 2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹ := by positivity
  have hnR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  -- `filter_upwards` would `dsimp` the (large) goal: combine the tail facts by hand instead
  have hev := ((((((((hρev.and (hρcol (β 1 ^ 3 / 2000) (by positivity))).and hzero).and
    (hnR.eventually_ge_atTop (8 * max L₀ Lmax))).and (hnR.eventually_ge_atTop (2300 * Δ))).and
    (hnR.eventually_ge_atTop 16)).and
    (hnR.eventually_ge_atTop (32 * (2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹)))).and
    (hnR.eventually_ge_atTop (32 * (1 + |(β 0)⁻¹| + |(β 1)⁻¹| + |(β 2)⁻¹| + |(β 3)⁻¹|)))).and
    (hnR.eventually_ge_atTop (32 * (600 * Δ + 2 * b'⁻¹))))
  refine hev.mono ?_
  rintro n ⟨⟨⟨⟨⟨⟨⟨⟨hρn, hcn⟩, hzn⟩, h8⟩, h2300⟩, h16⟩, hnC⟩, hnRβ⟩, hnE⟩
  obtain ⟨hρpos, hsm, hlc, hlip, hdata⟩ := hρn
  have hcn' : ∀ (i : Fin (B n).count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ n (((B n).collar i).toFun q) ≤ β 1 ^ 3 / 2000 := fun i q hq => (hcn i q hq).le
  have h2Λ : (2 : ℝ) / Λ = 2 * Λ⁻¹ := div_eq_mul_inv 2 Λ
  have hlc' : ∀ p, firstVolumeScale (g n) p w / 2 < ρ n p ∧
      ρ n p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) := by
    intro p
    have h := hlc p
    rw [h2Λ] at h
    exact h
  have hbcp : ∀ p, 0 < distanceToBoundary (W n) (g n) p →
      (n : ℝ) * (distanceToBoundary (W n) (g n) p).toReal /
          ((distanceToBoundary (W n) (g n) p).toReal + 3) <
        (distanceToBoundary (W n) (g n) p).toReal / ρ n p := fun p => (hdata p).2.2.2.1
  have hpos5 : ∀ x : (W n).pieceInterior ⊤,
      ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x →
        ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) x := fun x hx =>
    lt_trans ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 10)).mpr
      (by norm_num : (5 : ℝ) < 10)) hx
  -- the family of the regionalised kernel on `(W°, ĝ)`
  obtain ⟨hcN, L, ⟨hAd⟩, hres, hval, edgeB, hcoarseB, hdiskB, hsecB, hdomB, hexhB⟩ :=
    hbind (max L₀ Lmax) (le_max_left _ _) (le_max_right _ _) (W n) (g n) (ĝ n)
    (hcomp n) (heq4 n) (hle n) (ρ n) hρpos hsm hlip (fun p => (hlc p).1) (n : ℝ)
    (by linarith only [h8]) (by linarith only [h2300]) h16
    (fun p => ⟨(hdata p).1, (hdata p).2.1, (hdata p).2.2.1, (hdata p).2.2.2.1⟩)
  -- the zero family for THIS scale
  obtain ⟨N, C, mN, cN, mC, o, Fz, hFz⟩ := hzn (ρ n) hρpos hsm.continuous (fun p => (hlc' p).2)
    hcn'
  let instM_BDRY5 : MetricSpace ((W n).pieceInterior ⊤) := inducedMetricSpace (ĝ n)
  have hpos20 : ∀ x : (W n).pieceInterior ⊤,
      ENNReal.ofReal 20 < distanceToBoundary (W n) (g n) x →
        ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) x := fun x hx =>
    lt_trans ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 20)).mpr
      (by norm_num : (5 : ℝ) < 20)) hx
  refine ⟨ρ n, hρpos, hsm, hlip, hlc', hcn', hbcp, connectedSpace_pieceInterior_top_BDRY1 (W n),
    ĝ n, O n, hO n, hKO n, heqO n, hle n, hcN,
    { toLocalPacketsOn :=
        { toChartFamilyEOn := L
          circleAdapted := hAd
          N := N
          C := C
          instMetricN := mN
          instChartedN := cN
          instMetricC := mC
          o := o
          zero := Fz }
      slim_value := hval
      edgeB := edgeB
      edgeB_coarse := hcoarseB
      edgeB_domain := hdomB
      exhaustionB := hexhB }, ?_, ?_, hFz, ?_, ?_, hres, hdiskB, hsecB⟩
  · exact scaledSplittingRank_completion_eq_BDRY5 (W n) (g n) (ĝ n) (heq4 n) (ρ n) hρpos β hbcp
      hnRβ
  · intro j hj
    exact consumer_domain_completion_BDRY5 (W n) (g n) (ĝ n) (heq4 n) (ρ n) hρpos hCb0 hbcp hnC j
      (hpos5 j hj)
  · intro j hj x hx
    have hm := L.edge.mem_closure_weakEdge_BDRY5 hj
    exact infDist_weakEdge_completion_eq_BDRY5 (W n) (g n) (ĝ n) (heq4 n) (hle n) (ρ n) hρpos
      hΔpos hb'pos hΛ.le hΔΛ hlip hbcp hnE j (hpos5 j (L.edge.centres_subset hj)) hm x hx
  · intro j hj x hx
    have hm := edgeB.mem_closure_weakEdge_BDRY5 hj
    exact infDist_weakEdge_completion_eq_BDRY5 (W n) (g n) (ĝ n) (heq4 n) (hle n) (ρ n) hρpos
      hΔpos hb'pos hΛ.le hΔΛ hlip hbcp hnE j (hpos20 j (edgeB.centres_subset hj)) hm x hx

end DifferentialGeometry.Geometry.Collapse
