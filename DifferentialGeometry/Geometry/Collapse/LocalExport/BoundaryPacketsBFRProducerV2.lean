import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalBindingBR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLocalPacketsProducer
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroTransport
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFR

/-!
# T2B v2 on the extended final boundary family (lane BCG-5)

`eventually_nonempty_boundaryPacketsBFR_BCG5` is lane BCG-3's T2B v2
(`eventually_nonempty_boundaryPacketsBF_BCG3`; same statement, same tail, same proof) with the ONE
family `F` of the extended final boundary family `LocalPacketsOnBFR` (module `BoundaryPacketsBFR`):
its new field `rank_le_two` (rank `≤ 2` of the scale on `U₁ = {D > 10}`) is the rank bound of the
regional kernel, exported by the binding `exists_interior_chartFamilyEABR_BCG5` for the SAME scale
and the SAME call that produces the charts of `F` (producer gap found by lane BCG-4). Every other
clause is verbatim.
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
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **T2B v2 on the extended final boundary family** (lane BCG-5): BCG-3's T2B v2 with
`F : LocalPacketsOnBFR …` (new field `rank_le_two` on `{D > 10}`). Text of BCG-3:
(review 51 P0-B, P0-C(i), Q5; ONE family).
BCG-2's T2B with (1) the requested zero cap `εr < cap` chosen right after `ζ, cap`, before `T`, the
sequence, the joint zero witness and `V`; (2) `∀ Lmax` after `∃ V, ∃ δ`; (3) ONE
`F : LocalPacketsOnBF … vs ζ Λ' …` whose fields carry LFR07's residual on `F.circle`, LC84 disk
packets and EGP05 sections on `F.edgeB`, and on `F.zero` LC62, X82, LC73 (`λ ≥ Λ'`) and
`sec_ĝ ≥ -(1/60)² r_c⁻²` on `B_ĝ(c, 400 r_c)`; on the same tail T2B's ρ / ĝ / O clauses, BCP04.a at
`n`, and about the same `F`: ranks on `{D > 5}`, consumer domains as `g`-balls, zero balls as
`g`-balls, weak-edge locality for `edge` AND `edgeB`, and BZ-1's original-metric certificates
(A6') `sec_g ≥ -(1/60)² r_c⁻²` on `B_g(c, 400 r_c)`; (I) `val '' B_ĝ(c, 400 r_c) = B_g(c, 400 r_c)`
with the distances of `W`; (TD) the shell test domains inside `B(c, 11 r_c)`; (A3') LC62 for the
points of `W` with `d_g(c, q) ≤ 10 r_c`. -/
theorem eventually_nonempty_boundaryPacketsBFR_BCG5
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
      ∀ ζ cap : ℝ, β 1 < ζ → ζ < 1 → 0 < cap →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ εr < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ n)) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ Lmax : ℝ, 0 < Lmax → ∀ᶠ n in atTop,
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
            ∃ F : LocalPacketsOnBFR ((W n).pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
                (fun x => ρ x) (fun x => hρpos x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
                T V vs ζ Λ' {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x}
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
              -- BZ-1: the original-metric zero certificates of the producer v2 on `F.zero`
              (letI := F.instMetricN
              letI := F.instChartedN
              letI := F.instMetricC
              -- (A6') enlarged zero curvature of the ORIGINAL metric
              (∀ c (hc : c ∈ F.zero.centres),
                ∀ y ∈ riemannianBallOf (g n) c.val (400 * (F.zero.zero c hc).radius),
                SectionalBoundedBelowAt (g n) y
                  (-((1 / 60) ^ 2 * ((F.zero.zero c hc).radius)⁻¹ ^ 2))) ∧
              -- (I) `ĝ` is `g` on the enlarged zero balls
              (∀ c (hc : c ∈ F.zero.centres),
                Subtype.val '' Metric.ball c (400 * (F.zero.zero c hc).radius) =
                  riemannianBallOf (g n) c.val (400 * (F.zero.zero c hc).radius) ∧
                ∀ y ∈ Metric.ball c (400 * (F.zero.zero c hc).radius),
                  ∀ z ∈ Metric.ball c (400 * (F.zero.zero c hc).radius),
                    riemannianEDistOf (g n) y.val z.val = edist y z) ∧
              -- (TD) test domains inside `B(c, 11 r_c)`
              (∀ c (hc : c ∈ F.zero.centres), ∀ q, (F.zero.zero c hc).radius / 10 ≤ dist c q →
                dist c q ≤ 10 * (F.zero.zero c hc).radius →
                (∀ x ∈ @Metric.ball _ ((inducedMetricSpace ĝ).rescale (ρ q)⁻¹
                    (inv_pos.mpr (hρpos q))).toPseudoMetricSpace q (β 1)⁻¹,
                  x ∈ Metric.ball c (11 * (F.zero.zero c hc).radius)) ∧
                ∀ (lam : ℝ) (hlam : 0 < lam), Λ' ≤ lam →
                  ∀ x ∈ @Metric.ball _ (((inducedMetricSpace ĝ).rescale
                      ((F.zero.zero c hc).radius)⁻¹
                      (inv_pos.mpr (F.zero.zero c hc).radius_pos)).rescale lam
                      hlam).toPseudoMetricSpace q ζ⁻¹,
                    x ∈ Metric.ball c (11 * (F.zero.zero c hc).radius)) ∧
              -- (A3') LC62 for the points of `W`
              ∀ c (hc : c ∈ F.zero.centres), ∀ q : (W n).Carrier,
                riemannianEDistOf (g n) c.val q ≤
                  ENNReal.ofReal (10 * (F.zero.zero c hc).radius) →
                T / 20 ≤ (F.zero.zero c hc).radius / ρ q) := by
  -- `obtain`/`rintro` would re-check the (large) goal in every `cases` motive: destructure every
  -- supplier by `Exists.elim` and projections instead
  refine eventually_zeroModelFamilyOn_certified_gBalls_boundary_BZ1.elim fun δZ hZ => ?_
  refine (bsa06_row_eventually_strict_BDRY4.{0}).elim fun δR hR => ?_
  refine (exists_interior_chartFamilyEABR_BCG5 K (by omega) A).elim fun a₂ k1 => ?_
  refine ⟨min δZ δR, lt_min hZ.1 hR.1, a₂, k1.1, fun γ hγ hγ1 => ?_⟩
  refine (k1.2 γ hγ hγ1).elim fun β₀ k2 => ?_
  refine ⟨β₀, k2.1, k2.2.1, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  refine (k2.2.2 βc γc hβc hβγ hγc hγc1).elim fun σ₀ k3 => ?_
  refine k3.2.elim fun Δ₀ k4 => ?_
  refine ⟨σ₀, k3.1, Δ₀, k4.1, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔpos : 0 < Δ := lt_trans (div_pos (by norm_num) hβ₂) hΔ
  refine (k4.2 β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ).elim fun τ₀ k5 => ?_
  refine k5.2.elim fun bc₀ k6 => ?_
  refine ⟨τ₀, k5.1, bc₀, k6.1, fun σc ε μ τ hσc hσcσ₀ _ hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b' s'
    hs hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  have hb'pos : 0 < b' := by have := hs.trans hsb'; linarith
  refine (k6.2 σc ε μ τ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b' s' hs hssmall hsb' hss'
    hb'd hs'd hb'e hs'e).elim fun a₀ k7 => ?_
  refine k7.elim fun b₁ k8 => ?_
  refine ⟨a₀, b₁, k8.1, k8.2.1,
    fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 => ?_⟩
  have hΔΛ : 600 * Δ * Λ ≤ 1 := by linarith [mul_pos hΔpos hΛ]
  refine (k8.2.2 σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8).elim fun w₀ k9 => ?_
  have hvol4 : 0 < euclideanThreeUnitBallVolume / 4 := by
    unfold euclideanThreeUnitBallVolume; positivity
  refine ⟨min w₀ (euclideanThreeUnitBallVolume / 4), lt_min k9.1 hvol4,
    fun w hw hww hwc => ?_⟩
  refine (k9.2 w hw (hww.trans_le (min_le_left _ _))).elim fun bd₀ k10 => ?_
  refine ⟨bd₀, k10.1, fun b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs => ?_⟩
  refine (k10.2 b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs).elim fun b₀ k11 => ?_
  refine ⟨b₀, k11.1, fun β hβ2 hβ1 hβ1b hβ11 hβ3 ζ cap hβζ hζone hcap => ?_⟩
  -- the requested cap enters the zero producer before the joint witness and `V`
  refine (hZ.2 K hK A hA hβ1 hβ11 hβζ hζone hcap).elim fun εr z1 => ?_
  refine z1.elim fun δ' z2 => ?_
  refine z2.elim fun Λ' z3 => ?_
  refine ⟨εr, δ', Λ', z3.1, z3.2.1, z3.2.2.1, z3.2.2.2.1, z3.2.2.2.2.1, fun T hT hTΛ e he he1 δ₀
    hδ₀ hδ₀S W _ g B hcoll hder => ?_⟩
  -- ONE completion at cut height `4` for every `n`, before `V`
  have hT1 := fun n => exists_interior_completion_cut_BDRY1 (W n) (g n) (a := 4) (by norm_num)
  choose ĝ O hcomp hO hKO heqO hle using hT1
  have heq4 : ∀ n (x : (W n).pieceInterior ⊤),
      ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x →
        (ĝ n).inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x :=
    fun n x hx => heqO n x (hKO n hx)
  -- the ORIGINAL scale (strict BSA05 / BSA06)
  refine (hR.2 hδ₀ (hδ₀S.trans (min_le_right _ _)) K (by omega) A hA W g B hcoll hder hΛ hw
    (hww.trans_le (min_le_right _ _))).elim fun ρ hρ => ?_
  -- the certified zero family on the completion (BZ-1's producer v2)
  refine (z3.2.2.2.2.2 hT hTΛ he he1 hΛ hw hwc hδ₀ (hδ₀S.trans (min_le_left _ _)) W g B hcoll hder
    ĝ hcomp heq4 hle).elim fun V v1 => ?_
  refine v1.2.elim fun δ v2 => ?_
  -- `Lmax` after `V`: `V` comes from the zero producer alone; the chart binding takes `Lmax` now
  refine ⟨V, v1.1, δ, v2.1, v2.2.1, fun Lmax _ => ?_⟩
  refine (k11.2 β hβ2 hβ1 hβ1b hβ3 Lmax).elim fun L₀ l1 => ?_
  have hbind := l1.2
  have hV0 : 0 ≤ V := hT.le.trans v1.1
  have hβi1 : 0 < (β 1)⁻¹ := inv_pos.mpr hβ1
  have hbi : 0 < b⁻¹ := inv_pos.mpr hb
  have hb'i : 0 < b'⁻¹ := inv_pos.mpr hb'pos
  -- no `set` here: abstracting a subterm of the (large) goal times out
  have hCb0 : 0 ≤ 2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹ := by positivity
  have hnR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  -- `filter_upwards` would `dsimp` the (large) goal: combine the tail facts by hand instead
  have hev := hρ.1.and ((hρ.2 (β 1 ^ 3 / 2000) (by positivity)).and (v2.2.2.and
    ((hnR.eventually_ge_atTop (8 * max L₀ Lmax)).and ((hnR.eventually_ge_atTop (2300 * Δ)).and
    ((hnR.eventually_ge_atTop 16).and
    ((hnR.eventually_ge_atTop (32 * (2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹))).and
    ((hnR.eventually_ge_atTop (32 * (1 + |(β 0)⁻¹| + |(β 1)⁻¹| + |(β 2)⁻¹| + |(β 3)⁻¹|))).and
    (hnR.eventually_ge_atTop (32 * (600 * Δ + 2 * b'⁻¹))))))))))
  refine hev.mono fun n hn => ?_
  have hρpos := hn.1.fst
  have hsm := hn.1.snd.1
  have hlc := hn.1.snd.2.1
  have hlip := hn.1.snd.2.2.1
  have hdata := hn.1.snd.2.2.2
  have hcn' : ∀ (i : Fin (B n).count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ n (((B n).collar i).toFun q) ≤ β 1 ^ 3 / 2000 := fun i q hq => (hn.2.1 i q hq).le
  have hzn := hn.2.2.1
  have h8 := hn.2.2.2.1
  have h2300 := hn.2.2.2.2.1
  have h16 := hn.2.2.2.2.2.1
  have hnC := hn.2.2.2.2.2.2.1
  have hnRβ := hn.2.2.2.2.2.2.2.1
  have hnE := hn.2.2.2.2.2.2.2.2
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
  have hpos20 : ∀ x : (W n).pieceInterior ⊤,
      ENNReal.ofReal 20 < distanceToBoundary (W n) (g n) x →
        ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) x := fun x hx =>
    lt_trans ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 20)).mpr
      (by norm_num : (5 : ℝ) < 20)) hx
  -- the family of the regionalised kernel on `(W°, ĝ)`
  refine (hbind (max L₀ Lmax) (le_max_left _ _) (le_max_right _ _) (W n) (g n) (ĝ n)
    (hcomp n) (heq4 n) (hle n) (ρ n) hρpos hsm hlip (fun p => (hlc p).1) (n : ℝ)
    (by linarith only [h8]) (by linarith only [h2300]) h16
    (fun p => ⟨(hdata p).1, (hdata p).2.1, (hdata p).2.2.1, (hdata p).2.2.2.1⟩)).elim
    fun hcN e1 => ?_
  refine e1.elim fun L e2 => ?_
  refine e2.1.elim fun hAd => ?_
  refine e2.2.2.2.2.elim fun edgeB e3 => ?_
  -- the zero family for THIS scale
  refine (hzn (ρ n) hρpos hsm.continuous (fun p => (hlc' p).2) hcn').elim fun N y1 => ?_
  refine y1.elim fun C y2 => ?_
  refine y2.elim fun mN y3 => ?_
  refine y3.elim fun cN y4 => ?_
  refine y4.elim fun mC y5 => ?_
  refine y5.elim fun o y6 => ?_
  refine y6.elim fun Fz y7 => ?_
  let instM_BDRY5 : MetricSpace ((W n).pieceInterior ⊤) := inducedMetricSpace (ĝ n)
  refine ⟨ρ n, hρpos, hsm, hlip, hlc', hcn', hbcp, connectedSpace_pieceInterior_top_BDRY1 (W n),
    ĝ n, O n, hO n, hKO n, heqO n, hle n, hcN,
    { toLocalPacketsOnBF :=
        { toLocalPacketsOnB :=
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
              slim_value := e2.2.2.1
              edgeB := edgeB
              edgeB_coarse := e3.1
              edgeB_domain := e3.2.2.2.1
              exhaustionB := e3.2.2.2.2 }
          circle_residual := e2.2.1
          edgeDiskB := e3.2.1
          edgeB_section := e3.2.2.1
          zero_local_comparison := y7.2.1
          zero_shell_split := y7.2.2.2.1
          zero_adapted := y7.2.2.2.2.1
          zero_curvature := y7.2.2.1 }
      rank_le_two := e2.2.2.2.1 }, ?_, ?_, y7.1, ?_, ?_, y7.2.2.2.2.2.1, y7.2.2.2.2.2.2.1,
    y7.2.2.2.2.2.2.2.1, y7.2.2.2.2.2.2.2.2⟩
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
