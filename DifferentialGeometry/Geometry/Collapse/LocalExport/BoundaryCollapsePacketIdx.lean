import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCollapsePacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLocalPacketsProducerIdx

/-!
# LC88: the boundary collapse packet T3 on the index-shifted boundary sequence (lane BDRY-IDX)

The accepted T3 `lc88_boundary_collapse_packet_BDRY1` takes the boundary sequence at `δ_n` for ALL
`n` and is vacuous (`δ_0 = 0`, no nearly cuspidal data at ratio `0`; lane FC39-BQ).
`lc88_boundary_collapse_packet_BDRY1_IDX` is T3 with the sequence at `δ_{n+1}` (BBR03's sequence)
and the export packet `P : BoundaryExportPacket … (δ_{n+1}) εB` of the member; proof = T3's, on
T2 `eventually_nonempty_boundaryLocalPackets_BDRY1_IDX`, with `δ_{n+1} ≤ δ_n`
(`boundaryCounterexampleRatio_succ_le_IDX`) for the ratio bounds and `δ_{n+1}·16n⁴ ≤ 1` for the
per-member BSA04 / BCP04.a kernels at the real parameter `n`.
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

/-- **T3 (frozen v2), the LC88 row, index-shifted (lane BDRY-IDX).** The accepted T3 with the
boundary sequence at `δ_{n+1}` (BBR03's sequence) and the export packet at the member's ratio
`δ_{n+1}`; everything else verbatim. T2's prefix with the export tolerance `εB` after `β₁`. On one
tail: the export packet `P` with the supplied labels (`P.cusp = B n`), the data of T2, and the
labelled product alternative OR (enlarged collars pairwise disjoint, retained pieces disjoint at
distance `≥ 1`, and every ACTUAL zero ball `B_g(z, R_z)` of `F` disjoint from every FULL enlarged
collar `B_i⁺ = e_i{z < 92}`, with the block-support disjointness as a corollary). -/
theorem lc88_boundary_collapse_packet_BDRY1_IDX
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
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
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
  obtain ⟨δ2, hδ2, a₂, ha₂, hT2⟩ :=
    eventually_nonempty_boundaryLocalPackets_BDRY1_IDX hσs hσs1 K hK A hA
  obtain ⟨δP, hδP, hpair⟩ := bsa06_pair_BDRY2.{0}
  obtain ⟨δC, hδC, hcurv⟩ := bsa04_row.{0}
  refine ⟨min δ2 (min δP δC), lt_min hδ2 (lt_min hδP hδC), a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hT2⟩ := hT2 γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hT2⟩ := hT2 βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, hT2⟩ := hT2 β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 s b' s' i1 i2 i3 i4 i5
    i6 i7 i8 => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, hT2⟩ := hT2 σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 s b' s' i1 i2 i3
    i4 i5 i6 i7 i8
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 => ?_⟩
  obtain ⟨w₀, hw₀, hT2⟩ := hT2 σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5
  refine ⟨w₀, hw₀, fun w hw hww hwc b hb l1 l2 l3 l4 => ?_⟩
  obtain ⟨b₀, hb₀, hT2⟩ := hT2 w hw hww hwc b hb l1 l2 l3 l4
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβ11 hβ3 ζ hζ1 hζ2 εB hεB hεB1 hεBβ => ?_⟩
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
  have hδβ : boundaryCounterexampleRatio δ₀ (n + 1) ≤ β 1 ^ 2 / 1000 :=
    (boundaryCounterexampleRatio_succ_le_IDX δ₀ hn1).trans
      (boundaryCounterexampleRatio_le_of_BDRY5 δ₀ hβsq hn1 (one_le_sixteen_mul_of_ge_BDRY5 hβsq
          hnβ))
  have hδ6408 : boundaryCounterexampleRatio δ₀ (n + 1) ≤ 1 / 6408 :=
    (boundaryCounterexampleRatio_succ_le_IDX δ₀ hn1).trans
      (boundaryCounterexampleRatio_le_of_BDRY5 δ₀ (by norm_num) hn1 (by linarith only [hn6408]))
  have h300 : 300 * V < n := by linarith only [hn300]
  have hratio0 : 0 ≤ boundaryCounterexampleRatio δ₀ (n + 1) :=
    (boundaryCounterexampleRatio_pos hδ₀ (Nat.le_add_left 1 n)).le
  have hnw' : (n : ℝ)⁻¹ ≤ w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := (inv_le_comm₀ hn0 hw').mpr hnw
  obtain ⟨ρ, hρpos, hsm, hlip, hlc, hcol, hconn, ĝ, O, hO, hKO, heqO, hle, hcN, F, hrank, -,
    hzball, -⟩ := hn
  obtain ⟨P, hP⟩ := exists_boundaryExportPacket_cusp_eq_BDRY3 (B n) (hcoll n) (hder n)
    hK2 hδ6408 hεB hεB1 (A := A)
  -- BCP04.a and the curvature scale at every point (the original scale `ρ < 2 r(w')`)
  have hbcp : ∀ p : (W n).Carrier, 0 < distanceToBoundary (W n) (g n) p →
      (n : ℝ) * (distanceToBoundary (W n) (g n) p).toReal /
          ((distanceToBoundary (W n) (g n) p).toReal + 3) <
        (distanceToBoundary (W n) (g n) p).toReal / ρ p := fun p hp =>
    (hpair (W n) (g n) K _ hK2 hratio0
      ((boundaryCounterexampleRatio_le δ₀ (n + 1)).trans
        (hδ₀S.trans ((min_le_right _ _).trans (min_le_left _ _)))) (B n)
      (hcoll n) (hder n) hA hn3 (boundaryCounterexampleRatio_succ_mul_le_IDX δ₀ n) hnw' hw'c p
          (hρpos p)
      (hlc p).2.le).2.2.2 hp
  have hscale : ∀ p : (W n).Carrier,
      ENNReal.ofReal ((n : ℝ) * ρ p) < curvatureRadius (g n) p := by
    intro p
    have hst := (hcurv (W n) (g n) K _ hK2 hratio0
      ((boundaryCounterexampleRatio_le δ₀ (n + 1)).trans
        (hδ₀S.trans ((min_le_right _ _).trans (min_le_right _ _)))) (B n) (hcoll n) (hder n)
      hn3 (boundaryCounterexampleRatio_succ_mul_le_IDX δ₀ n) p).1
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
  let instM_BDRY5 : MetricSpace ((W n).pieceInterior ⊤) := inducedMetricSpace ĝ
  let _ := F.instMetricN
  let _ := F.instChartedN
  let _ := F.instMetricC
  -- every actual zero ball misses every full enlarged collar
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
  refine ⟨P, hP, ρ, hρpos, hsm, hlip, hlc, hcolP, hconn, ĝ, O, hO, hKO, heqO, hle, hcN, F, hrank,
    hzball, ?_⟩
  rcases P.alternative with hprod | hdisj
  · exact Or.inl hprod
  · refine Or.inr ⟨hdisj, hsep, ?_⟩
    apply Set.disjoint_left.mpr
    intro x hx hb
    obtain ⟨z, hx⟩ := mem_iUnion.mp hx
    obtain ⟨hz, hx⟩ := mem_iUnion.mp hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hb
    obtain ⟨q, hq, hqx⟩ := P.toBoundaryCollarPacket.tsupport_block_subset i hi
    have hq92 : q.2.val 0 < 92 := by
      have hh : q.2.val 0 ≤ 90 + εB := hq.2
      linarith only [hh, hεB1]
    exact Set.disjoint_left.mp (hsep z hz i) hx ⟨q, hq92, hqx⟩

end DifferentialGeometry.Geometry.Collapse
