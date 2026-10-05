import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCollapsePacket

/-!
# LC88, cusp side: requested precision BEFORE the physical cusp height (lane BCUSP-1, G1)

External review 51, P0-C(ii) (`docs/geometrization/chapter14/out/dispositions-task51-boundary-family-enrichment.md`):
a FIXED export tolerance `εB ≤ β₁²/1000` does not give `εB ≤ β∂²/1000` for a cusp splitting quality
`β∂ < β₁`, and it does not shrink with `n`. Decision: route 1 — every cusp precision request is
registered FIRST, then the actual height is chosen.

Route 1 is available with the tree's producers: T3 (`lc88_boundary_collapse_packet_BDRY1`) quantifies
the tolerance `εB` after `β` and `ζ` and before `εr, δ', Λ', T, e, Lmax, δ₀`, the sequence, `V` and the
tail, and the export packet (hence the height `P.height`) is produced inside the tail at tolerance
`εB`. All cusp precision thresholds of blueprint BR24 (`B:10458–10470`) are functions of parameters
fixed before that slot. Here the slot takes the REQUESTS `β∂` (cusp splitting quality) and `εN`
(norm/Hessian tolerance), and the tolerance is DETERMINED by them:
`εB = cuspTolerance_BCUSP1 β₁ β∂ εN = min (1/1000) (β₁²/1000) (β∂²/1000) εN`.

The late physical parameters (the buffer `L`, later `H∂, r∂`) constrain only the scale `ρ`, never the
height: on the returned `P` and `ρ` the conclusion carries the per-`n` certificate
`1000 δ_n² < w' min(1/2, r/4)² ⟹ ρ < r on z ≤ 96` (`NearlyCuspidalBoundary.lt_of_le_two_mul_firstVolumeScale`),
which one arithmetic tail (`eventually_thousand_mul_boundaryCounterexampleRatio_sq_lt`) makes true for
any later `r`. The SAME `P` and `ρ` serve every late parameter; nothing is re-chosen.

* `cuspTolerance_BCUSP1` and its bounds;
* `exists_boundaryExportPacket_req_BCUSP1`: the per-carrier height producer at the requested tolerance;
* `lc88_boundary_collapse_packet_req_BCUSP1`: T3 with the requests at the tolerance slot; on the tail
  also `δ_n ≤ β∂²/1000` and the late `ρ` certificate;
* consumer `lc88_cusp_adapted_req_BCUSP1`: `BoundaryExportPacket.adapted` at quality `β∂` (any `γ∂`,
  any late buffer `L`) on the height of the returned packet.
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

section Tolerance

/-- **The requested cusp tolerance.** The export tolerance determined by the requests: the
no-zero quality `β₁`, the cusp splitting quality `β∂` and the norm/Hessian tolerance `εN`. -/
def cuspTolerance_BCUSP1 (β₁ βd εN : ℝ) : ℝ :=
  min (1 / 1000) (min (β₁ ^ 2 / 1000) (min (βd ^ 2 / 1000) εN))

theorem cuspTolerance_pos_BCUSP1 {β₁ βd εN : ℝ} (h1 : 0 < β₁) (hd : 0 < βd) (hN : 0 < εN) :
    0 < cuspTolerance_BCUSP1 β₁ βd εN :=
  lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) hN))

theorem cuspTolerance_le_thousandth_BCUSP1 (β₁ βd εN : ℝ) :
    cuspTolerance_BCUSP1 β₁ βd εN ≤ 1 / 1000 :=
  min_le_left _ _

theorem cuspTolerance_le_beta_BCUSP1 (β₁ βd εN : ℝ) :
    cuspTolerance_BCUSP1 β₁ βd εN ≤ β₁ ^ 2 / 1000 :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem cuspTolerance_le_request_BCUSP1 (β₁ βd εN : ℝ) :
    cuspTolerance_BCUSP1 β₁ βd εN ≤ βd ^ 2 / 1000 :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

theorem cuspTolerance_le_norm_BCUSP1 (β₁ βd εN : ℝ) :
    cuspTolerance_BCUSP1 β₁ βd εN ≤ εN :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

end Tolerance

section Carrier

variable {W : CompactCarrier.{u}} [ConnectedSpace W.Carrier]
  {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A : ℝ → ℝ} {w₀ : ℝ}

/-- **The height producer at the requested tolerance.** The requests `β₁, β∂, εN > 0` are given
first; the export packet with the supplied labels and its height are produced at the tolerance
they determine. -/
theorem exists_boundaryExportPacket_req_BCUSP1 (B : NearlyCuspidalBoundary W g K w₀)
    (hv : boundaryVolumeCollapsed W g w₀) (hd : curvatureDerivativesControlled g K A w₀)
    (hK : 2 ≤ K) (hw : w₀ ≤ 1 / 6408) {β₁ βd εN : ℝ} (h1 : 0 < β₁) (hβd : 0 < βd)
    (hN : 0 < εN) :
    ∃ P : BoundaryExportPacket W g K A w₀ (cuspTolerance_BCUSP1 β₁ βd εN), P.cusp = B :=
  exists_boundaryExportPacket_cusp_eq_BDRY3 B hv hd hK hw (cuspTolerance_pos_BCUSP1 h1 hβd hN)
    (cuspTolerance_le_thousandth_BCUSP1 β₁ βd εN)

end Carrier

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **T3 with the cusp requests registered before the height.** T3's prefix, with the tolerance
slot replaced by the requests `β∂, εN`; the export packet `P` is produced at the tolerance
`cuspTolerance_BCUSP1 β₁ β∂ εN` they determine. On the same tail as T3's data: `δ_n ≤ β∂²/1000` and,
for the same `ρ`, the late certificate `1000 δ_n² < w' min(1/2, r/4)² ⟹ ρ < r` on every collar
`z ≤ 96` (every `r > 0`). -/
theorem lc88_boundary_collapse_packet_req_BCUSP1
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
      ∀ βd εN : ℝ, 0 < βd → 0 < εN →
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
        ∃ P : BoundaryExportPacket (W n) (g n) K A (boundaryCounterexampleRatio δ₀ n)
          (cuspTolerance_BCUSP1 (β 1) βd εN),
        P.cusp = B n ∧ boundaryCounterexampleRatio δ₀ n ≤ βd ^ 2 / 1000 ∧
        ∃ ρ : (W n).Carrier → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
          ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ ρ ∧
          (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
          (∀ p, firstVolumeScale (g n) p w / 2 < ρ p ∧
            ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
          (∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
            ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000) ∧
          (∀ r : ℝ, 0 < r →
            1000 * boundaryCounterexampleRatio δ₀ n ^ 2 <
              w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (r / 4) ^ 2 →
            ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
              ρ ((P.cusp.collar i).toFun q) < r) ∧
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
  obtain ⟨δS, hδS, a₂, ha₂, hT3⟩ := lc88_boundary_collapse_packet_BDRY1 hσs hσs1 K hK A hA
  refine ⟨δS, hδS, a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hT3⟩ := hT3 γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hT3⟩ := hT3 βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, hT3⟩ := hT3 β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 s b' s' i1 i2 i3 i4 i5
    i6 i7 i8 => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, hT3⟩ := hT3 σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 s b' s' i1 i2 i3
    i4 i5 i6 i7 i8
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 => ?_⟩
  obtain ⟨w₀, hw₀, hT3⟩ := hT3 σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5
  refine ⟨w₀, hw₀, fun w hw hww hwc b hb l1 l2 l3 l4 => ?_⟩
  obtain ⟨b₀, hb₀, hT3⟩ := hT3 w hw hww hwc b hb l1 l2 l3 l4
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβ11 hβ3 ζ hζ1 hζ2 βd εN hβd hεN => ?_⟩
  obtain ⟨εr, δ', Λ', hεr, hεr1, hδ', hΛ', hT3⟩ := hT3 β hβ2 hβ1 hβ1b hβ11 hβ3 ζ hζ1 hζ2
    (cuspTolerance_BCUSP1 (β 1) βd εN) (cuspTolerance_pos_BCUSP1 hβ1 hβd hεN)
    (cuspTolerance_le_thousandth_BCUSP1 _ _ _) (cuspTolerance_le_beta_BCUSP1 _ _ _)
  refine ⟨εr, δ', Λ', hεr, hεr1, hδ', hΛ', fun T hT hTΛ e he he1 Lmax hLmax δ₀ hδ₀ hδ₀S W _ g B
    hcoll hder => ?_⟩
  obtain ⟨V, hTV, δ, hδ, hδδ', hev⟩ := hT3 T hT hTΛ e he he1 Lmax hLmax δ₀ hδ₀ hδ₀S W g B hcoll
    hder
  refine ⟨V, hTV, δ, hδ, hδδ', ?_⟩
  have hβd2 : 0 < βd ^ 2 / 1000 := by positivity
  have hw' : 0 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := by positivity
  have hnR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hev, hnR.eventually_ge_atTop 7,
    hnR.eventually_ge_atTop (1 / (16 * (βd ^ 2 / 1000)))] with n hn hn7 hnβ
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith only [hn7])
  have hratio : boundaryCounterexampleRatio δ₀ n ≤ βd ^ 2 / 1000 :=
    boundaryCounterexampleRatio_le_of_BDRY5 δ₀ hβd2 hn1 (one_le_sixteen_mul_of_ge_BDRY5 hβd2 hnβ)
  have h100 : boundaryCounterexampleRatio δ₀ n ≤ 1 / 100 :=
    boundaryCounterexampleRatio_le_of_BDRY5 δ₀ (by norm_num) hn1 (by linarith only [hn7])
  obtain ⟨P, hP, ρ, hρpos, hsm, hlip, hlc, hcol, hrest⟩ := hn
  have hcert : ∀ r : ℝ, 0 < r →
      1000 * boundaryCounterexampleRatio δ₀ n ^ 2 <
        w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (r / 4) ^ 2 →
      ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
        ρ ((P.cusp.collar i).toFun q) < r := by
    rw [hP]
    intro r hr hcond i q hq
    exact (B n).lt_of_le_two_mul_firstVolumeScale h100 hw' hr hcond (fun p => (hlc p).2.le) i hq
  exact ⟨P, hP, hratio, ρ, hρpos, hsm, hlip, hlc, hcol, hcert, hrest⟩

/-- **Consumer: the BCP02 adapted coordinate at the requested quality on the returned height.** On
the tail of the requested T3, the SAME packet `P` (requested tolerance, `P.cusp = B n`) and the same
scale `ρ`: for every late buffer `L ≥ 0` and quality `β∂ < γ∂ < 1` for which `δ_n` passes the
arithmetic test, at every band point `e_i q₀` (`2 ≤ z ≤ 98`, `5 ≤ η_i ≤ 95`) the hypotheses of
`BoundaryExportPacket.adapted` hold at `β = β∂`, `r = ρ(e_i q₀)`, and it yields the actual rank-one
splitting and the bound `|U| < 1 + γ∂` for `U = (η_i − η_i(e_i q₀))/ρ(e_i q₀)`. The test holds on a
tail for every fixed `L` (second conclusion). -/
theorem lc88_cusp_adapted_req_BCUSP1
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
      ∀ βd εN : ℝ, 0 < βd → 0 < εN →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ Lmax : ℝ, 0 < Lmax →
      ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ n)) →
      ∃ V : ℝ, T ≤ V ∧ (∀ᶠ n in atTop,
        ∃ P : BoundaryExportPacket (W n) (g n) K A (boundaryCounterexampleRatio δ₀ n)
          (cuspTolerance_BCUSP1 (β 1) βd εN),
        P.cusp = B n ∧ ∃ ρ : (W n).Carrier → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
          ∀ L γd : ℝ, 0 ≤ L → βd < γd → γd < 1 →
            1000 * boundaryCounterexampleRatio δ₀ n ^ 2 <
              w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (βd ^ 3 / (2000 * (1 + L)) / 4) ^ 2 →
          ∀ (i : Fin P.cusp.count) (q₀ : CuspHalfSpace), 2 ≤ q₀.2.val 0 → q₀.2.val 0 ≤ 98 →
            5 ≤ P.height i ((P.cusp.collar i).toFun q₀) →
            P.height i ((P.cusp.collar i).toFun q₀) ≤ 95 →
            @HasEuclideanSplitting.{0, 0} (W n).Carrier
              ((inducedMetricSpace (g n)).rescale (ρ ((P.cusp.collar i).toFun q₀))⁻¹
                (inv_pos.mpr (hρpos _))) ((P.cusp.collar i).toFun q₀) 1 βd ∧
            ∀ x : (W n).Carrier,
              (ρ ((P.cusp.collar i).toFun q₀))⁻¹ *
                  (riemannianEDistOf (g n) x ((P.cusp.collar i).toFun q₀)).toReal < 1 →
                |(P.height i x - P.height i ((P.cusp.collar i).toFun q₀)) /
                  ρ ((P.cusp.collar i).toFun q₀)| < 1 + γd) ∧
        ∀ L : ℝ, 0 ≤ L → ∀ᶠ n in atTop, 1000 * boundaryCounterexampleRatio δ₀ n ^ 2 <
          w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (βd ^ 3 / (2000 * (1 + L)) / 4) ^ 2 := by
  obtain ⟨δS, hδS, a₂, ha₂, hR⟩ := lc88_boundary_collapse_packet_req_BCUSP1 hσs hσs1 K hK A hA
  refine ⟨δS, hδS, a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hR⟩ := hR γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hR⟩ := hR βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, hR⟩ := hR β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 s b' s' i1 i2 i3 i4 i5
    i6 i7 i8 => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, hR⟩ := hR σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 s b' s' i1 i2 i3
    i4 i5 i6 i7 i8
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 => ?_⟩
  obtain ⟨w₀, hw₀, hR⟩ := hR σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5
  refine ⟨w₀, hw₀, fun w hw hww hwc b hb l1 l2 l3 l4 => ?_⟩
  obtain ⟨b₀, hb₀, hR⟩ := hR w hw hww hwc b hb l1 l2 l3 l4
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβ11 hβ3 ζ hζ1 hζ2 βd εN hβd hεN => ?_⟩
  obtain ⟨εr, δ', Λ', hεr, hεr1, hδ', hΛ', hR⟩ := hR β hβ2 hβ1 hβ1b hβ11 hβ3 ζ hζ1 hζ2 βd εN hβd
    hεN
  refine ⟨εr, δ', Λ', hεr, hεr1, hδ', hΛ', fun T hT hTΛ e he he1 Lmax hLmax δ₀ hδ₀ hδ₀S W _ g B
    hcoll hder => ?_⟩
  obtain ⟨V, hTV, δ1, -, -, hev⟩ := hR T hT hTΛ e he he1 Lmax hLmax δ₀ hδ₀ hδ₀S W g B hcoll hder
  have hw' : 0 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := by positivity
  have hrL : ∀ L : ℝ, 0 ≤ L → 0 < βd ^ 3 / (2000 * (1 + L)) := fun L hL =>
    div_pos (pow_pos hβd 3) (by linarith)
  refine ⟨V, hTV, ?_, fun L hL =>
    eventually_thousand_mul_boundaryCounterexampleRatio_sq_lt hδ₀
      (mul_pos hw' (pow_pos (lt_min (by norm_num) (div_pos (hrL L hL) (by norm_num))) 2))⟩
  filter_upwards [hev] with n hn
  obtain ⟨P, hP, hratio, ρ, hρpos, -, -, -, -, hcert, -⟩ := hn
  refine ⟨P, hP, ρ, hρpos, fun L γd hL hβγ hγ1 hcond i q₀ hz2 hz98 h5 h95 => ?_⟩
  have hq₀ : q₀ ∈ cuspDomain := cusp_mem_cuspDomain_of_le (by norm_num [cuspDepth]) hz98
  have hz96 : q₀.2.val 0 ≤ 96 := by
    have h := abs_lt.mp (P.height_contract i q₀ hq₀ hz2 hz98).1
    have h1000 := cuspTolerance_le_thousandth_BCUSP1 (β 1) βd εN
    linarith
  have hρL : ρ ((P.cusp.collar i).toFun q₀) ≤ βd ^ 3 / (2000 * (1 + L)) :=
    (hcert _ (hrL L hL) hcond i q₀ hz96).le
  obtain ⟨hsplit, -, -, -, -, hbound⟩ := P.adapted i βd γd L (ρ ((P.cusp.collar i).toFun q₀)) q₀
    (hρpos _) hβd hβγ hγ1 hL hratio (cuspTolerance_le_request_BCUSP1 _ _ _) hρL hz2 hz98 h5 h95
  exact ⟨hsplit, hbound⟩

end DifferentialGeometry.Geometry.Collapse
