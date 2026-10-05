import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspRequest
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarSplittingBCP02KLProduct

/-!
# B3 on the packet returned by the requested T3 (lane BCUSP-1, G2 consumer)

`lc88_cusp_splitting_req_BCUSP1`: on the tail of `lc88_boundary_collapse_packet_req_BCUSP1` (cusp
requests `β∂, εN` registered before the height), the SAME packet `P` and scale `ρ` serve every late
buffer `L` and adapted quality `γ∂ ∈ (β∂, 1)` passing the arithmetic test: at every band point
`e_i q₀`, with `r = ρ(e_i q₀)`, the actual Kleiner–Lott `β∂`-splitting of `(W_n, r⁻¹ d_g, e_i q₀)`
to `ℝ ×₂` the frozen flat torus has real coordinate EXACTLY `U = (η_i − η_i(e_i q₀))/r` everywhere
and the actual torus coordinate on the test ball (`BoundaryExportPacket.cusp_splitting_BCUSP1`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **Consumer: B3 on the returned height.** -/
theorem lc88_cusp_splitting_req_BCUSP1
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
      ∃ V : ℝ, T ≤ V ∧ ∀ᶠ n in atTop,
        ∃ P : BoundaryExportPacket (W n) (g n) K A (boundaryCounterexampleRatio δ₀ n)
          (cuspTolerance_BCUSP1 (β 1) βd εN),
        P.cusp = B n ∧ ∃ ρ : (W n).Carrier → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
          ∀ L γd : ℝ, 0 ≤ L → βd < γd → γd < 1 →
            1000 * boundaryCounterexampleRatio δ₀ n ^ 2 <
              w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (βd ^ 3 / (2000 * (1 + L)) / 4) ^ 2 →
          ∀ (i : Fin P.cusp.count) (q₀ : CuspHalfSpace), 2 ≤ q₀.2.val 0 → q₀.2.val 0 ≤ 98 →
            5 ≤ P.height i ((P.cusp.collar i).toFun q₀) →
            P.height i ((P.cusp.collar i).toFun q₀) ≤ 95 →
            letI := (inducedMetricSpace (g n)).rescale (ρ ((P.cusp.collar i).toFun q₀))⁻¹
              (inv_pos.mpr (hρpos _))
            letI := (inducedMetricSpace (P.cusp.collar i).cusp.torusMetric).rescale
              ((ρ ((P.cusp.collar i).toFun q₀))⁻¹ * Real.exp (-(q₀.2.val 0) / 2))
              (mul_pos (inv_pos.mpr (hρpos _)) (Real.exp_pos _))
            ∃ t₀ : Torus, t₀ = q₀.1 ∧ ∃ f : KleinerLottApprox ((P.cusp.collar i).toFun q₀)
                (WithLp.toLp 2 ((0 : ℝ), t₀)) βd,
              (∀ x, (f.toFun x).fst = (P.height i x - P.height i ((P.cusp.collar i).toFun q₀)) /
                ρ ((P.cusp.collar i).toFun q₀)) ∧
              ∀ x, (ρ ((P.cusp.collar i).toFun q₀))⁻¹ *
                  (riemannianEDistOf (g n) x ((P.cusp.collar i).toFun q₀)).toReal ≤ βd⁻¹ + βd →
                (f.toFun x).snd = (invFunOn (P.cusp.collar i).toFun cuspDomain x).1 := by
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
  have hrL : ∀ L : ℝ, 0 ≤ L → 0 < βd ^ 3 / (2000 * (1 + L)) := fun L hL =>
    div_pos (pow_pos hβd 3) (by linarith)
  refine ⟨V, hTV, ?_⟩
  filter_upwards [hev] with n hn
  obtain ⟨P, hP, hratio, ρ, hρpos, -, -, -, -, hcert, -⟩ := hn
  refine ⟨P, hP, ρ, hρpos, fun L γd hL hβγ hγ1 hcond i q₀ hz2 hz98 h5 h95 => ?_⟩
  have hq₀ : q₀ ∈ cuspDomain := cusp_mem_cuspDomain_of_le (by norm_num [cuspDepth]) hz98
  have h1000 := cuspTolerance_le_thousandth_BCUSP1 (β 1) βd εN
  have hz96 : q₀.2.val 0 ≤ 96 := by
    have h := abs_lt.mp (P.height_contract i q₀ hq₀ hz2 hz98).1
    linarith
  have hρL : ρ ((P.cusp.collar i).toFun q₀) ≤ βd ^ 3 / (2000 * (1 + L)) :=
    (hcert _ (hrL L hL) hcond i q₀ hz96).le
  exact (P.cusp_splitting_BCUSP1 (le_trans (by norm_num) hK) h1000 i βd γd L
    (ρ ((P.cusp.collar i).toFun q₀)) q₀ (hρpos _) hβd hβγ hγ1 hL hratio
    (cuspTolerance_le_request_BCUSP1 _ _ _) hρL hz2 hz98 h5 h95).1

end DifferentialGeometry.Geometry.Collapse
