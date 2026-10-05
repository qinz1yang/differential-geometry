import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspRequest
import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.SupportListsCollar

/-!
# B5: the late physical cusp scale `r∂` and `ε∂ = 20 c₃ r∂` (lane BCUSP-1, G4)

Review 51, item B5 (`B5 H∂, r∂, ε∂ order`); blueprint BR24 (`B:10458–10483`): after the cusp qualities,
"Let `H∂` be a finite common upper bound for all the resulting cusp test radii and their first-exit
buffers. … Choose `r∂ > 0` below those product/first-exit bounds and, explicitly, below
`min{1/(1000L), 1/10⁴, 1/(100H∂), ϑ²/(4·10⁸(12L+1000)), 10⁻⁶/(20(c₃+1))}` (BRegPhysical). … This gives
BCG02's Hessian integral bound, BCG01's complete support-domain buffer, BCG05's exact-marker
localization and `20c₃r∂ < 10⁻⁶`. The parameter is chosen AFTER the finite `V`"; BR25: one uniform tail.

The order is a LATE-PARAMETER + COMMON-TAIL certificate, not a family field:
* `cuspPhysicalScale_BCUSP1 β∂ L H ϑ c₃` = half the minimum of BRegPhysical and the BCP02 product bound
  `β∂³/(2000(1 + H))` at buffer `H = H∂`; it is a function of earlier parameters only (`H` after `β∂`,
  `r∂` after `H`), with its bounds `cuspPhysicalScale_pos/_mul_L/_lt_tenthousandth/_mul_H/_taylor/
  _eps/_le_bcp02_BCUSP1` (`ε∂ = 20c₃r∂ < 10⁻⁶`);
* consumer `lc88_cusp_physical_req_BCUSP1`: on the tail of the requested T3, the SAME packet `P` and
  scale `ρ` serve every late `(L, H∂, ϑ, c₃)`: if `δ_n` passes the arithmetic test at `r∂`, then on every
  collar `z ≤ 96`: `ρ < r∂`, BCP02's product bound at buffer `H∂`, `ρ H∂ < 1/100`, BCG02's Hessian
  integral bound `2ρ(12L + 1000) < ϑ²/10⁸`, `20c₃ρ < 10⁻⁶`; and BCG01.b for every reference domain
  `B(p, Cρ(p))` (`C ≤ .95L`, `ΛC ≤ 1/2`) meeting a closed boundary support: `ρ(p) < 2r∂`, the domain in
  the band `19 < z, η_b < 91`. The test holds on ONE tail for every fixed late tuple.
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

section Scale

/-- **The late physical cusp scale `r∂`** (BRegPhysical with the BCP02 product bound at buffer `H`):
half of `min {1/(1000L), 1/10⁴, 1/(100H), ϑ²/(4·10⁸(12L+1000)), 10⁻⁶/(20(c₃+1)), β∂³/(2000(1+H))}`. -/
def cuspPhysicalScale_BCUSP1 (βd L H ϑ c₃ : ℝ) : ℝ :=
  min (1 / (1000 * L)) (min (1 / 10000) (min (1 / (100 * H))
    (min (ϑ ^ 2 / (4 * 10 ^ 8 * (12 * L + 1000))) (min (1 / 1000000 / (20 * (c₃ + 1)))
      (βd ^ 3 / (2000 * (1 + H))))))) / 2

variable {βd L H ϑ c₃ : ℝ}

theorem cuspPhysicalScale_pos_BCUSP1 (hβd : 0 < βd) (hL : 0 < L) (hH : 0 < H) (hϑ : 0 < ϑ)
    (hc₃ : 0 ≤ c₃) : 0 < cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ := by
  unfold cuspPhysicalScale_BCUSP1
  have h1 : 0 < 1 / (1000 * L) := by positivity
  have h3 : 0 < 1 / (100 * H) := by positivity
  have h4 : 0 < ϑ ^ 2 / (4 * 10 ^ 8 * (12 * L + 1000)) := by positivity
  have h5 : 0 < 1 / 1000000 / (20 * (c₃ + 1)) := by positivity
  have h6 : 0 < βd ^ 3 / (2000 * (1 + H)) := by positivity
  have h := lt_min h1 (lt_min (by norm_num : (0 : ℝ) < 1 / 10000) (lt_min h3 (lt_min h4
    (lt_min h5 h6))))
  linarith

/-- The six entries bound the doubled scale. -/
theorem two_mul_cuspPhysicalScale_le_BCUSP1 (βd L H ϑ c₃ : ℝ) :
    2 * cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ ≤ 1 / (1000 * L) ∧
    2 * cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ ≤ 1 / 10000 ∧
    2 * cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ ≤ 1 / (100 * H) ∧
    2 * cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ ≤ ϑ ^ 2 / (4 * 10 ^ 8 * (12 * L + 1000)) ∧
    2 * cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ ≤ 1 / 1000000 / (20 * (c₃ + 1)) ∧
    2 * cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ ≤ βd ^ 3 / (2000 * (1 + H)) := by
  unfold cuspPhysicalScale_BCUSP1
  rw [mul_div_cancel₀ _ (two_ne_zero)]
  exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))),
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))),
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))⟩

/-- BCG01's support-domain requirement `r∂ < 1/(1000L)`, in the form `r∂ (1000L) < 1`. -/
theorem cuspPhysicalScale_mul_L_BCUSP1 (hβd : 0 < βd) (hL : 0 < L) (hH : 0 < H) (hϑ : 0 < ϑ)
    (hc₃ : 0 ≤ c₃) : cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ * (1000 * L) < 1 := by
  have h0 := cuspPhysicalScale_pos_BCUSP1 hβd hL hH hϑ hc₃
  have h := (two_mul_cuspPhysicalScale_le_BCUSP1 βd L H ϑ c₃).1
  rw [le_div_iff₀ (by positivity)] at h
  nlinarith

/-- BCG05's requirement `r∂ < 10⁻⁴`. -/
theorem cuspPhysicalScale_lt_tenthousandth_BCUSP1 (hβd : 0 < βd) (hL : 0 < L) (hH : 0 < H)
    (hϑ : 0 < ϑ) (hc₃ : 0 ≤ c₃) : cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ < 1 / 10000 := by
  have h0 := cuspPhysicalScale_pos_BCUSP1 hβd hL hH hϑ hc₃
  have h := (two_mul_cuspPhysicalScale_le_BCUSP1 βd L H ϑ c₃).2.1
  linarith

/-- The first-exit buffer `r∂ < 1/(100 H∂)`, in the form `r∂ (100 H∂) < 1`. -/
theorem cuspPhysicalScale_mul_H_BCUSP1 (hβd : 0 < βd) (hL : 0 < L) (hH : 0 < H) (hϑ : 0 < ϑ)
    (hc₃ : 0 ≤ c₃) : cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ * (100 * H) < 1 := by
  have h0 := cuspPhysicalScale_pos_BCUSP1 hβd hL hH hϑ hc₃
  have h := (two_mul_cuspPhysicalScale_le_BCUSP1 βd L H ϑ c₃).2.2.1
  rw [le_div_iff₀ (by positivity)] at h
  nlinarith

/-- BCG02's Hessian integral bound `2 r∂ (12L + 1000) < ϑ²/10⁸`. -/
theorem cuspPhysicalScale_taylor_BCUSP1 (hβd : 0 < βd) (hL : 0 < L) (hH : 0 < H) (hϑ : 0 < ϑ)
    (hc₃ : 0 ≤ c₃) :
    2 * cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ * (12 * L + 1000) < ϑ ^ 2 / 10 ^ 8 := by
  have h0 := cuspPhysicalScale_pos_BCUSP1 hβd hL hH hϑ hc₃
  have h := (two_mul_cuspPhysicalScale_le_BCUSP1 βd L H ϑ c₃).2.2.2.1
  have hA : 0 < 12 * L + 1000 := by linarith
  rw [le_div_iff₀ (by positivity)] at h
  have hϑ2 : 0 < ϑ ^ 2 := by positivity
  rw [lt_div_iff₀ (by norm_num)]
  nlinarith

/-- **`ε∂ = 20 c₃ r∂ < 10⁻⁶`** (the actual torus core). -/
theorem cuspPhysicalScale_eps_BCUSP1 (hβd : 0 < βd) (hL : 0 < L) (hH : 0 < H) (hϑ : 0 < ϑ)
    (hc₃ : 0 ≤ c₃) : 20 * c₃ * cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ < 1 / 1000000 := by
  have h0 := cuspPhysicalScale_pos_BCUSP1 hβd hL hH hϑ hc₃
  have h := (two_mul_cuspPhysicalScale_le_BCUSP1 βd L H ϑ c₃).2.2.2.2.1
  rw [le_div_iff₀ (by positivity)] at h
  nlinarith

/-- BCP02's product bound at buffer `H∂`: `r∂ ≤ β∂³/(2000(1 + H∂))`. -/
theorem cuspPhysicalScale_le_bcp02_BCUSP1 (hβd : 0 < βd) (hL : 0 < L) (hH : 0 < H)
    (hϑ : 0 < ϑ) (hc₃ : 0 ≤ c₃) :
    cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ ≤ βd ^ 3 / (2000 * (1 + H)) := by
  have h0 := cuspPhysicalScale_pos_BCUSP1 hβd hL hH hϑ hc₃
  have h := (two_mul_cuspPhysicalScale_le_BCUSP1 βd L H ϑ c₃).2.2.2.2.2
  linarith

end Scale

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **Consumer: the late physical scale on the returned packet (B5).** -/
theorem lc88_cusp_physical_req_BCUSP1
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
        P.cusp = B n ∧ ∃ ρ : (W n).Carrier → ℝ, (∀ p, 0 < ρ p) ∧
          ∀ L H ϑ c₃ : ℝ, 0 < L → 0 < H → 0 < ϑ → 0 ≤ c₃ →
            1000 * boundaryCounterexampleRatio δ₀ n ^ 2 <
              w / (2 * (1 + 2 * Λ⁻¹) ^ 3) *
                min (1 / 2) (cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ / 4) ^ 2 →
            (∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
              ρ ((P.cusp.collar i).toFun q) < cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ ∧
              ρ ((P.cusp.collar i).toFun q) ≤ βd ^ 3 / (2000 * (1 + H)) ∧
              ρ ((P.cusp.collar i).toFun q) * H < 1 / 100 ∧
              2 * ρ ((P.cusp.collar i).toFun q) * (12 * L + 1000) < ϑ ^ 2 / 10 ^ 8 ∧
              20 * c₃ * ρ ((P.cusp.collar i).toFun q) < 1 / 1000000) ∧
            ∀ (C : ℝ) (p : (W n).Carrier) (b : Fin P.cusp.count), C ≤ 95 / 100 * L →
              Λ * C ≤ 1 / 2 →
              (∃ x ∈ tsupport (P.toBoundaryCollarPacket.block b),
                riemannianEDistOf (g n) p x < ENNReal.ofReal (C * ρ p)) →
              ρ p < 2 * cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ ∧
              ∀ y, riemannianEDistOf (g n) p y < ENNReal.ofReal (C * ρ p) →
                ∃ q ∈ cuspDomain, (P.cusp.collar b).toFun q = y ∧ 19 < q.2.val 0 ∧
                  q.2.val 0 < 91 ∧ 19 < P.height b y ∧ P.height b y < 91) ∧
        ∀ L H ϑ c₃ : ℝ, 0 < L → 0 < H → 0 < ϑ → 0 ≤ c₃ → ∀ᶠ n in atTop,
          1000 * boundaryCounterexampleRatio δ₀ n ^ 2 <
            w / (2 * (1 + 2 * Λ⁻¹) ^ 3) *
              min (1 / 2) (cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ / 4) ^ 2 := by
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
  refine ⟨V, hTV, ?_, fun L H ϑ c₃ hL hH hϑ hc₃ =>
    eventually_thousand_mul_boundaryCounterexampleRatio_sq_lt hδ₀
      (mul_pos hw' (pow_pos (lt_min (by norm_num)
        (div_pos (cuspPhysicalScale_pos_BCUSP1 hβd hL hH hϑ hc₃) (by norm_num))) 2))⟩
  filter_upwards [hev] with n hn
  obtain ⟨P, hP, -, ρ, hρpos, -, hlip, -, -, hcert, -⟩ := hn
  have h1000 := cuspTolerance_le_thousandth_BCUSP1 (β 1) βd εN
  refine ⟨P, hP, ρ, hρpos, fun L H ϑ c₃ hL hH hϑ hc₃ hcond => ?_⟩
  have hr0 := cuspPhysicalScale_pos_BCUSP1 hβd hL hH hϑ hc₃
  have hsmall := hcert _ hr0 hcond
  refine ⟨fun i q hq => ?_, fun C p b hC hΛC hmeet =>
    P.toBoundaryCollarPacket.bcg01_reference_domain (by linarith) hρpos hΛ.le hlip hsmall hL hC
      hΛC (cuspPhysicalScale_mul_L_BCUSP1 hβd hL hH hϑ hc₃) hmeet⟩
  have h := hsmall i q hq
  have hρ0 := hρpos ((P.cusp.collar i).toFun q)
  have hrH := cuspPhysicalScale_mul_H_BCUSP1 hβd hL hH hϑ hc₃
  have hrT := cuspPhysicalScale_taylor_BCUSP1 hβd hL hH hϑ hc₃
  have hrE := cuspPhysicalScale_eps_BCUSP1 hβd hL hH hϑ hc₃
  have hA : 0 < 12 * L + 1000 := by linarith
  have h1 : ρ ((P.cusp.collar i).toFun q) * H ≤ cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ * H :=
    mul_le_mul_of_nonneg_right h.le hH.le
  have h2 : 2 * ρ ((P.cusp.collar i).toFun q) * (12 * L + 1000) ≤
      2 * cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ * (12 * L + 1000) :=
    mul_le_mul_of_nonneg_right (by linarith only [h]) hA.le
  have h3 : 20 * c₃ * ρ ((P.cusp.collar i).toFun q) ≤
      20 * c₃ * cuspPhysicalScale_BCUSP1 βd L H ϑ c₃ :=
    mul_le_mul_of_nonneg_left h.le (by linarith only [hc₃])
  exact ⟨h, h.le.trans (cuspPhysicalScale_le_bcp02_BCUSP1 hβd hL hH hϑ hc₃),
    by linarith only [h1, hrH], by linarith only [h2, hrT], by linarith only [h3, hrE]⟩

end DifferentialGeometry.Geometry.Collapse
