import DifferentialGeometry.Geometry.Collapse.BoundaryPacketsOutBFRSeq
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRProducerT3Idx

/-!
# T3B-R's per-member conclusion on the index-shifted boundary sequence (lane BDRY-IDX4)

The accepted verbatim check `lc88_boundary_packets_BFR_out_BQ` (`BoundaryPacketsOutBFRSeq.lean`)
is T3B-R with its per-member conclusion written as `BoundaryPacketsOutBFR_BQ`; like T3B-R it takes
the boundary sequence at `δ_n` for ALL `n`, an EMPTY hypothesis (`δ_0 = 0`; lane FC39-BQ).
`lc88_boundary_packets_BFR_out_BQ_IDX4` is the same statement on sequences at `δ_{n+1}` (BBR03's
sequence), on lane BDRY-IDX2's `lc88_boundary_packets_BFR_BCG5_IDX2`: the cusp requests
`∀ βd εN` sit just before the eventual tail (after `V`, `δ`, `Lmax`, BBR01 BR24), the member's ratio
is `δ_{n+1}` and the BCP04.a index is the member's counterexample index `((n + 1 : ℕ) : ℝ)` — so the
per-member conclusion is literally the member clause of lane FC39-BQ's records
`PartialBoundaryFamilyOnSeqV2_BQ` / `PartialBoundaryFamilyAtSeqTied_BQ` (no adapter).

* `BoundaryPacketsOutBFR_BQ.mono_index_IDX4`: the per-member conclusion at one BCP04.a index gives
  it at another index for which BCP04.a holds at every positive scale `ρ < 2 r(w')`;
* `lc88_boundary_packets_BFR_out_BQ_IDX4`: T3B-R _IDX2 (index `n`, lane BDRY-IDX's convention)
  raised to the index `n + 1` by the per-member BSA06 pair kernel `bsa06_pair_BDRY2` at the real
  parameter `n + 1` (`δ_{n+1}·16(n+1)⁴ ≤ 1`, `(n+1)⁻¹ ≤ w'`).
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
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **Raising the BCP04.a index of T3B-R's per-member conclusion.** If BCP04.a holds at the index
`idx'` for EVERY positive scale `ρ < 2 r(w')` (in the producers it comes from the per-member BSA06
pair kernel `bsa06_pair_BDRY2`), then the per-member conclusion at `idx` gives the one at `idx'`
(only the BCP04.a clause changes; the same packet, scale, completion and packets). -/
theorem BoundaryPacketsOutBFR_BQ.mono_index_IDX4 {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A : ℝ → ℝ} {δn : ℝ}
    {B : NearlyCuspidalBoundary W g K δn} {idx idx' Λ w : ℝ} {β : ℕ → ℝ}
    {Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λ' βd εN : ℝ}
    (hup : ∀ ρ : W.Carrier → ℝ, (∀ p, 0 < ρ p) →
      (∀ p, ρ p < 2 * firstVolumeScale g p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
      ∀ p, 0 < distanceToBoundary W g p →
        idx' * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
          (distanceToBoundary W g p).toReal / ρ p)
    (h : BoundaryPacketsOutBFR_BQ W g K A δn B idx Λ w β Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ
      εr e T V vs ζ Λ' βd εN) :
    BoundaryPacketsOutBFR_BQ W g K A δn B idx' Λ w β Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λ' βd εN := by
  obtain ⟨P, hP, hδn, ρ, hρpos, hsm, hlip, hlc, hcol, h1, h2, h3, h4, h5, -, hrest⟩ := h
  exact ⟨P, hP, hδn, ρ, hρpos, hsm, hlip, hlc, hcol, h1, h2, h3, h4, h5,
    hup ρ hρpos (fun p => (hlc p).2), hrest⟩

/-- **Consumer (verbatim check), index-shifted (lane BDRY-IDX4)**: T3B-R on the sequence at
`δ_{n+1}` (BBR03's sequence; `lc88_boundary_packets_BFR_BCG5_IDX2`, cusp requests `βd εN` just
before the eventual tail) with its per-member conclusion written as `BoundaryPacketsOutBFR_BQ` at
the member's ratio `δ_{n+1}` and the member's counterexample index `idx = n + 1` — exactly the
member clause of lane FC39-BQ's `PartialBoundaryFamilyOnSeqV2_BQ`. BCP04.a at `n + 1` is re-derived
per member from `bsa06_pair_BDRY2` (`δ_{n+1}·16(n+1)⁴ ≤ 1`). -/
theorem lc88_boundary_packets_BFR_out_BQ_IDX4
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
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ Lmax : ℝ, 0 < Lmax →
      ∀ βd εN : ℝ, 0 < βd → 0 < εN → ∀ᶠ n in atTop,
        BoundaryPacketsOutBFR_BQ (W n) (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1)) (B n)
          ((n + 1 : ℕ) : ℝ) Λ w β Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λ'
          βd εN := by
  obtain ⟨δ3, hδ3, a₂, ha₂, hT3⟩ := lc88_boundary_packets_BFR_BCG5_IDX2 K hK A hA
  obtain ⟨δP, hδP, hpair⟩ := bsa06_pair_BDRY2.{0}
  refine ⟨min δ3 δP, lt_min hδ3 hδP, a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hT3⟩ := hT3 γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hT3⟩ := hT3 βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, hT3⟩ := hT3 β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 s b' s' i1 i2 i3
    i4 i5 i6 i7 i8 => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, hT3⟩ := hT3 σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 s b' s' i1
    i2 i3 i4 i5 i6 i7 i8
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 k6 => ?_⟩
  obtain ⟨w₀, hw₀, hT3⟩ := hT3 σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 k6
  refine ⟨w₀, hw₀, fun w hw hww hwc => ?_⟩
  obtain ⟨bd₀, hbd₀, hT3⟩ := hT3 w hw hww hwc
  refine ⟨bd₀, hbd₀, fun b hb l1 l2 l3 l4 l5 σs vs m1 m2 m3 => ?_⟩
  obtain ⟨b₀, hb₀, hT3⟩ := hT3 b hb l1 l2 l3 l4 l5 σs vs m1 m2 m3
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβ11 hβ3 ζ cap hζ1 hζ2 hcap => ?_⟩
  obtain ⟨εr, δ', Λ', hεr, hεr1, hεrcap, hδ', hΛ', hT3⟩ :=
    hT3 β hβ2 hβ1 hβ1b hβ11 hβ3 ζ cap hζ1 hζ2 hcap
  refine ⟨εr, δ', Λ', hεr, hεr1, hεrcap, hδ', hΛ', fun T hT hTΛ e he he1 δ₀ hδ₀ hδ₀S W _ g B
    hcoll hder => ?_⟩
  obtain ⟨V, hTV, δ, hδ, hδδ', hev⟩ :=
    hT3 T hT hTΛ e he he1 δ₀ hδ₀ (hδ₀S.trans (min_le_left _ _)) W g B hcoll hder
  refine ⟨V, hTV, δ, hδ, hδδ', fun Lmax hLmax βd εN hβd hεN => ?_⟩
  obtain ⟨hw', hw'c⟩ := lpa01_volume_bounds_BDRY5 hΛ hw hwc
  have hK2 : 2 ≤ K := le_trans (by norm_num) hK
  have hnR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine ((hev Lmax hLmax βd εN hβd hεN).and ((hnR.eventually_ge_atTop 3).and
    (hnR.eventually_ge_atTop (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))⁻¹))).mono fun n hn => ?_
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hn3 : (3 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by rw [hcast]; linarith only [hn.2.1]
  have hn0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith only [hn3]
  have hinv : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := by
    refine (inv_le_comm₀ hn0 hw').mpr ?_
    rw [hcast]
    linarith only [hn.2.2]
  -- BCP04.a at the member's counterexample index `n + 1` (BSA06 pair kernel, one member)
  exact BoundaryPacketsOutBFR_BQ.mono_index_IDX4 (idx := (n : ℝ))
    (fun ρ hρ hρw p hp => (hpair (W n) (g n) K _ hK2
      (boundaryCounterexampleRatio_pos hδ₀ (Nat.le_add_left 1 n)).le
      ((boundaryCounterexampleRatio_le δ₀ (n + 1)).trans (hδ₀S.trans (min_le_right _ _))) (B n)
      (hcoll n) (hder n) hA hn3 (boundaryCounterexampleRatio_mul_le δ₀ (Nat.le_add_left 1 n))
      hinv hw'c p (hρ p) (hρw p).le).2.2.2 hp) hn.1

end DifferentialGeometry.Geometry.Collapse
