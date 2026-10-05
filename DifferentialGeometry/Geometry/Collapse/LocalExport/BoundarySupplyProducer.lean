import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySupply

/-!
# The producers of `BoundarySupplyCore` and `BoundarySupply` (lane BAUG-A, G4)

* `lc88_boundarySupplyCore_BAUGA`: the statement of `lc88_boundary_packets_BFRZ_BFZD` (same prefix,
  same tail) whose per-member conclusion is packaged as ONE `BoundarySupplyCore` for every
  orientation `oM` of `W°`;
* `lc88_boundarySupply_BAUGA`: the statement of `lc88_boundary_packets_BFRZ_BA_BIND` (same prefix
  with BCG8's requests, same tail) packaged as ONE `BoundarySupply` (core + BCG02's joint (BA)
  certificates on the projection of the SAME family, D64-6).
The export packet, the scale, the completion and the family are those of the producer, and every
field is the producer's clause about them (D61-2). The member ratio is
`δ_{n+1} = boundaryCounterexampleRatio δ₀ (n + 1)` and the BCP04.a index is `n`.
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

/-- **The `BoundarySupplyCore` producer** (D61-1, D61-2): T3B on the complete final family, its
per-member joint conclusion stored as ONE `BoundarySupplyCore` (for every orientation `oM`). -/
theorem lc88_boundarySupplyCore_BAUGA
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
        ∀ oM : ManifoldOrientation 𝓘(ℝ, E3) ((W n).pieceInterior ⊤) 3,
          Nonempty (BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
            V vs ζ Λ' (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1)) n (B n) oM) := by
  refine (lc88_boundary_packets_BFRZ_BFZD K hK A hA).elim fun δStar t1 => ?_
  refine ⟨δStar, t1.1, ?_⟩
  refine t1.2.elim fun a₂ t2 => ?_
  refine ⟨a₂, t2.1, fun γ hγ hγ1 => ?_⟩
  refine (t2.2 γ hγ hγ1).elim fun β₀ t3 => ?_
  refine ⟨β₀, t3.1, t3.2.1, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  refine (t3.2.2 βc γc hβc hβγ hγc hγc1).elim fun σ₀ t4 => ?_
  refine t4.2.elim fun Δ₀ t5 => ?_
  refine ⟨σ₀, t4.1, Δ₀, t5.1, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  refine (t5.2 β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ).elim fun τ₀ t6 => ?_
  refine t6.2.elim fun bc₀ t7 => ?_
  refine ⟨τ₀, t6.1, bc₀, t7.1, fun σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 s b' s' i1 i2 i3
    i4 i5 i6 i7 i8 => ?_⟩
  refine (t7.2 σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 s b' s' i1 i2 i3 i4 i5 i6 i7
    i8).elim fun a₀ t8 => ?_
  refine t8.elim fun b₁ t9 => ?_
  refine ⟨a₀, b₁, t9.1, t9.2.1, fun σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 k6 => ?_⟩
  refine (t9.2.2 σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 k6).elim fun w₀ t10 => ?_
  refine ⟨w₀, t10.1, fun w hw hww hwc => ?_⟩
  refine (t10.2 w hw hww hwc).elim fun bd₀ t11 => ?_
  refine ⟨bd₀, t11.1, fun b hb l1 l2 l3 l4 l5 σs vs m1 m2 m3 => ?_⟩
  refine (t11.2 b hb l1 l2 l3 l4 l5 σs vs m1 m2 m3).elim fun b₀ t12 => ?_
  refine ⟨b₀, t12.1, fun β hβ2 hβ1 hβ1b hβ11 hβ3 ζ cap hζ1 hζ2 hcap => ?_⟩
  refine (t12.2 β hβ2 hβ1 hβ1b hβ11 hβ3 ζ cap hζ1 hζ2 hcap).elim fun εr t13 => ?_
  refine t13.elim fun δ' t14 => ?_
  refine t14.elim fun Λ' t15 => ?_
  refine ⟨εr, δ', Λ', t15.1, t15.2.1, t15.2.2.1, t15.2.2.2.1, t15.2.2.2.2.1,
    fun T hT hTΛ e he he1 δ₀ hδ₀ hδ₀S W _ g B hcoll hder => ?_⟩
  refine (t15.2.2.2.2.2 T hT hTΛ e he he1 δ₀ hδ₀ hδ₀S W g B hcoll hder).elim fun V t16 => ?_
  refine t16.2.elim fun δ t17 => ?_
  refine ⟨V, t16.1, δ, t17.1, t17.2.1, fun Lmax hLmax βd εN hβd hεN => ?_⟩
  refine (t17.2.2 Lmax hLmax βd εN hβd hεN).mono fun n hn oM => ?_
  obtain ⟨P, hcusp, hratio, ρ, hρpos, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, hconn, ĝ, O, hO,
    hOsub, hOeq, hle, hcomp, hF⟩ := hn
  obtain ⟨F, r1, r2, r3, -, r5, r6, r7⟩ := hF oM
  exact ⟨{
    packet := P
    rho := ρ
    rho_pos := hρpos
    completion := {
      metric := ĝ
      agree := O
      isOpen_agree := hO
      far_subset_agree := hOsub
      inner_eq_on_agree := hOeq
      inner_le := hle
      complete := hcomp }
    family := F
    cusp_eq := hcusp
    scale_spec := ⟨c1, c2, c3, c4, c10⟩
    cusp_spec := ⟨hratio, c5, c6, c7, c8, c9⟩
    transport_spec := ⟨r1, r2, r3, r5, r6⟩
    geometric_cases := r7 }⟩

/-- **The `BoundarySupply` producer with BCG02's joint (BA) certificates** (D61-2, D64-6): the
joint producer `lc88_boundary_packets_BFRZ_BA_BIND` (T3B on BFRZ with BCG8's requests and the (BA)
block on the projection of the SAME family), its per-member conclusion stored as ONE
`BoundarySupply` (for every orientation `oM` of `W°`). -/
theorem lc88_boundarySupply_BAUGA
    (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) {θ ν : ℝ} (hθ : 0 < θ)
    (hθ1 : θ < 1) (hν : 0 < ν) (hν1 : ν < 1 / 1000000) :
    ∃ σC : ℝ, 0 < σC ∧ ∃ ηC : ℝ, 0 < ηC ∧
    ∃ δStar : ℝ, 0 < δStar ∧
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → γ ≤ θ ^ 2 / 10000000 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      3 * β₂ ≤ σC → β₂ ≤ θ ^ 2 / 10000000 → ∃ σE : ℝ, 0 < σE ∧ ∃ ηE : ℝ, 0 < ηE ∧
      ∃ σS : ℝ, 0 < σS ∧ ∃ ηS : ℝ, 0 < ηS ∧
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 → ε ≤ 1 / 10 ^ 8 → μ ≤ 1 / 10 ^ 8 →
        μ * Δ ≤ θ / 4 → σc ≤ θ ^ 2 / 10000000 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) → 100 * Δ * Λ ≤ 1 / 10 ^ 8 →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 → ∃ bd₀ : ℝ, 0 < bd₀ ∧
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → b < bd₀ → 3 * b ≤ σE →
        b * (2 * (421 * Δ + 1)) ≤ 1 → b ≤ θ ^ 2 / 10000000 →
      ∀ σs vs : ℝ, 0 < σs → σs ≤ 1 / 100 → 0 < vs → vs ≤ θ / 4 → σs ≤ θ ^ 2 / 10000000 →
      ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
        3 * ν ≤ β 3 → 2 * β 1 ≤ ηC → 2 * β 1 ≤ ηE → 2 * β 1 ≤ ηS →
        1000000 * Δ * β 1 ^ 3 < 1 → 3 * β 1 ≤ σS → β 1 * (2 * (1950002 * Δ + 1)) ≤ 1 →
        β 1 ≤ θ ^ 2 / 10000000 →
      ∀ ζ cap : ℝ, β 1 < ζ → ζ < 1 → 0 < cap →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ εr < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ Lmax : ℝ, 0 < Lmax → σC⁻¹ ≤ Lmax →
      σE⁻¹ ≤ Lmax → σS⁻¹ ≤ Lmax → ∀ βd εN : ℝ, 0 < βd → 0 < εN → εN ≤ θ ^ 2 / 40000000 →
      ∀ᶠ n in atTop,
        ∀ oM : ManifoldOrientation 𝓘(ℝ, E3) ((W n).pieceInterior ⊤) 3,
          Nonempty (BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
            vs ζ Λ' θ (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1)) n (B n) oM) := by
  refine (lc88_boundary_packets_BFRZ_BA_BIND K hK A hA hθ hθ1 hν hν1).elim fun σC u1 => ?_
  refine ⟨σC, u1.1, ?_⟩
  refine u1.2.elim fun ηC u2 => ?_
  refine ⟨ηC, u2.1, ?_⟩
  refine u2.2.elim fun δStar t1 => ?_
  refine ⟨δStar, t1.1, ?_⟩
  refine t1.2.elim fun a₂ t2 => ?_
  refine ⟨a₂, t2.1, fun γ hγ hγ1 hγθ => ?_⟩
  refine (t2.2 γ hγ hγ1 hγθ).elim fun β₀ t3 => ?_
  refine ⟨β₀, t3.1, t3.2.1, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  refine (t3.2.2 βc γc hβc hβγ hγc hγc1).elim fun σ₀ t4 => ?_
  refine t4.2.elim fun Δ₀ t5 => ?_
  refine ⟨σ₀, t4.1, Δ₀, t5.1, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ hσC hβθ => ?_⟩
  refine (t5.2 β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ hσC hβθ).elim fun σE u3 => ?_
  refine u3.2.elim fun ηE u4 => ?_
  refine u4.2.elim fun σS u5 => ?_
  refine u5.2.elim fun ηS u6 => ?_
  refine u6.2.elim fun τ₀ t6 => ?_
  refine t6.2.elim fun bc₀ t7 => ?_
  refine ⟨σE, u3.1, ηE, u4.1, σS, u5.1, ηS, u6.1, τ₀, t6.1, bc₀, t7.1,
    fun σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 s b' s' i1 i2 i3 i4 i5 i6 i7 i8 =>
      ?_⟩
  refine (t7.2 σc ε μ τ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 s b' s' i1 i2 i3 i4 i5 i6
    i7 i8).elim fun a₀ t8 => ?_
  refine t8.elim fun b₁ t9 => ?_
  refine ⟨a₀, b₁, t9.1, t9.2.1, fun σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 k6 => ?_⟩
  refine (t9.2.2 σ j1 j2 j3 j4 Λ hΛ k1 k2 k3 k4 k5 k6).elim fun w₀ t10 => ?_
  refine ⟨w₀, t10.1, fun w hw hww hwc => ?_⟩
  refine (t10.2 w hw hww hwc).elim fun bd₀ t11 => ?_
  refine ⟨bd₀, t11.1, fun b hb l1 l2 l3 l4 l5 l6 l7 l8 σs vs m1 m2 m3 m4 m5 => ?_⟩
  refine (t11.2 b hb l1 l2 l3 l4 l5 l6 l7 l8 σs vs m1 m2 m3 m4 m5).elim fun b₀ t12 => ?_
  refine ⟨b₀, t12.1, fun β hβ2 hβ1 hβ1b hβ11 hβ3 q1 q2 q3 q4 q5 q6 q7 q8 ζ cap hζ1 hζ2 hcap =>
    ?_⟩
  refine (t12.2 β hβ2 hβ1 hβ1b hβ11 hβ3 q1 q2 q3 q4 q5 q6 q7 q8 ζ cap hζ1 hζ2 hcap).elim
    fun εr t13 => ?_
  refine t13.elim fun δ' t14 => ?_
  refine t14.elim fun Λ' t15 => ?_
  refine ⟨εr, δ', Λ', t15.1, t15.2.1, t15.2.2.1, t15.2.2.2.1, t15.2.2.2.2.1,
    fun T hT hTΛ e he he1 δ₀ hδ₀ hδ₀S W _ g B hcoll hder => ?_⟩
  refine (t15.2.2.2.2.2 T hT hTΛ e he he1 δ₀ hδ₀ hδ₀S W g B hcoll hder).elim fun V t16 => ?_
  refine t16.2.elim fun δ t17 => ?_
  refine ⟨V, t16.1, δ, t17.1, t17.2.1, fun Lmax hLmax o1 o2 o3 βd εN hβd hεN hεNθ => ?_⟩
  refine (t17.2.2 Lmax hLmax o1 o2 o3 βd εN hβd hεN hεNθ).mono fun n hn oM => ?_
  obtain ⟨P, hcusp, hratio, ρ, hρpos, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, hconn, ĝ, O, hO,
    hOsub, hOeq, hle, hcomp, hF⟩ := hn
  obtain ⟨F, r1, r2, r3, -, r5, r6, r7, ba⟩ := hF oM
  exact ⟨{
    packet := P
    rho := ρ
    rho_pos := hρpos
    completion := {
      metric := ĝ
      agree := O
      isOpen_agree := hO
      far_subset_agree := hOsub
      inner_eq_on_agree := hOeq
      inner_le := hle
      complete := hcomp }
    family := F
    cusp_eq := hcusp
    scale_spec := ⟨c1, c2, c3, c4, c10⟩
    cusp_spec := ⟨hratio, c5, c6, c7, c8, c9⟩
    transport_spec := ⟨r1, r2, r3, r5, r6⟩
    geometric_cases := r7
    ba_spec := ba }⟩

end DifferentialGeometry.Geometry.Collapse
