import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementChainBC2

/-!
# Consumer of the chain-level (Repl_∂): the localized edge region of `M₂` lies in `P_e` (lane
S-BCF02b, G2)

`BoundaryGaf02ChainE.edgePiece_of_strict_BC2`: a point `q ∈ M₂` of the edge chart `i`
(`d(q, i) < 100Δρ_i`, `|η_i(q)|, t(q) ≤ 4.01Δ`) on or below the rim `T(q) ≤ 4Δ` lies in
`P_e = M₂ ∩ X₂`: the chain-level replacement `bcf02_strict_replacement_BC2` gives the `edgeB`
centre `j` with `ζ_j(q) = 1`, `|η_j(q)| < 2Δ` (so `q ∈ B(j, 100Δρ_j)`), and EDP02's entry
`edge_entry` puts `q` in `X₂`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {Bs : BoundaryGaf02BasesV2 C.toChain}

include C in
/-- **The localized edge region of `M₂` is in `P_e`** (consumer of
`bcf02_strict_replacement_BC2`). -/
theorem edgePiece_of_strict_BC2 (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hn : 1140 * Δ ≤ 35 * (n : ℝ)) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000) (hβ2 : β 2 < 1 / 1000000)
    (hσL : (bcf02SigmaStrict_BC2 Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02EtaStrict_BC2 Δ)
    (h3b : 3 * b ≤ bcf02SigmaStrict_BC2 Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000)
    {q : W.pieceInterior ⊤} (hqM : q.val ∈ Kc.M₂) {i : W.pieceInterior ⊤}
    (hi : i ∈ S.stageCentres_BIF 1)
    (hqi : letI := inducedMetricSpace S.completion.metric; dist q i < 100 * Δ * S.rho i)
    (hηi : |S.edgeEta_BIF i q| ≤ 401 / 100 * Δ) (hhi : S.edgeHeightRaw q ≤ 401 / 100 * Δ)
    (hT4 : C.toChain.heightRatio q.val ≤ 4 * Δ) :
    q.val ∈ Kc.edgePiece := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨m, hm1, hη2, hζ, -, -⟩ := C.bcf02_strict_replacement_BC2 Z Kc hΔ hΛ hμ hτ hσc hn hT hσs
    hσs1 hb hs hβ2 hσL hbη h3b hbH hLΛ hμΔ q hqM i hi hqi hηi hhi
  rcases m with j | j | j
  · have h : (0 : Fin 3) = 1 := hm1
    exact absurd h (by decide)
  · have h : (2 : Fin 3) = 1 := hm1
    exact absurd h (by decide)
  · have hjc : j.1 ∈ S.stageCentres_BIF 1 := (Set.Finite.mem_toFinset _).mp j.2
    have hne : S.family.edgeB.cutoff_BAUGA j.1 q ≠ 0 := by
      change S.family.edgeB.cutoff_BAUGA j.1 q = 1 at hζ
      rw [hζ]
      exact one_ne_zero
    obtain ⟨-, hball, -, -⟩ := S.family.edgeB.mem_of_cutoff_ne_zero_BAUGA hΔ0 hne
    have hr := S.rho_pos j.1
    have hd : dist q j.1 < 100 * Δ * S.rho j.1 := by
      have h := (inv_mul_lt_iff₀ hr).mp hball
      linarith
    refine ⟨hqM, Bs.edge_entry q j.1 hjc hd ?_ ?_ hT4⟩
    · change |S.edgeEta_BIF j.1 q| < 2 * Δ at hη2
      linarith
    · linarith

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
