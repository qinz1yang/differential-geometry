import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBcg07RowBGR

/-!
# BCG07 on a non-empty chain with an A4 output: the existential form (S-BCG-ROWS3, G34)

* **`bcg07_row_of_A4_BGR`**: `h` is the conclusion of the production A2 v3 (a chain on `DP`),
  `hA4` the conclusion of A4 (v2 bases with the whole-fibre layer v2b on every chain). The
  conclusion is `bcg07_row_BGR` (F1 ∧ F2 ∧ F3 ∧ F4a–d ∧ F5) ∧ `bcg07_row_extras_BGR` on ONE chain
  and ONE A4 output. Premises: the numerical block of `bcg07_row_BGR` (F1's six, `hεr`, `he`, E4's
  `r_∂` block with `θ`).
* `bcg07_slim_base_of_row_BGR`: consumer of F3, F4c and F5 of the row: from `Z` the slim base
  domain facts (`X₃ ∩ f₃⁻¹(D₃) = M₁ ∩ X₃`, `D₃ ∖ int D₃ ⊆ f₃(∂M₁ ∩ X₃)`).
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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

/-- **BCG07 on a non-empty chain with an A4 output** (existential form of `bcg07_row_BGR` and
`bcg07_row_extras_BGR`). -/
theorem bcg07_row_of_A4_BGR
    (h : Nonempty (BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj))
    (hA4 : ∀ C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj,
      ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs)
    (h3βc : 3 * βc ≤ β 2) (hβ2 : β 2 < 1) (hγ : 0 ≤ γ) (hγ34 : γ ≤ 3 / 4)
    (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj,
      ∃ Bs : BoundaryGaf02BasesV2 C.toChain, BoundaryWholeFiberSpecV2b C.toChain Bs ∧
        -- F1
        ((∀ y ∈ Bs.base 1, ∀ p ∈ Bs.fibre 1 y, C.toChain.heightRatio p = 4 * Δ →
          p ∈ Bs.source 0 ∧
            Bs.fibre 1 y ∩ {q | C.toChain.heightRatio q = 4 * Δ} =
              Bs.fibre 0 (C.toChain.stageMap 0 p)) ∧
        -- F2
        (∀ (st : Fin 3) (i : Fin S.packet.cusp.count) (p q : W.Carrier),
          p ∈ C.toChain.cuspFront_BIF i → C.toChain.stageMap st q = C.toChain.stageMap st p →
            q ∈ C.toChain.cuspFront_BIF i) ∧
        -- F3
        Nonempty (BoundaryActualZeroDomains_BIFc C.toChain Bs) ∧
        -- F4a
        IsCompact C.toChain.M₁_BIFc ∧
        -- F4b
        C.toChain.M₁_BIFc ⊆ {p | ENNReal.ofReal 35 ≤ distanceToBoundary W g p} ∧
        -- F4c
        frontier C.toChain.M₁_BIFc =
          (⋃ k, C.toChain.actualZeroFace_BIFc k) ∪ ⋃ i, C.toChain.cuspFront_BIF i ∧
        -- F4d
        (∀ st : Fin 3, st ≠ 1 → C.toChain.M₁_BIFc ∩ Bs.source st =
          Bs.source st ∩ C.toChain.stageMap st ⁻¹' (C.toChain.stageMap st '' (C.toChain.M₁_BIFc ∩
            Bs.source st))) ∧
        -- F5
        (∀ i : Fin S.packet.cusp.count, (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty →
          ∃ y ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y)) ∧
        -- the complement used by BCF01
        (Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' Bs.slimBaseDomain_BIFc =
            C.toChain.M₁_BIFc ∩ Bs.source 2 ∧
          Bs.slimBaseDomain_BIFc \ relInterior_BIF (Bs.base 2) Bs.slimBaseDomain_BIFc ⊆
            C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ Bs.source 2) ∧
          (∀ k : S.ZeroIdx_BAUGC, (C.toChain.actualZeroFace_BIFc k ∩ Bs.source 2).Nonempty →
            ∃ y ∈ Bs.base 2, C.toChain.actualZeroFace_BIFc k = Bs.fibre 2 y) ∧
          (∀ i : Fin S.packet.cusp.count, (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty →
            ∃ y ∈ Bs.base 2,
              C.toChain.stageMap 2 '' (C.toChain.cuspFront_BIF i ∩ Bs.source 2) = {y}) ∧
          (C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ Bs.source 2)).Finite ∧
          frontier C.toChain.M₁_BIFc ⊆ {p | ENNReal.ofReal 35 ≤ distanceToBoundary W g p} ∧
          (∀ st : Fin 3, st ≠ 1 →
            IsClosed (Subtype.val ⁻¹' (C.toChain.stageMap st '' (C.toChain.M₁_BIFc ∩
              Bs.source st)) : Set (Bs.base st)))) := by
  obtain ⟨C⟩ := h
  obtain ⟨Bs, WF⟩ := hA4 C
  exact ⟨C, Bs, WF, C.bcg07_row_BGR h3βc hβ2 hγ hγ34 hc hC hεr he hrd hrd4 hrdc hprem hθ WF,
    C.bcg07_row_extras_BGR hεr hrd hrd4 hrdc hprem hθ WF⟩

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **Consumer of the row's F3**: the produced `Z` gives the slim base domain facts
(`X₃ ∩ f₃⁻¹(D₃) = M₁ ∩ X₃`, `D₃ ∖ int D₃ ⊆ f₃(∂M₁ ∩ X₃)`) through BIFACEd's and B-BCF134's
consumers; the inputs are exactly the row's. -/
theorem bcg07_slim_base_of_row_BGR (h3βc : 3 * βc ≤ β 2) (hβ2 : β 2 < 1) (hγ : 0 ≤ γ)
    (hγ34 : γ ≤ 3 / 4) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) :
    Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' Bs.slimBaseDomain_BIFc =
        C.toChain.M₁_BIFc ∩ Bs.source 2 ∧
      Bs.slimBaseDomain_BIFc \ relInterior_BIF (Bs.base 2) Bs.slimBaseDomain_BIFc ⊆
        C.toChain.stageMap 2 '' (frontier C.toChain.M₁_BIFc ∩ Bs.source 2) := by
  obtain ⟨-, -, ⟨Z⟩, -⟩ := C.bcg07_row_BGR h3βc hβ2 hγ hγ34 hc hC hεr he hrd hrd4 hrdc hprem hθ WF
  exact ⟨Z.slimSource_inter_preimage_BIF, Z.relFrontier_slimBaseDomain_subset_BCF⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
