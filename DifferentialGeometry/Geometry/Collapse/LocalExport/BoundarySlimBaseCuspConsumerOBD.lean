import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimBaseCuspDescentOBD

/-!
# BCG07 clause 07.g3, assembled (lane O-BD2b)

Lane O-BD1 (by O-BD2b, suffix `_OBD`), consumer of G3c / G3d: the whole clause 07.g3 at a cusp
frontier point of the slim base domain, in the shape of review 77 (D77-6):
**`BoundaryGaf02ChainE.bcg07_clause_g3_OBD`** — if the cusp front `H_b` meets `X₃`, then `H_b` is
the whole slim fibre over ONE `y₀ ∈ B₃`; the descended cusp function `h_b` (`h_b ∘ f₃ =
u_b/v_b − 40`) vanishes at `y₀`; near `y₀` the slim base domain is `{0 ≤ φ_b}` (`φ_b ∘ f₃ =
u_b − 40 v_b`); and along the ACTUAL base chart `σ` at `y₀` the derivative of `h_b ∘ σ` is non-zero.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

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

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **BCG07 07.g3, assembled** (A4 data `Bs`, `WF` v2b; the zero domains `Z`; E4b premises). -/
theorem bcg07_clause_g3_OBD {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count)
    (hX : (C.toChain.cuspFront_BIF i ∩ Bs.source 2).Nonempty) :
    ∃ y₀ ∈ Bs.base 2, C.toChain.cuspFront_BIF i = Bs.fibre 2 y₀ ∧
      cuspRatioBase_OBD i y₀ = 0 ∧
      (∃ O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)), IsOpen O ∧
        y₀ ∈ O ∧ ∀ y ∈ Bs.base 2 ∩ O, (y ∈ Bs.slimBaseDomain_BIFc ↔ 0 ≤ cuspBaseCLM_OBD i y)) ∧
      ∃ σ : EuclideanSpace ℝ (Fin 1) →
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count),
        σ 0 = y₀ ∧ ContDiff ℝ ∞ σ ∧ (∃ O, IsOpen O ∧ range σ = Bs.base 2 ∩ O) ∧
        fderiv ℝ (cuspRatioBase_OBD i ∘ σ) 0 ≠ 0 := by
  obtain ⟨y₀, hy₀, hH, -, O, hO, hy₀O, hD⟩ :=
    C.slimBaseDomain_cuspEquation_OBD WF Z hrd hrd4 hrdc hprem hθ i hX
  obtain ⟨p, hp, hpX⟩ := hX
  have hpy : C.toChain.stageMap 2 p = y₀ := by
    have h : p ∈ Bs.fibre 2 y₀ := hH ▸ hp
    exact h.2
  obtain ⟨σ, hσ0, hσs, -, -, hσO, hne⟩ :=
    C.cuspRatio_baseChart_OBD WF hrd hrd4 hrdc hprem hθ i hp hpX
  have hfr : (9 / 10 : ℝ) ≤ chainBoundaryV_BCG6K C.toChain.E i p ∧
      chainBoundaryU_BCG6K C.toChain.E i p = 40 * chainBoundaryV_BCG6K C.toChain.E i p := hp
  have hzero : cuspRatioBase_OBD i y₀ = 0 := by
    rw [← hpy, cuspRatioBase_stageMap_OBD C.toChain 2 i p, hfr.2,
      mul_div_assoc, div_self (by linarith [hfr.1]), mul_one, sub_self]
  exact ⟨y₀, hy₀, hH, hzero, ⟨O, hO, hy₀O, hD⟩, σ, hσ0.trans hpy, hσs, hσO, hne⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
