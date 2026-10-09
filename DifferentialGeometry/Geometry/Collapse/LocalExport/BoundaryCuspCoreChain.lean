import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreRow
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceBases

/-!
# BCG06, G5: the row bound to the boundary chain (lane BCG6-Kb)

BIFACE's interface (`BoundaryInterfaceChain`, `BoundaryInterfaceBases`, BIFACE G1): ONE supply
`S : BoundarySupply`, ONE chain `C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ`, its final map
`C.E`, the boundary pair `(u_b, v_b) = J_b(C.E)` (`chainBoundaryU_BCG6K C.E`,
`chainBoundaryV_BCG6K C.E`; BIFACE's `C.markerPair`), the cores `C.cuspCore_BIF` / fronts
`C.cuspFront_BIF` (= BCG6-K's sets at that pair, `cuspCore_BIF_eq_BCG6K`), and the actual zero cores
`ZC : BoundaryInitialCoresSpec C` (each inside an original selected zero ball of `S.family`).

The chain's BCG04 / BCG05 conclusions enter as the kernel's explicit premises at `C.E` (their
producers are rows E1–E3 of the boundary target text, lane BCG45-LOC's successor):
(BI) `|J_b(C.E) − P.block b| < ε∂` componentwise, (BFM) `v_b(C.E) = 1` on `Safe_b`, (BD) on
`band ∩ {38 ≤ η_b ≤ 42}`, and smoothness of `u_b` (from smoothness of `C.E`,
`contMDiff_chainBoundaryU_BCG6K`).

* `contMDiff_chainBoundaryU_BCG6K` (generic: `J_b ∘ E` is smooth when `E` is);
* `stage_three_BCG6K` (`C.stage 3 = C.E`), `c_two_pos_BCG6K` (`0 < c 2` from GAF01's CHOICE numbers),
  `cuspCore_BIF_eq_BCG6K`, `cuspFront_BIF_eq_BCG6K`;
* **`bcg06_row_chain_BCG6K`**: on the chain, every component satisfies the branch-free clauses and the
  geometric output holds with the original selected zero balls `S.zeroBall_BCG6K`;
* **`bcg06_output_chain_initialCores_BCG6K`**: the geometric output with the ACTUAL zero cores
  `ZC.core` of the chain (separated branch: every core disjoint from every actual zero core);
  `cuspCore_BIF_disjoint_initialCores_BCG6K` (transport on the separated spec).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

section Generic

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `J_b` read as a continuous linear functional: the first coordinate of the slot of `b`. -/
def chainBoundaryUCLM_BCG6K (b : κ) : BlockSpace (fun _ : ι ⊕ κ => ℝ²) →L[ℝ] ℝ :=
  (EuclideanSpace.proj (0 : Fin 2)).comp ((ContinuousLinearMap.fst ℝ ℝ² ℝ).comp
    (((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ² ℝ : WithLp 2 (ℝ² × ℝ) ≃L[ℝ] ℝ² × ℝ) :
      WithLp 2 (ℝ² × ℝ) →L[ℝ] ℝ² × ℝ).comp
      (PiLp.proj 2 (fun _ : ι ⊕ κ => WithLp 2 (ℝ² × ℝ)) (Sum.inr b))))

/-- **`u_b = (J_b ∘ E).1` is smooth when `E` is.** -/
theorem contMDiff_chainBoundaryU_BCG6K {E' H' M : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace M]
    [ChartedSpace H' M] {E : M → BlockSpace (fun _ : ι ⊕ κ => ℝ²)}
    (hE : ContMDiff I 𝓘(ℝ, BlockSpace (fun _ : ι ⊕ κ => ℝ²)) ∞ E) (b : κ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (chainBoundaryU_BCG6K E b) := by
  have h := (chainBoundaryUCLM_BCG6K (ι := ι) b).contDiff.comp_contMDiff hE
  exact h

end Generic

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S}

namespace BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S Φ} {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)

/-- The last stage output is the final map. -/
theorem stage_three_BCG6K : C.stage 3 = C.E :=
  rfl

include C in
/-- GAF01's CHOICE numbers of the chain give `0 < c 2` (the constant `c₃` of (BD)). -/
theorem c_two_pos_BCG6K : 0 < c 2 := by
  obtain ⟨hj, h0, -, -, -, -, h1, -, -, -, -, h2, -, -⟩ := C.numbers
  obtain ⟨hΞ0, hS0, -⟩ := hj 0
  obtain ⟨hΞ1, hS1, -⟩ := hj 1
  obtain ⟨hΞ2, hS2, -⟩ := hj 2
  have hc0 : 0 < c 0 := lt_of_le_of_lt (by positivity) h0
  have hc1 : 0 < c 1 := by nlinarith
  nlinarith

/-- BIFACE's chain core is BCG6-K's core at `(u_b, v_b) = J_b(C.E)`. -/
theorem cuspCore_BIF_eq_BCG6K (i : Fin S.packet.cusp.count) :
    C.cuspCore_BIF i = S.packet.toBoundaryCollarPacket.cuspCore_BCG6K i
      (chainBoundaryU_BCG6K C.E) (chainBoundaryV_BCG6K C.E) :=
  rfl

/-- BIFACE's chain front is BCG6-K's front at `(u_b, v_b) = J_b(C.E)`. -/
theorem cuspFront_BIF_eq_BCG6K (i : Fin S.packet.cusp.count) :
    C.cuspFront_BIF i = S.packet.toBoundaryCollarPacket.cuspFront_BCG6K i
      (chainBoundaryU_BCG6K C.E) (chainBoundaryV_BCG6K C.E) :=
  rfl

/-- **BCG06 on the boundary chain**: with the chain's (BI), (BFM), (BD) at `C.E`
(`ε∂ < 10⁻⁶`, `0 ≤ c₃ < 10⁻⁵`) and `u_b` smooth, every component satisfies the branch-free
clauses (whole inner collar by the relative flow on `W`, labelled `T² × [0, 1]`, `∂C_b = ∂_bW ⊔ H_b`,
`C_b ∩ ∂W = ∂_bW`, `frontier C_b = H_b`, front in `39.99 < η_b < 40.01` with `v_b = 1` and
`d(u_b − 40) ≠ 0`, strict markers), and the geometric output holds with the original selected
zero balls of the stored family. -/
theorem bcg06_row_chain_BCG6K
    (hu : ∀ i, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (chainBoundaryU_BCG6K C.E i))
    {εd c₃ : ℝ} (hεd : εd < 1 / 1000000) (hc₃0 : 0 ≤ c₃) (hc₃ : c₃ < 1 / 100000)
    (hBI : ∀ (i : Fin S.packet.cusp.count) (p : W.Carrier),
      |(augmentedBoundaryCoord_BC7C i (C.E p)).1 -
          (S.packet.toBoundaryCollarPacket.block i p).1| < εd ∧
        |(augmentedBoundaryCoord_BC7C i (C.E p)).2 -
          (S.packet.toBoundaryCollarPacket.block i p).2| < εd)
    (hBFM : ∀ (i : Fin S.packet.cusp.count),
      ∀ p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i,
        (augmentedBoundaryCoord_BC7C i (C.E p)).2 = 1)
    (hBD : ∀ (i : Fin S.packet.cusp.count), ∀ x ∈ S.packet.toBoundaryCollarPacket.collarBand_BAUGA i,
      38 ≤ S.packet.toBoundaryCollarPacket.height i x →
      S.packet.toBoundaryCollarPacket.height i x ≤ 42 →
      ∀ v : TangentSpace W.model x,
        |mvfderiv W.model (fun y => chainBoundaryU_BCG6K C.E i y -
            S.packet.toBoundaryCollarPacket.height i y) x v| ≤ c₃ * Real.sqrt (g.inner x v v)) :
    (∀ i, S.packet.toBoundaryCollarPacket.BoundaryCuspCoreComponent_BCG6K
        (chainBoundaryU_BCG6K C.E) (chainBoundaryV_BCG6K C.E) i) ∧
      BoundaryCollarPacket.BoundaryGeometricOutput_BCG6K S.packet.toBoundaryCollarPacket
        (chainBoundaryU_BCG6K C.E) (chainBoundaryV_BCG6K C.E)
        S.toBoundarySupplyCore.zeroBall_BCG6K :=
  S.toBoundarySupplyCore.bcg06_row_supply_BCG6K hu hεd hc₃0 hc₃ hBI hBFM hBD

/-- **Transport to the actual zero cores of the chain** (separated branch): every core is disjoint
from every zero core `Z_k` of `ZC` (each `Z_k` lies in an original selected zero ball). -/
theorem cuspCore_BIF_disjoint_initialCores_BCG6K
    (h : S.packet.toBoundaryCollarPacket.BoundaryCuspCoreSpec_BCG6K (chainBoundaryU_BCG6K C.E)
      (chainBoundaryV_BCG6K C.E) S.toBoundarySupplyCore.zeroBall_BCG6K)
    (ZC : BoundaryInitialCoresSpec C) (i : Fin S.packet.cusp.count) (k : Fin ZC.count) :
    Disjoint (C.cuspCore_BIF i) (ZC.core k) :=
  S.toBoundarySupplyCore.cuspCore_disjoint_of_subset_supplyZeroBall_BCG6K h ZC.core ZC.centre
    ZC.core_subset_ball i k

/-- **BCG06 on the chain with the ACTUAL zero cores**: the geometric output whose separated branch
has every core disjoint from every actual zero core `ZC.core k` of the chain (draft 61 §4.4, D65-5:
original zero balls first, then the actual `Z_k ⊆` original balls). -/
theorem bcg06_output_chain_initialCores_BCG6K
    (hu : ∀ i, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (chainBoundaryU_BCG6K C.E i))
    {εd c₃ : ℝ} (hεd : εd < 1 / 1000000) (hc₃0 : 0 ≤ c₃) (hc₃ : c₃ < 1 / 100000)
    (hBI : ∀ (i : Fin S.packet.cusp.count) (p : W.Carrier),
      |(augmentedBoundaryCoord_BC7C i (C.E p)).1 -
          (S.packet.toBoundaryCollarPacket.block i p).1| < εd ∧
        |(augmentedBoundaryCoord_BC7C i (C.E p)).2 -
          (S.packet.toBoundaryCollarPacket.block i p).2| < εd)
    (hBFM : ∀ (i : Fin S.packet.cusp.count),
      ∀ p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i,
        (augmentedBoundaryCoord_BC7C i (C.E p)).2 = 1)
    (hBD : ∀ (i : Fin S.packet.cusp.count), ∀ x ∈ S.packet.toBoundaryCollarPacket.collarBand_BAUGA i,
      38 ≤ S.packet.toBoundaryCollarPacket.height i x →
      S.packet.toBoundaryCollarPacket.height i x ≤ 42 →
      ∀ v : TangentSpace W.model x,
        |mvfderiv W.model (fun y => chainBoundaryU_BCG6K C.E i y -
            S.packet.toBoundaryCollarPacket.height i y) x v| ≤ c₃ * Real.sqrt (g.inner x v v))
    (ZC : BoundaryInitialCoresSpec C) :
    BoundaryCollarPacket.BoundaryGeometricOutput_BCG6K S.packet.toBoundaryCollarPacket
      (chainBoundaryU_BCG6K C.E) (chainBoundaryV_BCG6K C.E) ZC.core := by
  refine (S.packet.toBoundaryCollarPacket.bcg06_row_BCG6K
    (cuspTolerance_le_thousandth_BCUSP1 _ _ _) hu hεd hc₃0 hc₃ hBI hBFM hBD ZC.core ?_).2
  rcases S.toBoundarySupplyCore.geometric_alternative_BCG6K with hprod | ⟨hsep, hZ⟩
  · exact Or.inl hprod
  · refine Or.inr ⟨hsep, fun k i => ?_⟩
    obtain ⟨hk, hsub⟩ := ZC.core_subset_ball k
    exact (hZ ⟨ZC.centre k, hk⟩ i).mono_left hsub

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
