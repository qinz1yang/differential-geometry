import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreChain
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreSupplyApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceInhabitants

/-!
# BCG06, G5–G6: inhabitants and consumers of the row (lane BCG6-Kb)

* `original_boundaryCuspCoreComponent_BCG6K`: every collar packet with `ε ≤ 1/1000`, every
  component, the ORIGINAL pair `E = F_∂` (positive tolerances `ε∂ = 10⁻⁷`, `c₃ = 10⁻⁶`) satisfies
  `BoundaryCuspCoreComponent_BCG6K`; `doubleCusp_boundaryCuspCoreComponent_BCG6K`: the compiled
  non-trivial inhabitant on both ends of the double cusp `T² × [0, 240]`;
* `supply_original_bcg06_row_BCG6K`: the whole row on every stored supply for `J_b ∘ F_∂`;
* chain consumer: on every boundary chain over BIFACE's empty slot (all stage adjustments are the
  identity, `E_eq_boundaryOriginalMap_of_emptySlots_BCG6K`, e.g. BIFACE's `emptyChain_BIF`) the row
  holds at `(u_b, v_b) = J_b(C.E)`, with the original zero balls and with the actual zero cores of
  every `ZC : BoundaryInitialCoresSpec C` (`emptySlots_bcg06_row_chain_BCG6K`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis
open GC.Seifert

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

universe u

section Packet

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ}

namespace BoundaryCollarPacket

/-- **Inhabitant (every packet)**: the original pair `E = F_∂` satisfies the per-component BCG06
clauses for every component (`ε∂ = 10⁻⁷`, `c₃ = 10⁻⁶`). -/
theorem original_boundaryCuspCoreComponent_BCG6K (P : BoundaryCollarPacket W g K A w₀ ε)
    (hε : ε ≤ 1 / 1000) (b : Fin P.cusp.count) :
    P.BoundaryCuspCoreComponent_BCG6K P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K b :=
  boundaryCuspCoreComponent_BCG6K hε (P.contMDiff_originalBoundaryU_BCG6K b)
    (εd := 1 / 10000000) (c₃ := 1 / 1000000) (by norm_num) (by norm_num) (by norm_num)
    (P.original_BI_BCG6K (by norm_num) b) (P.original_BFM_BCG6K b)
    (P.original_BD_BCG6K (by norm_num) b)

end BoundaryCollarPacket

end Packet

/-- The double cusp carrier is connected (as in `SmallBoundaryPackets`). -/
local instance connectedSpace_annulusCircleCarrier_row_BCG6K :
    ConnectedSpace annulusCircleCarrier.{u}.Carrier :=
  connectedSpace_productSet (Or.inl rfl)

/-- **Compiled non-trivial inhabitant on the double cusp `T² × [0, 240]`**: both ends satisfy the
per-component BCG06 clauses for the original pair. -/
theorem doubleCusp_boundaryCuspCoreComponent_BCG6K (K : ℕ) (hK : 2 ≤ K) :
    ∃ a : ℝ, ∃ ha : 0 < a, ∃ A : ℝ → ℝ, (∀ w, 0 < A w) ∧
      ∃ P : BoundaryExportPacket annulusCircleCarrier.{u} (doubleCuspMetric.{u} a ha) K A
          (1 / 6408) (1 / 1000),
        P.cusp.count = 2 ∧ ∀ b,
          P.toBoundaryCollarPacket.BoundaryCuspCoreComponent_BCG6K P.originalBoundaryU_BCG6K
            P.originalBoundaryV_BCG6K b := by
  obtain ⟨a, ha, A, hA, P, hc⟩ := exists_doubleCuspBoundaryExport.{u} K hK (1 / 6408) (1 / 1000)
    (by norm_num) le_rfl (by norm_num) le_rfl
  exact ⟨a, ha, A, hA, P, hc, fun b =>
    P.toBoundaryCollarPacket.original_boundaryCuspCoreComponent_BCG6K le_rfl b⟩

section Supply

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- `J_b ∘ F_∂` of the stored supply is the original pair of its packet. -/
theorem chainBoundary_boundaryOriginalMap_BCG6K :
    chainBoundaryU_BCG6K S.boundaryOriginalMap =
        S.packet.toBoundaryCollarPacket.originalBoundaryU_BCG6K ∧
      chainBoundaryV_BCG6K S.boundaryOriginalMap =
        S.packet.toBoundaryCollarPacket.originalBoundaryV_BCG6K :=
  S.packet.toBoundaryCollarPacket.chainBoundary_original_eq_BCG6K S.interiorMapW_BAUGA

/-- **Consumer: the whole BCG06 row for the original map of every stored supply** (`E = F_∂`
through `J_b`, `ε∂ = 10⁻⁷`, `c₃ = 10⁻⁶`, the actual zero balls of the stored family). -/
theorem supply_original_bcg06_row_BCG6K :
    (∀ i, S.packet.toBoundaryCollarPacket.BoundaryCuspCoreComponent_BCG6K
        (chainBoundaryU_BCG6K S.boundaryOriginalMap) (chainBoundaryV_BCG6K S.boundaryOriginalMap)
        i) ∧
      BoundaryCollarPacket.BoundaryGeometricOutput_BCG6K S.packet.toBoundaryCollarPacket
        (chainBoundaryU_BCG6K S.boundaryOriginalMap) (chainBoundaryV_BCG6K S.boundaryOriginalMap)
        S.zeroBall_BCG6K := by
  obtain ⟨eU, eV⟩ := S.chainBoundary_boundaryOriginalMap_BCG6K
  rw [eU, eV]
  exact S.bcg06_row_supply_BCG6K
    (fun i => S.packet.toBoundaryCollarPacket.contMDiff_originalBoundaryU_BCG6K i)
    (εd := 1 / 10000000) (c₃ := 1 / 1000000) (by norm_num) (by norm_num) (by norm_num)
    (fun i => S.packet.toBoundaryCollarPacket.original_BI_BCG6K (by norm_num) i)
    (fun i => S.packet.toBoundaryCollarPacket.original_BFM_BCG6K i)
    (fun i => S.packet.toBoundaryCollarPacket.original_BD_BCG6K (by norm_num) i)

end BoundarySupplyCore

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM}

namespace BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S S.emptySlots_BIF} {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ}
  {bcut bder κ : ℝ} (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)

/-- Over the empty slot every stage adjustment is the identity, so `C.E = F_∂`. -/
theorem E_eq_boundaryOriginalMap_of_emptySlots_BCG6K : C.E = S.boundaryOriginalMap := by
  rw [E_eq]
  simp only [Ψ, BoundarySupply.emptySlots_adjust_BIF, Function.id_comp]

/-- **Consumer on the chain** (every chain over the empty slot, e.g. BIFACE's `emptyChain_BIF`):
the whole BCG06 row at `(u_b, v_b) = J_b(C.E)` with the original zero balls, and the geometric
output with the actual zero cores of every `ZC`. -/
theorem emptySlots_bcg06_row_chain_BCG6K :
    ((∀ i, S.packet.toBoundaryCollarPacket.BoundaryCuspCoreComponent_BCG6K
        (chainBoundaryU_BCG6K C.E) (chainBoundaryV_BCG6K C.E) i) ∧
      BoundaryCollarPacket.BoundaryGeometricOutput_BCG6K S.packet.toBoundaryCollarPacket
        (chainBoundaryU_BCG6K C.E) (chainBoundaryV_BCG6K C.E)
        S.toBoundarySupplyCore.zeroBall_BCG6K) ∧
      ∀ ZC : BoundaryInitialCoresSpec C,
        BoundaryCollarPacket.BoundaryGeometricOutput_BCG6K S.packet.toBoundaryCollarPacket
          (chainBoundaryU_BCG6K C.E) (chainBoundaryV_BCG6K C.E) ZC.core := by
  have hE := C.E_eq_boundaryOriginalMap_of_emptySlots_BCG6K
  obtain ⟨eU, eV⟩ := S.toBoundarySupplyCore.chainBoundary_boundaryOriginalMap_BCG6K
  have hU : chainBoundaryU_BCG6K C.E = S.packet.toBoundaryCollarPacket.originalBoundaryU_BCG6K := by
    rw [hE]
    exact eU
  have hV : chainBoundaryV_BCG6K C.E = S.packet.toBoundaryCollarPacket.originalBoundaryV_BCG6K := by
    rw [hE]
    exact eV
  have hu : ∀ i, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (chainBoundaryU_BCG6K C.E i) := fun i => by
    rw [hU]
    exact S.packet.toBoundaryCollarPacket.contMDiff_originalBoundaryU_BCG6K i
  have hBI : ∀ (i : Fin S.packet.cusp.count) (p : W.Carrier),
      |(augmentedBoundaryCoord_BC7C i (C.E p)).1 -
          (S.packet.toBoundaryCollarPacket.block i p).1| < 1 / 10000000 ∧
        |(augmentedBoundaryCoord_BC7C i (C.E p)).2 -
          (S.packet.toBoundaryCollarPacket.block i p).2| < 1 / 10000000 := fun i p => by
    have h1 : (augmentedBoundaryCoord_BC7C i (C.E p)).1 =
        S.packet.toBoundaryCollarPacket.originalBoundaryU_BCG6K i p := congrFun (congrFun hU i) p
    have h2 : (augmentedBoundaryCoord_BC7C i (C.E p)).2 =
        S.packet.toBoundaryCollarPacket.originalBoundaryV_BCG6K i p := congrFun (congrFun hV i) p
    rw [h1, h2]
    exact S.packet.toBoundaryCollarPacket.original_BI_BCG6K (by norm_num) i p
  have hBFM : ∀ (i : Fin S.packet.cusp.count),
      ∀ p ∈ S.packet.toBoundaryCollarPacket.safeBand_BAUGA i,
        (augmentedBoundaryCoord_BC7C i (C.E p)).2 = 1 := fun i p hp => by
    have h2 : (augmentedBoundaryCoord_BC7C i (C.E p)).2 =
        S.packet.toBoundaryCollarPacket.originalBoundaryV_BCG6K i p := congrFun (congrFun hV i) p
    rw [h2]
    exact S.packet.toBoundaryCollarPacket.original_BFM_BCG6K i p hp
  have hBD : ∀ (i : Fin S.packet.cusp.count),
      ∀ x ∈ S.packet.toBoundaryCollarPacket.collarBand_BAUGA i,
      38 ≤ S.packet.toBoundaryCollarPacket.height i x →
      S.packet.toBoundaryCollarPacket.height i x ≤ 42 →
      ∀ v : TangentSpace W.model x,
        |mvfderiv W.model (fun y => chainBoundaryU_BCG6K C.E i y -
            S.packet.toBoundaryCollarPacket.height i y) x v| ≤
          1 / 1000000 * Real.sqrt (g.inner x v v) := fun i => by
    rw [hU]
    exact S.packet.toBoundaryCollarPacket.original_BD_BCG6K (by norm_num) i
  exact ⟨C.bcg06_row_chain_BCG6K hu (by norm_num) (by norm_num) (by norm_num) hBI hBFM hBD,
    fun ZC => C.bcg06_output_chain_initialCores_BCG6K hu (by norm_num) (by norm_num)
      (by norm_num) hBI hBFM hBD ZC⟩

end BoundaryGaf02Chain

end Supply

end DifferentialGeometry.Geometry.Collapse
