import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreSupply
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreApplications

/-!
# BCG06, G4: consumer of the zero-ball binding on the stored supply (lane BCG6-Kb)

* `supply_original_boundaryGeometricOutput_BCG6K`: for EVERY stored supply
  `S : BoundarySupplyCore` (inhabited on the double-cusp standing sequence,
  `lc88_boundarySupply_doubleCusp_BAUGA`), the ORIGINAL augmented map `E = F_∂ = S.boundaryOriginalMap`
  read through BCG7-COLLAR's block coordinates `J_b` (`chainBoundaryU_BCG6K`,
  `chainBoundaryV_BCG6K`), with POSITIVE tolerances `ε∂ = 10⁻⁷`, `c₃ = 10⁻⁶`, has the BCG06
  geometric output with the ACTUAL original selected zero balls of `S.family`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- **Consumer: BCG06's geometric output for the original map of every stored supply**, with the
actual zero balls of the stored family (`E = F_∂`, `(u_b, v_b) = J_b ∘ E`, `ε∂ = 10⁻⁷`,
`c₃ = 10⁻⁶`). -/
theorem supply_original_boundaryGeometricOutput_BCG6K :
    BoundaryCollarPacket.BoundaryGeometricOutput_BCG6K S.packet.toBoundaryCollarPacket
      (chainBoundaryU_BCG6K S.boundaryOriginalMap) (chainBoundaryV_BCG6K S.boundaryOriginalMap)
      S.zeroBall_BCG6K := by
  obtain ⟨hU, hV⟩ :=
    S.packet.toBoundaryCollarPacket.chainBoundary_original_eq_BCG6K S.interiorMapW_BAUGA
  have eU : chainBoundaryU_BCG6K S.boundaryOriginalMap =
      S.packet.toBoundaryCollarPacket.originalBoundaryU_BCG6K := hU
  have eV : chainBoundaryV_BCG6K S.boundaryOriginalMap =
      S.packet.toBoundaryCollarPacket.originalBoundaryV_BCG6K := hV
  rw [eU, eV]
  exact S.boundaryGeometricOutput_supply_BCG6K
    (fun i => S.packet.toBoundaryCollarPacket.contMDiff_originalBoundaryU_BCG6K i)
    (εd := 1 / 10000000) (c₃ := 1 / 1000000) (by norm_num) (by norm_num) (by norm_num)
    (fun i => S.packet.toBoundaryCollarPacket.original_BI_BCG6K (by norm_num) i)
    (fun i => S.packet.toBoundaryCollarPacket.original_BFM_BCG6K i)
    (fun i => S.packet.toBoundaryCollarPacket.original_BD_BCG6K (by norm_num) i)

end BoundarySupplyCore

end DifferentialGeometry.Geometry.Collapse
