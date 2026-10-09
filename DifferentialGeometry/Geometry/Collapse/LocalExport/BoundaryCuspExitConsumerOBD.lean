import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspExitOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryDecompositionV2bOBD

/-!
# Consumer of the linked cusp exit (lane O-BD1)

`cuspClause_of_exit_OBD`: rows `Rw` over the produced tori whose cusp row IS the produced
`CuspCores` satisfy the `cusp` clause of `BoundaryRowsLink74b` (ranges = cores, internal ends =
fronts, `cuspFn = u_b − 40 v_b`) for ANY v2b decomposition `dec` of the chain, with the labels.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0
open DifferentialGeometry.Topology.HalfCollarHCOL

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

/-- **The cusp clause of the rows link from the produced cusp exit**: every rows family whose cusp
row is the produced `CuspCores` has the `cusp` clause of `BoundaryRowsLink74b` on the produced
tori, whose labels are the packet's components. Premises of E4b. -/
theorem cuspClause_of_exit_OBD {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ (Et : BoundaryTori W S.packet.cusp.count) (cc : CuspCores W Et),
      (∀ i, range (Et.torusMap i) = S.packet.cusp.component i) ∧
      ∀ Rw : FC39RowsV2 W Et, Rw.cusp = cc → ∀ i,
        range (Rw.cusp.piece i).map = C.toChain.cuspCore_BIF i ∧
        (range fun t => (Rw.cusp.piece i).map (Rw.cusp.product i (t, iccEnd true))) =
          C.toChain.cuspFront_BIF i ∧
        ∀ x ∈ Rw.cusp.near i, Rw.cusp.cuspFn i x =
          chainBoundaryU_BCG6K C.toChain.E i x - 40 * chainBoundaryV_BCG6K C.toChain.E i x := by
  obtain ⟨Et, cc, hlab, hcc⟩ := C.exists_cuspExit_OBD hrd hrd4 hrdc hprem hθ
  refine ⟨Et, cc, hlab, fun Rw hRw => ?_⟩
  rw [hRw]
  exact hcc

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
