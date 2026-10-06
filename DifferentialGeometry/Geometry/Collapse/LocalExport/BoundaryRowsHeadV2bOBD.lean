import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroRowsV2bOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsOfExitsV2bOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspExitOBD

/-!
# The zero / cusp exit and the BD2 head of the boundary landing on v2b (lane O-BD2b)

Lane O-BD1 (by O-BD2b, suffix `_OBD`), group G3 (D74-16 BD2; draft 74 §4.3; review 76 D76-5).

* **`BoundaryGaf02ChainE.exists_zeroCuspExit74b_OBD C dec Q (E4b)`**: the zero / cusp rows of the
  boundary landing (`BoundaryZeroCuspExit74b C.toChain dec`) — the zero rows of
  `exists_zeroDomains_OBD` on `dec.zero` (ratio = `dec.zero.defFn` exactly) and the cusp rows of
  `exists_cuspExit_OBD` (tori with the packet's labels, cuspFn = `u_b − 40 v_b`).
* **`BoundaryGaf02ChainE.boundary_rows_of_actual_decomposition74b_OBD`**: the BD2 head
  `∃ Et, labels ∧ ∃ Rw, BoundaryRowsLink74b C.toChain dec Et Rw`, the zero / cusp exit produced
  here and the stage lift with the cut geometry over THAT exit as the remaining input `hlift`
  (stages over `W` identified with `dec.bases`, the cut choice identified with `dec.slim`, and the
  cut geometry `H`: the rows of the tree that do not yet exist on the boundary bases).
* **`boundary_strongCertificate_of_exits74b_OBD`** (§R final shape, review 73 §7.2 / D76-5):
  `∃ Et, labels ∧ ∃ Rw, BoundaryRowsLink74b ∧ Nonempty (StrongCertificate W Et)` with the strong
  certificate `exists_strongCertificate_of_rows_GFIN` on the SAME rows `Rw`; and its head form
  `BoundaryGaf02ChainE.boundary_strongCertificate_of_actual_decomposition74b_OBD`.
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

section Certificate

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

/-- **§R final shape on v2b** (review 73 §7.2, D76-5): the landing's rows and the strong
certificate of `exists_strongCertificate_of_rows_GFIN` on the SAME rows. -/
theorem boundary_strongCertificate_of_exits74b_OBD
    (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ) (dec : BoundaryActualDecompositionV2b C)
    (geom : BoundaryGeometricExports74b C dec) (X : BoundaryLandingExits74b C dec) :
    ∃ Et : BoundaryTori W S.packet.cusp.count,
      (∀ i, range (Et.torusMap i) = S.packet.cusp.component i) ∧
      ∃ Rw : FC39RowsV2 W Et, BoundaryRowsLink74b C dec Et Rw ∧
        Nonempty (StrongCertificate W Et) := by
  obtain ⟨Et, hEt, Rw, L⟩ := boundary_rows_of_actual_decomposition74b_of_exits_OBD C dec geom X
  exact ⟨Et, hEt, Rw, L, exists_strongCertificate_of_rows_GFIN Rw⟩

end Certificate

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The zero / cusp exit of the boundary landing** (BD2, zero and cusp halves): the zero rows of
the decomposition's actual zero domains (pieces `Ψ_k ∘ val ∘ param` of the selected cores `Q k`,
ratio `dec.zero.defFn` exactly) and the cusp rows of the SAME chain (tori with the packet's labels,
cuspFn = `u_b − 40 v_b`). Premises: E4b; data: the decomposition and the Z1 cores. -/
theorem exists_zeroCuspExit74b_OBD (dec : BoundaryActualDecompositionV2b C.toChain)
    (Q : ∀ k : S.ZeroIdx_BAUGC,
      SelectedSmoothCore74.{0, 0} {q : W.pieceInterior ⊤ | S.zeroRadial_BIFc k q ≤ 2 / 5})
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) : Nonempty (BoundaryZeroCuspExit74b C.toChain dec) := by
  obtain ⟨zero, σ, hz⟩ := dec.zero.exists_zeroDomains_OBD Q
  obtain ⟨Et, cc, hEt, hcc⟩ := C.exists_cuspExit_OBD hrd hrd4 hrdc hprem hθ
  exact ⟨⟨Et, hEt, zero, ⟨σ, fun k => ⟨(hz k).1, (hz k).2.1⟩⟩, cc, hcc⟩⟩

/-- **BD2 head on v2b** (D74-16 `boundary_rows_of_actual_decomposition74`, v2b revision): the zero
/ cusp exit is produced (`exists_zeroCuspExit74b_OBD`); the stage lift with the cut geometry over
that exit is the remaining input `hlift`. -/
theorem boundary_rows_of_actual_decomposition74b_OBD
    (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74b C.toChain dec)
    (Q : ∀ k : S.ZeroIdx_BAUGC,
      SelectedSmoothCore74.{0, 0} {q : W.pieceInterior ⊤ | S.zeroRadial_BIFc k q ≤ 2 / 5})
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    (hlift : ∀ zc : BoundaryZeroCuspExit74b C.toChain dec,
      ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc) :
    ∃ Et : BoundaryTori W S.packet.cusp.count,
      (∀ i, range (Et.torusMap i) = S.packet.cusp.component i) ∧
      ∃ Rw : FC39RowsV2 W Et, BoundaryRowsLink74b C.toChain dec Et Rw := by
  obtain ⟨zc⟩ := C.exists_zeroCuspExit74b_OBD dec Q hrd hrd4 hrdc hprem hθ
  obtain ⟨X, -⟩ := hlift zc
  exact boundary_rows_of_actual_decomposition74b_of_exits_OBD C.toChain dec geom X

/-- **§R final shape, head form**: the BD2 head followed by the strong certificate on the SAME
rows. -/
theorem boundary_strongCertificate_of_actual_decomposition74b_OBD
    (dec : BoundaryActualDecompositionV2b C.toChain)
    (geom : BoundaryGeometricExports74b C.toChain dec)
    (Q : ∀ k : S.ZeroIdx_BAUGC,
      SelectedSmoothCore74.{0, 0} {q : W.pieceInterior ⊤ | S.zeroRadial_BIFc k q ≤ 2 / 5})
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100)
    (hlift : ∀ zc : BoundaryZeroCuspExit74b C.toChain dec,
      ∃ X : BoundaryLandingExits74b C.toChain dec, X.zc = zc) :
    ∃ Et : BoundaryTori W S.packet.cusp.count,
      (∀ i, range (Et.torusMap i) = S.packet.cusp.component i) ∧
      ∃ Rw : FC39RowsV2 W Et, BoundaryRowsLink74b C.toChain dec Et Rw ∧
        Nonempty (StrongCertificate W Et) := by
  obtain ⟨Et, hEt, Rw, L⟩ :=
    C.boundary_rows_of_actual_decomposition74b_OBD dec geom Q hrd hrd4 hrdc hprem hθ hlift
  exact ⟨Et, hEt, Rw, L, exists_strongCertificate_of_rows_GFIN Rw⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
