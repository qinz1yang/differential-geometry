import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceDecomposition
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreDefs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.NoncollapseLocalization

/-!
# BCG07 F4b: the remaining piece `M₁` stays `35` away from `∂W` (lane B-BCG-ROWS)

Blueprint `master207B.tex`, BCG07 (B:9471–9500): `M₁ = M \ int_M(Z ∪ C)` is contained in
`{d(p, ∂M) ≥ 35}`. Proof: a point at distance `< 35` from `∂W` is `35`-close to a point of some
boundary component `∂_b W` (`NearlyCuspidalBoundary.covers`), hence in the OPEN neighbourhood
`N₃₅(∂_b W) ⊆ C_b` (BCG06.a's global definition), hence in `int(Z ∪ C)` — for ANY family of zero
domains `Z`.

* `BoundaryCollarPacket.isOpen_cuspNbhd35_BGR`: `N₃₅(∂_b W)` is open.
* `BoundaryCollarPacket.mem_cuspNbhd35_of_distanceToBoundary_lt_BGR`.
* **`BoundaryGaf02Chain.M₁_subset_buffer_BGR`** (frozen F4b `M₁_subset_buffer_BAUGF`, on the
  removed region `W \ int(Z ∪ C_∂)` with an arbitrary `Z`; the v2 actual zero domains are
  `Z = ⋃_k C.actualZeroDomain_BIFc k`); **`BoundaryInitialCoresSpec.M₁_subset_buffer_BGR`** (the v1
  interface's `ZC.M₁`).
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

namespace BoundaryCollarPacket

variable {W : CompactCarrier.{0}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ} (P : BoundaryCollarPacket W g K A w₀ ε)

/-- `N₃₅(∂_b W)` is open (a union of open Riemannian balls). -/
theorem isOpen_cuspNbhd35_BGR (b : Fin P.cusp.count) : IsOpen (P.cuspNbhd35_BCG6K b) := by
  have h : P.cuspNbhd35_BCG6K b = ⋃ y ∈ P.cusp.component b, riemannianBallOf g y 35 := by
    ext x
    simp only [cuspNbhd35_BCG6K, mem_iUnion, riemannianBallOf, exists_prop]
    rfl
  rw [h]
  exact isOpen_biUnion fun y _ => isOpen_riemannianBallOf g y 35

/-- A point at distance `< 35` from `∂W` lies in `N₃₅(∂_b W)` for some boundary component `b`. -/
theorem mem_cuspNbhd35_of_distanceToBoundary_lt_BGR {p : W.Carrier}
    (hp : distanceToBoundary W g p < ENNReal.ofReal 35) :
    ∃ b : Fin P.cusp.count, p ∈ P.cuspNbhd35_BCG6K b := by
  obtain ⟨q, hq⟩ := iInf_lt_iff.mp hp
  have hqb : (q : W.Carrier) ∈ ⋃ i, P.cusp.component i := by
    rw [P.cusp.covers]
    exact q.2
  obtain ⟨b, hb⟩ := mem_iUnion.mp hqb
  refine ⟨b, q, hb, ?_⟩
  rw [riemannianEDistOf_comm]
  exact hq

end BoundaryCollarPacket

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

namespace BoundaryGaf02Chain

variable (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)

/-- **BCG07 F4b on the chain**: for ANY zero-domain set `Z`, the removed region
`W \ int(Z ∪ C_∂)` lies in `{D ≥ 35}` (every point at distance `< 35` from `∂W` is in the open
`N₃₅(∂_b W) ⊆ C_b`). -/
theorem M₁_subset_buffer_BGR (Z : Set W.Carrier) :
    (interior (Z ∪ C.cuspCores_BIF))ᶜ ⊆
      {p | ENNReal.ofReal 35 ≤ distanceToBoundary W g p} := by
  intro p hp
  by_contra hlt
  obtain ⟨i, hi⟩ := S.packet.toBoundaryCollarPacket.mem_cuspNbhd35_of_distanceToBoundary_lt_BGR
    (not_le.mp hlt)
  refine hp (interior_maximal ?_ (S.packet.toBoundaryCollarPacket.isOpen_cuspNbhd35_BGR i) hi)
  intro x hx
  exact Or.inr (mem_iUnion.mpr ⟨i, Or.inl hx⟩)

end BoundaryGaf02Chain

/-- **BCG07 F4b** (frozen `M₁_subset_buffer_BAUGF`) on the v1 interface: `M₁ ⊆ {D ≥ 35}`. -/
theorem BoundaryInitialCoresSpec.M₁_subset_buffer_BGR
    {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} (ZC : BoundaryInitialCoresSpec C) :
    ZC.M₁ ⊆ {p | ENNReal.ofReal 35 ≤ distanceToBoundary W g p} :=
  C.M₁_subset_buffer_BGR ZC.union

end DifferentialGeometry.Geometry.Collapse
