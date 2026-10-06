import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRemovalOBDe

/-!
# `∂M₁` is the union of the neighbour faces (lane S-BD2e, suffix `_OBDe`), group G11h

Lane O-BD1 (by S-BD2e). For the zero / cusp exit `zc` of the produced cut, with
`geom.frontierM₁ : ∂M₁ = ⋃ zero faces ∪ ⋃ cusp fronts`:

* `neighbourSet_subset_frontier_OBDe`: every neighbour face (zero model face, cusp front) lies in
  `∂M₁`;
* `frontier_subset_neighbours_OBDe`: `∂M₁` lies in the union of the neighbour faces.
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

section NeighbourFrontier

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} (zc : BoundaryZeroCuspExit74b C.toChain dec)

include C in
/-- **Every neighbour face lies in `∂M₁`.** -/
theorem neighbourSet_subset_frontier_OBDe (geom : BoundaryGeometricExports74b C.toChain dec)
    (F : NeighbourFace zc.zero zc.cusp) :
    neighbourSet F ⊆ frontier (regionM1 zc.zero zc.cusp) := by
  rw [C.regionM1_eq_OBD zc, geom.frontierM₁]
  intro x hxF
  rcases F with ⟨i, Fm⟩ | ⟨b, Fb⟩
  · obtain ⟨σ, hσ⟩ := zc.zero_link
    obtain ⟨p, hp, rfl⟩ := hxF
    have hb : (zc.zero.piece i).map p ∈ pieceBoundary (zc.zero.piece i) := by
      refine ⟨p, ?_, rfl⟩
      obtain ⟨y, -, hm⟩ := Fm.2
      rw [hm] at hp
      exact connectedComponentIn_subset _ _ hp
    rw [zc.zero.boundary_eq i, mem_ofPred_eq] at hb
    refine Or.inl (mem_iUnion.2 ⟨σ i, ?_⟩)
    rw [dec.zero.face_eq (σ i), mem_ofPred_eq, ← (hσ i).2]
    exact hb
  · refine Or.inr (mem_iUnion.2 ⟨b, ?_⟩)
    have hfr : neighbourSet (cuspFrontFace_OBDe zc.zero zc.cusp b) = cuspFront_OBDe zc.cusp b :=
      neighbourSet_cuspFrontFace_OBDe zc.zero zc.cusp b
    obtain ⟨Fm, hFm⟩ := Fb
    subst hFm
    have hx' : x ∈ neighbourSet (cuspFrontFace_OBDe zc.zero zc.cusp b) := hxF
    rw [hfr] at hx'
    exact ((zc.cusp_link b).2.1) ▸ hx'

include C in
/-- **`∂M₁` lies in the union of the neighbour faces.** -/
theorem frontier_subset_neighbours_OBDe (geom : BoundaryGeometricExports74b C.toChain dec) :
    frontier (regionM1 zc.zero zc.cusp) ⊆ ⋃ F : NeighbourFace zc.zero zc.cusp, neighbourSet F := by
  rw [C.regionM1_eq_OBD zc, geom.frontierM₁]
  rintro x (hx | hx)
  · obtain ⟨k, hk⟩ := mem_iUnion.1 hx
    obtain ⟨σ, hσ⟩ := zc.zero_link
    obtain ⟨i, rfl⟩ := σ.surjective k
    have h0 : zc.zero.ratio i x = 0 := by
      rw [(hσ i).2]
      have := hk
      rw [dec.zero.face_eq (σ i), mem_ofPred_eq] at this
      exact this
    have hb : x ∈ pieceBoundary (zc.zero.piece i) := by
      rw [zc.zero.boundary_eq i, mem_ofPred_eq]
      exact h0
    obtain ⟨Fm, hFm⟩ := exists_zeroFace_of_pieceBoundary_OBDe zc.zero i hb
    exact mem_iUnion.2 ⟨.inl ⟨i, Fm⟩, hFm⟩
  · obtain ⟨b, hb⟩ := mem_iUnion.1 hx
    refine mem_iUnion.2 ⟨cuspFrontFace_OBDe zc.zero zc.cusp b, ?_⟩
    rw [neighbourSet_cuspFrontFace_OBDe]
    change x ∈ range fun t => (zc.cusp.piece b).map (zc.cusp.product b (t, iccEnd true))
    exact ((zc.cusp_link b).2.1).symm ▸ hb

end BoundaryGaf02ChainE

end NeighbourFrontier

end DifferentialGeometry.Geometry.Collapse
