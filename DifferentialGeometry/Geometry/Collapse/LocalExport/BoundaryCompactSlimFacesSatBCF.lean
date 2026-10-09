import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCompactSlimFacesBCF
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceCoresSat

/-!
# BCF01 (G3) on the saturated cores: `S ⊆ M₁`, `S ∩ M₂ = ∂S \ ∂M₁`, disjoint interiors
(lane B-BCF134)

Blueprint `master207B.tex`, BCF01 (B:9642–9716), frozen target G3 of
`docs/geometrization/chapter14/evidence/boundary/TargetsBoundary.lean.txt` (T:390–395) with the
lead-approved statement change (13:4x) `ZC : BoundaryInitialCoresSpec → BoundaryInitialCoresSpecSat`
(the plain structure has a counterexample, see `LE/BoundaryInterfaceCoresSat.lean`). On
`Z : BoundaryInitialCoresSpecSat C Bs` and
`Kc : BoundaryCompactSlimChoice Bs Z.toBoundaryInitialCoresSpec`:

* `BoundaryCompactSlimChoice.piece_subset_M₁_BCF01`: `S ⊆ M₁` (the premise `hSM` of the ZSP05
  kernel `relative_interior_removal`), from the saturation of `M₁ ∩ X₃`;
* `frontier_piece_diff_subset_BCF01` and `piece_inter_M₂_eq_BCF01`: the first conjunct of G3,
  `S ∩ M₂ = ∂S \ ∂M₁`, in full;
* `frontier_M₂_subset_BCF`, `frontier_M₁_diff_subset_BCF`, `disjoint_faces_BCF` (the interface
  pack) give the rest of G3 except the inclusion `∂S \ ∂M₁ ⊆ ∂M₂`, which needs the regularity
  `cl(int S) = S` (openness of `f₃|X₃` and regularity of `K₃ ∩ D₃` in the one-manifold `B₃`: the
  shared ZSP04 / `K₃` kernel);
* `disjoint_interior_union_piece_BCF01`, `disjoint_interior_piece_M₂_BCF01`,
  `disjoint_interior_union_M₂_BCF01`: the pieces `Z ∪ C_∂`, `S`, `M₂` have disjoint interiors.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
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
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02Bases C}

namespace BoundaryCompactSlimChoice

variable {Z : BoundaryInitialCoresSpecSat C Bs}
  (Kc : BoundaryCompactSlimChoice Bs Z.toBoundaryInitialCoresSpec)

/-- **`S ⊆ M₁`** (ZSP05's `hSM`): a point of `S` shares its `f₃`-fibre with a point of `M₁ ∩ X₃`,
and `M₁ ∩ X₃` is saturated. -/
theorem piece_subset_M₁_BCF01 : Kc.piece ⊆ Z.M₁ := by
  rintro x ⟨hxX, -, p, ⟨hpM, hpX⟩, hpx⟩
  exact Z.mem_M₁_of_stageMap_eq_BCF (st := 2) (by decide) hpM hpX hxX hpx.symm

/-- **G3, first conjunct, `⊇`**: `∂S \ ∂M₁ ⊆ S ∩ M₂`. -/
theorem frontier_piece_diff_subset_BCF01 :
    frontier Kc.piece \ frontier Z.M₁ ⊆ Kc.piece ∩ Kc.M₂ := by
  rintro x ⟨hxf, hxf₁⟩
  rw [Kc.isClosed_piece_BCF.frontier_eq] at hxf
  have hxM₁ : x ∈ Z.M₁ := Kc.piece_subset_M₁_BCF01 hxf.1
  have hxint₁ : x ∈ interior Z.M₁ := by
    by_contra h
    rw [Z.isClosed_M₁_BCF.frontier_eq] at hxf₁
    exact hxf₁ ⟨hxM₁, h⟩
  refine ⟨hxf.1, hxM₁, fun hxrel => ?_⟩
  obtain ⟨-, O, hO, hxO, hOS⟩ := mem_relInterior_iff_BCF.mp hxrel
  apply hxf.2
  rw [mem_interior]
  exact ⟨O ∩ interior Z.M₁, fun y hy => hOS ⟨hy.1, interior_subset hy.2⟩,
    hO.inter isOpen_interior, hxO, hxint₁⟩

/-- **G3, first conjunct** (BCF01.b, `S ∩ M₂ = ∂S \ ∂M₁`), on the saturated cores. -/
theorem piece_inter_M₂_eq_BCF01 : Kc.piece ∩ Kc.M₂ = frontier Kc.piece \ frontier Z.M₁ :=
  Subset.antisymm Kc.piece_inter_M₂_subset_BCF Kc.frontier_piece_diff_subset_BCF01

/-- **Disjoint interiors, `Z ∪ C_∂` and `S`**. -/
theorem disjoint_interior_union_piece_BCF01 :
    Disjoint (interior (Z.union ∪ C.cuspCores_BIF)) (interior Kc.piece) :=
  Set.disjoint_left.mpr fun _ hx hxS => Kc.piece_subset_M₁_BCF01 (interior_subset hxS) hx

end BoundaryCompactSlimChoice

namespace BoundaryCompactSlimChoice

variable {ZC : BoundaryInitialCoresSpec C} (Kc : BoundaryCompactSlimChoice Bs ZC)

/-- **Disjoint interiors, `S` and `M₂`** (no saturation needed). -/
theorem disjoint_interior_piece_M₂_BCF01 : Disjoint (interior Kc.piece) (interior Kc.M₂) := by
  refine Set.disjoint_left.mpr fun x hxS hxM₂ => (interior_subset hxM₂).2 ?_
  exact mem_relInterior_iff_BCF.mpr ⟨(interior_subset hxM₂).1, interior Kc.piece,
    isOpen_interior, hxS, fun _ hy => interior_subset hy.1⟩

/-- **Disjoint interiors, `Z ∪ C_∂` and `M₂`** (no saturation needed). -/
theorem disjoint_interior_union_M₂_BCF01 :
    Disjoint (interior (ZC.union ∪ C.cuspCores_BIF)) (interior Kc.M₂) :=
  Set.disjoint_left.mpr fun _ hx hxM₂ => (interior_subset hxM₂).1 hx

end BoundaryCompactSlimChoice

end DifferentialGeometry.Geometry.Collapse
