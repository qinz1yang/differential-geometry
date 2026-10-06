import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRowsOfExitsLND
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryExitsKernelLND

/-!
# The boundary landing exits project to the plain-data kernel

Lane S-LANDING (by S-LANDING2, suffix `_LND`), G6. `BoundaryLandingExits74 C dec` (S-LANDING G3b,
v2 decomposition) is a record over a boundary chain; `BoundaryExitsKernel_LND`
(`Closure/BoundaryExitsKernelLND`) is its chain-free mirror on plain data, inhabited on the S³
singleton and the S² × S¹ loop (`Closure/BoundaryExitsKernelApplicationsLND`, `n = 0`). This file
proves that the boundary exits ARE instances of the kernel, field for field:

* `BoundaryActualDecompositionV2.exitsData_LND C dec`: the plain data of `(C, dec)`;
* `BoundaryLandingExits74.toKernel_LND X geom : BoundaryExitsKernel_LND dec.exitsData_LND …`
  (`geom` supplies the saturation of `R_c`, the `pieces` clause of G6);
* `BoundaryLandingExits74.rows_link_LND`: the kernel head on the boundary exits (the J1 rows
  satisfy the plain form of `BoundaryRowsLink`), through the projection.

The same text transfers verbatim to the v2b decomposition (O-BD2, `BoundaryLandingExits74b`): see
`BoundaryExitsKernelBridgeV2bLND.lean`.
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

section Bridge

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

/-- **The plain data of the chain `C` and the decomposition `dec`** (v2). -/
def BoundaryActualDecompositionV2.exitsData_LND (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut
    bder κ) (dec : BoundaryActualDecompositionV2 C) :
    BoundaryExitsData_LND W (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
      S.packet.cusp.count S.ZeroIdx_BAUGC where
  q0 := C.stageMap 0
  q1 := C.stageMap 1
  q2 := C.stageMap 2
  src0 := dec.bases.source 0
  src1 := dec.bases.source 1
  src2 := dec.bases.source 2
  eParent := dec.bases.edgeParent
  base0 := dec.bases.base 0
  base1 := dec.bases.base 1
  height := C.heightRatio
  lvl := 4 * Δ
  Dset := dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc
  slimPiece := dec.slim.piece
  edgePiece := dec.slim.edgePiece
  remainder := dec.slim.remainder
  M₁ := C.M₁_BIFc
  M₂ := dec.slim.M₂
  zdom := C.actualZeroDomain_BIFc
  zdef := dec.zero.defFn
  cuspCore := C.cuspCore_BIF
  cuspFront := C.cuspFront_BIF
  cuspFn := fun i x => chainBoundaryU_BCG6K C.E i x - 40 * chainBoundaryV_BCG6K C.E i x

/-- **`BoundaryLandingExits74` is an instance of the boundary exits kernel.** -/
def BoundaryLandingExits74.toKernel_LND {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    {dec : BoundaryActualDecompositionV2 C} (X : BoundaryLandingExits74 C dec)
    (geom : BoundaryGeometricExports74 C dec) :
    BoundaryExitsKernel_LND (dec.exitsData_LND C) S.packet.cusp.component where
  Et := X.zc.Et
  labels_eq := X.zc.labels
  zero := X.zc.zero
  zero_link := X.zc.zero_link
  cusp := X.zc.cusp
  cusp_link := X.zc.cusp_link
  slim := X.stages.slim
  edge := X.stages.edge
  circle := X.stages.circle
  ιslim := X.stages.ιslim
  ιedge := X.stages.ιedge
  ιcircle := X.stages.ιcircle
  slim_ident := X.stages.slim_ident
  edge_ident := X.stages.edge_ident
  circle_ident := X.stages.circle_ident
  edge_range := X.stages.edge_range
  circle_range := X.stages.circle_range
  edge_height := X.stages.edge_height
  edge_level := X.stages.edge_level
  cut := X.stages.cut
  cut_D₃ := X.stages.cut_D₃
  cut_C₂ := X.stages.cut_C₂
  cut_C₁ := X.stages.cut_C₁
  comp := X.stages.comp
  comp_eq := X.stages.comp_eq
  edgePiece_eq := X.stages.edgePiece_eq
  geometry := X.geometry
  src1_eq := dec.bases.parent.edgeParent_cut
  slimPiece_eq := rfl
  M₁_eq := rfl
  M₂_eq := rfl
  remainder_eq := rfl
  remainder_sat := geom.pieces.2.2.2.2.2.2.1

/-- **Kernel head on the boundary exits**: the J1 rows of the stage geometry satisfy the plain form
of `BoundaryRowsLink`, through the projection to the kernel. -/
theorem BoundaryLandingExits74.rows_link_LND {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
    {dec : BoundaryActualDecompositionV2 C} (X : BoundaryLandingExits74 C dec)
    (geom : BoundaryGeometricExports74 C dec) :
    ∃ Rw : FC39RowsV2 W X.zc.Et,
      (∃ σ : Fin Rw.zero.count ≃ S.ZeroIdx_BAUGC, ∀ k,
        range (Rw.zero.piece k).map = C.actualZeroDomain_BIFc (σ k) ∧
          Rw.zero.ratio k = dec.zero.defFn (σ k)) ∧
      (∀ i, range (Rw.cusp.piece i).map = C.cuspCore_BIF i ∧
        (range fun t => (Rw.cusp.piece i).map (Rw.cusp.product i (t, iccEnd true))) =
          C.cuspFront_BIF i ∧ ∀ x ∈ Rw.cusp.near i,
          Rw.cusp.cuspFn i x =
            chainBoundaryU_BCG6K C.E i x - 40 * chainBoundaryV_BCG6K C.E i x) ∧
      (Rw.slim.union = dec.slim.piece ∧
        ∃ σ : Fin Rw.slim.count ≃ ActualComponent (dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc),
          ∀ j, range (Rw.slim.piece j).map = dec.bases.source 2 ∩ C.stageMap 2 ⁻¹' (σ j).1) ∧
      regionM1 Rw.zero Rw.cusp = C.M₁_BIFc ∧ regionM2 Rw.slim = dec.slim.M₂ ∧
        regionM3 Rw.slim Rw.edge = dec.slim.remainder := by
  obtain ⟨Rw, hz, hc, hs, -, -, h1, h2, h3⟩ := (X.toKernel_LND geom).rows_link
  exact ⟨Rw, hz, hc, hs, h1, h2, h3⟩

end Bridge

end DifferentialGeometry.Geometry.Collapse
