import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryHorizontalOBDe
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceFibresV2b
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageFaceDisjointOBDe

/-!
# Faces g3 `edge_faces` and g5 `region_boundary` on the rows over the produced stages

Lane O-BD1 (by S-BD2f, suffix `_OBDf`), group G11j. No circle-side input is used (in particular no
rim or corner fact, so there is no circularity with `exists_rims_OBDe`): the reduction of both
fields to "`x ∈ P_e ∩ ∂M₂ ⟹ f₂ x ∈ ∂C₂`" goes through the saturation of the horizontal face
`H_e = ∂M₂ ∩ X₂` (`horizontalFace_saturated_BG4`, a union of whole edge fibres) and the centre of
the whole disk (`dec.fibres.edge_fibre_OWF`: the rim is `{T = 4Δ}`, so the centre of the closed
cell has `T < 4Δ`):

* `exists_disk_below_OBDf`: every disk of the restricted edge bundle has a point with `T < level`;
* `frontier_of_proj_eq_OBDf`: a point of `∂M₂` in `X₂` puts its whole disk into `∂M₂`;
* `edgeSet_frontier_subset_disks_OBDf`: `P_e ∩ ∂M₂ ⊆ ⋃ disks over endpoints` (a point over an
  interior point of `C₂` with `T < level` is interior to `M₂`);
* `edge_faces_rows_OBDf` (g3), `horizontalDisks_eq_OBDf` (`horizontalDisks = H_e`),
  `region_boundary_rows_OBDf` (g5, from `geom.pieces`).
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

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

section EdgeFaces

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}
  (P : BoundaryStageGeometry74b zc) (R : StageCutRows74 P.stageGeometry P.cut)

include C in
/-- **Every disk of the restricted edge bundle has a point strictly below the level** (the centre
of the closed cell of the whole-fibre chart: the rim is exactly `{T = 4Δ}`). -/
theorem exists_disk_below_OBDf (c' : R.edge.Base) :
    ∃ z : R.edge.source, R.edge.proj z = c' ∧ R.edge.height z < R.edge.level := by
  have hy : P.ιedge c'.1 ∈ dec.bases.base 1 := P.edge_range ⟨c'.1, rfl⟩
  obtain ⟨ed, hed⟩ := dec.fibres.edge_fibre_OWF _ hy
  obtain ⟨q, hq⟩ : ∃ q : dec.bases.fibre 1 (P.ιedge c'.1), ed q = closedCellCenter 2 :=
    ⟨ed.symm (closedCellCenter 2), ed.apply_symm_apply _⟩
  have hqf : (q : W.Carrier) ∈ dec.bases.source 1 ∩
      C.toChain.stageMap 1 ⁻¹' {P.ιedge c'.1} := q.2
  have hT1 : C.toChain.heightRatio (q : W.Carrier) ≠ 4 * Δ := by
    intro hT
    have hmem : (q : W.Carrier) ∈ dec.bases.fibre 1 (P.ιedge c'.1) ∩
        {p | C.toChain.heightRatio p = 4 * Δ} := ⟨q.2, hT⟩
    rw [← hed] at hmem
    obtain ⟨q', hq', hq'q⟩ := hmem
    have hqq : q' = q := Subtype.ext hq'q
    rw [hqq] at hq'
    have h1 : ‖((ed q).1 : EuclideanSpace ℝ (Fin 2))‖ = 1 := hq'
    rw [hq] at h1
    simp [closedCellCenter] at h1
  have hq1 := hqf.1
  rw [dec.bases.parent.edgeParent_cut] at hq1
  have hp : (q : W.Carrier) ∈ P.edge.parent := by
    rw [← SetLike.mem_coe, P.edge_ident.parent_eq]
    exact hq1.1
  have hproj : P.edge.proj ⟨q, hp⟩ = c'.1 := by
    apply P.edge_ident.emb.injective
    rw [P.edge_ident.proj_eq ⟨q, hp⟩]
    exact hqf.2
  have hsrc : (q : W.Carrier) ∈ P.cut.edgeSource :=
    P.stageGeometry.edge.mem_restrictParent_of hp (by rw [hproj]; exact c'.2)
  refine ⟨⟨q, hsrc⟩, Subtype.ext hproj, ?_⟩
  change P.edge.height ⟨q, hp⟩ < P.edge.level
  rw [P.edge_height, P.edge_level]
  exact lt_of_le_of_ne hq1.2 hT1

include C in
/-- **A point of `∂M₂` in `X₂` puts the whole disk through it into `∂M₂`** (saturation of the
horizontal face). -/
theorem frontier_of_proj_eq_OBDf {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) {x z : R.edge.source} (hxT : R.edge.height x ≤ R.edge.level)
    (hzT : R.edge.height z ≤ R.edge.level) (hproj : R.edge.proj z = R.edge.proj x)
    (hx : (x : W.Carrier) ∈ frontier P.cut.M₂) : (z : W.Carrier) ∈ frontier P.cut.M₂ := by
  have hx1 : (x : W.Carrier) ∈ dec.bases.source 1 := C.mem_source_one_of_edge_OBDe P R x hxT
  have hz1 : (z : W.Carrier) ∈ dec.bases.source 1 := C.mem_source_one_of_edge_OBDe P R z hzT
  have hM2 : P.cut.M₂ = dec.slim.M₂ := (C.cut_M₂_M₃_eq_OBD P).1
  have hH : (x : W.Carrier) ∈ dec.slim.horizontalFace := by
    rw [hM2] at hx
    exact ⟨hx, hx1⟩
  have hf : C.toChain.stageMap 1 (z : W.Carrier) = C.toChain.stageMap 1 (x : W.Carrier) := by
    have hze : (z : W.Carrier) ∈ P.edge.parent := P.edge.restrictParent_le _ z.2
    have hxe : (x : W.Carrier) ∈ P.edge.parent := P.edge.restrictParent_le _ x.2
    rw [← P.edge_ident.proj_eq ⟨z, hze⟩, ← P.edge_ident.proj_eq ⟨x, hxe⟩]
    have : (R.edge.proj z).1 = (R.edge.proj x).1 := by rw [hproj]
    exact congrArg P.ιedge this
  have hfib : (z : W.Carrier) ∈ dec.bases.fibre 1 (C.toChain.stageMap 1 (x : W.Carrier)) :=
    ⟨hz1, hf⟩
  have hHz := C.horizontalFace_saturated_BG4 dec.fibres dec.zero hrd hrd4 hrdc hprem hθ dec.slim
    (x : W.Carrier) hH (z : W.Carrier) hfib
  rw [hM2]
  exact hHz.1

include C in
/-- **`P_e ∩ ∂M₂` lies in the disks over the endpoints of `C₂`**: a point of `P_e` over an interior
point of `C₂` is not in `∂M₂` (its whole disk would be in `∂M₂`, but the disk has a point with
`T < level` over an interior point of `C₂`, which is interior to `M₂`). -/
theorem edgeSet_frontier_subset_disks_OBDf {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (cov : CutCoverFacts74 P.stageGeometry P.cut) :
    ∀ x ∈ P.cut.edgeSet ∩ frontier P.cut.M₂, ∃ e : R.edge.EdgeEnd, x ∈ R.edge.disk e.1 := by
  rintro x ⟨hxE, hxfr⟩
  have hedge : R.edge.edgePiece = P.cut.edgeSet := P.cut.edgePiece_edgeBundle74 R.edgeFacts
  rw [← hedge] at hxE
  obtain ⟨z0, ⟨hz0c, hz0T⟩, rfl⟩ := hxE
  by_cases hfr : R.edge.proj z0 ∈ frontier R.edge.cbase
  · exact ⟨⟨_, hfr⟩, z0, ⟨rfl, hz0T⟩, rfl⟩
  · exfalso
    have hint : R.edge.proj z0 ∈ interior R.edge.cbase := by
      by_contra hni
      exact hfr ⟨subset_closure hz0c, hni⟩
    obtain ⟨z1, hz1p, hz1h⟩ := C.exists_disk_below_OBDf P R (R.edge.proj z0)
    have hO : IsOpen {u : R.edge.source | R.edge.proj u ∈ interior R.edge.cbase ∧
        R.edge.height u < R.edge.level} :=
      (isOpen_interior.preimage R.edge.proj.continuous).inter
        (isOpen_lt R.edge.height_smooth.continuous continuous_const)
    have hOpen : IsOpen (Subtype.val '' {u : R.edge.source | R.edge.proj u ∈ interior R.edge.cbase ∧
        R.edge.height u < R.edge.level}) :=
      R.edge.source.isOpen.isOpenMap_subtype_val _ hO
    have hsub : Subtype.val '' {u : R.edge.source | R.edge.proj u ∈ interior R.edge.cbase ∧
        R.edge.height u < R.edge.level} ⊆ P.cut.M₂ := by
      rintro _ ⟨u, ⟨hu1, hu2⟩, rfl⟩
      apply cov.edgeSet_subset_M₂
      rw [← hedge]
      exact ⟨u, ⟨interior_subset hu1, hu2.le⟩, rfl⟩
    have hz1int : (z1 : W.Carrier) ∈ interior P.cut.M₂ :=
      interior_maximal hsub hOpen ⟨z1, ⟨hz1p ▸ hint, hz1h⟩, rfl⟩
    have hz1fr := C.frontier_of_proj_eq_OBDf P R hrd hrd4 hrdc hprem hθ hz0T hz1h.le hz1p hxfr
    exact hz1fr.2 hz1int

end BoundaryGaf02ChainE

end EdgeFaces

end DifferentialGeometry.Geometry.Collapse
