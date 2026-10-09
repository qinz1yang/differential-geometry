import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryStageZeroConsumerOBD
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerDescentLocOBDe

/-!
# Fibre constancy of `T` and of the zero / cusp face functions on the circle fibres

Lane O-BD1 (by S-BD2e, suffix `_OBDe`), group G11d (hlift, corner descent, zero and cusp labels).
For ANY rows `R` over the produced stages:

* `circle_fibre_E_eq_OBDe`: two points of one circle fibre have the same `E` (the circle stage map
  is `E`, `stageMap_zero_eq_E_OBD`);
* `cornerT_fibreConst_OBDe`: `T − 4Δ` (`R.cornerT`) is constant on the circle fibres inside the edge
  source (`hconstT` of the corner descent and the vertical points of `local_faces`);
* `zero_ratio_localConst_OBDe`: the ratio of the zero piece `i` is a function of `E` on an open set
  around its face (`ratio_near`: `defFn = u/v − 2/5`, `u`, `v` coordinates of `E`);
* `cusp_fn_const_OBDe`: the cusp function is a function of `E` on its neighbourhood (`cusp_link`);
* `residual_localConst_nonNew_OBDe`: for every residual face that is NOT a new slim end there is an
  open `Ω ⊇ residualSet` on which the face function is constant on the circle fibres;
* `exists_cornerDescent_nonNew_OBDe`: `CornerDescent74 F G e` at every endpoint whose label is not a
  new slim end (the new ends need the end-coordinate clause of the slim exit).
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

section CornerConst

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}
  (P : BoundaryStageGeometry74b zc) (R : StageCutRows74 P.stageGeometry P.cut)

/-- **Two points of one circle fibre have the same `E`.** -/
theorem circle_fibre_E_eq_OBDe (x y : R.circle.domain)
    (hxy : R.circle.proj y = R.circle.proj x) :
    C.toChain.E (x : W.Carrier) = C.toChain.E (y : W.Carrier) := by
  have hx : (x : W.Carrier) ∈ R.circle.fibre (R.circle.proj x) := ⟨x, rfl, rfl⟩
  have hy : (y : W.Carrier) ∈ R.circle.fibre (R.circle.proj x) := ⟨y, hxy, rfl⟩
  have hset := C.circleFibre_set_OBD P R.circleFacts (R.circle.proj x)
  have hx' : (x : W.Carrier) ∈
      {y | C.toChain.stageMap 0 y = P.ιcircle (R.circle.proj x).1} := by
    rw [← hset]
    exact hx
  have hy' : (y : W.Carrier) ∈
      {y | C.toChain.stageMap 0 y = P.ιcircle (R.circle.proj x).1} := by
    rw [← hset]
    exact hy
  have h : C.toChain.stageMap 0 (x : W.Carrier) = C.toChain.stageMap 0 (y : W.Carrier) :=
    hx'.trans hy'.symm
  rwa [C.stageMap_zero_eq_E_OBD, C.stageMap_zero_eq_E_OBD] at h

/-- **`T − 4Δ` is constant on the circle fibres inside the edge source** (`hconstT`). -/
theorem cornerT_fibreConst_OBDe (x y : R.circle.domain) (hx : (x : W.Carrier) ∈ R.edge.source)
    (hy : (y : W.Carrier) ∈ R.edge.source) (hxy : R.circle.proj y = R.circle.proj x) :
    R.cornerT x = R.cornerT y := by
  have hxe : (x : W.Carrier) ∈ P.edge.parent := P.edge.restrictParent_le _ hx
  have hye : (y : W.Carrier) ∈ P.edge.parent := P.edge.restrictParent_le _ hy
  have hE := C.circle_fibre_E_eq_OBDe P R x y hxy
  have hT : C.toChain.heightRatio (x : W.Carrier) = C.toChain.heightRatio (y : W.Carrier) := by
    unfold BoundaryGaf02Chain.heightRatio BoundaryGaf02Chain.height BoundaryGaf02Chain.scale
    rw [hE]
  simp only [StageCutRows74.cornerT, hx, hy, ↓reduceDIte]
  have hhx := P.edge_height ⟨x, hxe⟩
  have hhy := P.edge_height ⟨y, hye⟩
  have hHx : P.edge.height ⟨x, hxe⟩ = P.edge.height ⟨y, hye⟩ := by rw [hhx, hhy, hT]
  exact sub_left_inj.2 hHx

include C in
/-- **The ratio of a zero piece is a function of `E` on an open set around its face.** -/
theorem zero_ratio_localConst_OBDe (i : Fin zc.zero.count) :
    ∃ Ω : Set W.Carrier, IsOpen Ω ∧ {x | zc.zero.ratio i x = 0} ⊆ Ω ∧
      ∀ x ∈ Ω, ∀ y ∈ Ω, C.toChain.E x = C.toChain.E y → zc.zero.ratio i x = zc.zero.ratio i y := by
  obtain ⟨σ, hσ⟩ := zc.zero_link
  obtain ⟨O, hO, hface, hnear⟩ := dec.zero.ratio_near (σ i)
  refine ⟨O, hO, ?_, ?_⟩
  · intro x hx
    apply hface
    rw [dec.zero.face_eq (σ i), mem_ofPred_eq]
    have h := (hσ i).2
    rw [mem_ofPred_eq] at hx
    rw [← h]
    exact hx
  · intro x hx y hy hE
    rw [(hσ i).2, (hnear x hx).2, (hnear y hy).2]
    unfold BoundaryGaf02Chain.zeroCoord_BIFc BoundaryGaf02Chain.zeroMarker_BIFc
    rw [hE]

include C in
/-- **The cusp function is a function of `E` on its neighbourhood.** -/
theorem cusp_fn_const_OBDe (b : Fin S.packet.cusp.count) {x y : W.Carrier}
    (hx : x ∈ (zc.cusp.near b : Set W.Carrier)) (hy : y ∈ (zc.cusp.near b : Set W.Carrier))
    (hE : C.toChain.E x = C.toChain.E y) : zc.cusp.cuspFn b x = zc.cusp.cuspFn b y := by
  rw [(zc.cusp_link b).2.2 x hx, (zc.cusp_link b).2.2 y hy]
  unfold chainBoundaryU_BCG6K chainBoundaryV_BCG6K
  rw [hE]

include C in
/-- **The face function of a residual face that is not a new slim end is constant on the circle
fibres inside an open set around the face.** -/
theorem residual_localConst_nonNew_OBDe (Fl : R.slimPieces.ResidualFace)
    (hFl : ∀ en : R.slimPieces.NewEnd, Fl ≠ .inr en) :
    ∃ Ω : Set W.Carrier, IsOpen Ω ∧ R.slimPieces.residualSet Fl ⊆ Ω ∧
      ∀ x y : R.circle.domain,
        (x : W.Carrier) ∈ (R.slimPieces.residualNear Fl : Set W.Carrier) ∩ Ω →
        (y : W.Carrier) ∈ (R.slimPieces.residualNear Fl : Set W.Carrier) ∩ Ω →
        R.circle.proj y = R.circle.proj x →
        R.slimPieces.residualFn Fl x = R.slimPieces.residualFn Fl y := by
  rcases Fl with ⟨F | F, hF⟩ | en
  · obtain ⟨Ω, hΩ, hsub, hconst⟩ := C.zero_ratio_localConst_OBDe (zc := zc) F.1
    refine ⟨Ω, hΩ, fun z hz => hsub ?_, fun x y hx hy hxy =>
      hconst x hx.2 y hy.2 (C.circle_fibre_E_eq_OBDe P R x y hxy)⟩
    exact R.slimPieces.residualFn_eq_zero_JN74 (.inl ⟨.inl F, hF⟩) hz
  · obtain ⟨b, Fm, hFm⟩ := F
    refine ⟨(zc.cusp.near b : Set W.Carrier), (zc.cusp.near b).isOpen, fun z hz => ?_,
      fun x y hx hy hxy => ?_⟩
    · exact R.slimPieces.residualSet_subset_residualNear_JN74 (.inl ⟨.inr ⟨b, Fm, hFm⟩, hF⟩) hz
    · exact C.cusp_fn_const_OBDe (zc := zc) b hx.2 hy.2
        (C.circle_fibre_E_eq_OBDe P R x y hxy)
  · exact absurd rfl (hFl en)

include C in
/-- **`CornerDescent74` at an endpoint whose label is not a new slim end.** -/
theorem exists_cornerDescent_nonNew_OBDe (F : JunctionFaceFacts74 P.stageGeometry P.cut R)
    (G : JunctionRimFacts74 P.stageGeometry P.cut R) (e : R.edge.EdgeEnd)
    (hlab : ∀ en : R.slimPieces.NewEnd, F.horizontal e ≠ .inr en) :
    Nonempty (CornerDescent74 F G e) := by
  obtain ⟨Ω, hΩ, hsub, hconst⟩ := C.residual_localConst_nonNew_OBDe P R (F.horizontal e) hlab
  refine exists_cornerDescent_loc_OBDe F G e Ω hΩ (fun x hx => hsub ?_)
    (fun x y hx hy hxy => C.cornerT_fibreConst_OBDe P R x y hx hy hxy) hconst
  obtain ⟨z, ⟨hz1, hz2⟩, hzx⟩ := hx
  exact F.horizontal_disk e ⟨z, ⟨hz1, hz2.le⟩, hzx⟩

end BoundaryGaf02ChainE

end CornerConst

end DifferentialGeometry.Geometry.Collapse
