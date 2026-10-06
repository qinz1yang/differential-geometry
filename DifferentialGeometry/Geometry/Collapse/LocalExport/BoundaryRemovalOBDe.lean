import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCutCoverOBD
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspBaseEquationOBD
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCuspKitOBDe

/-!
# The removal property `hKR` of the boundary cut (lane S-BD2e, suffix `_OBDe`), group G11e

Lane O-BD1 (by S-BD2e), hlift, cut facts `H`: the removal property of the cusp-aware kit,

`hKR : ∀ F : NeighbourFace zero cusp, neighbourSet F ∩ slimSet ⊆ relInt_{M₁} slimSet`

for the zero model faces AND the cusp fronts of the produced cut. It follows from the decomposition
alone (no slim pieces): a neighbour face lies in `∂M₁` (`geom.frontierM₁`: `∂M₁` is the union of the
zero faces and the cusp fronts), a point of `∂M₁ ∩ X₃` is mapped by `f₃` into the relative interior
of `K₃` in `B₃` (`dec.slim.faces_subset`), and `X₃ ∩ f₃⁻¹(D₃) = M₁ ∩ X₃` (F4d):

* `relInt_slimPiece_of_faces_OBDe` (generic): the topological core;
* `frontier_slim_relInt_OBDe`: `∂M₁ ∩ slimPiece ⊆ relInt_{M₁} slimPiece`;
* `hKR_OBDe`: the removal property on the zero / cusp exit `zc` of the produced stage geometry.
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

/-- **The topological core of `hKR`**: if `f x` is in the relative interior of `K` in the base `B`,
`f` is continuous, `Xs` is open, `f` maps `Xs` into `B` and `Xs ∩ f⁻¹ D = A ∩ Xs`, then `x ∈ Xs ∩ A`
lies in the interior, relative to `A`, of `Xs ∩ f⁻¹(K ∩ D)`. -/
theorem relInt_slimPiece_of_faces_OBDe {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) {Xs A : Set X} (hXs : IsOpen Xs) {Bs K D : Set Y}
    (hmap : ∀ y ∈ Xs, f y ∈ Bs) (hD : Xs ∩ f ⁻¹' D = A ∩ Xs) {x : X} (hx : x ∈ Xs)
    (hxA : x ∈ A)
    (hfx : f x ∈ Subtype.val '' interior (Subtype.val ⁻¹' K : Set Bs)) :
    x ∈ relInt A (Xs ∩ f ⁻¹' (K ∩ D)) := by
  obtain ⟨q, hq, hqx⟩ := hfx
  obtain ⟨t, hts, hto, hqt⟩ := mem_interior.1 hq
  obtain ⟨U, hU, hUt⟩ := isOpen_induced_iff.1 hto
  refine mem_relInt_iff_exists_open_JN74.2 ⟨hxA, Xs ∩ f ⁻¹' U, hXs.inter (hU.preimage hf),
    ⟨hx, ?_⟩, ?_⟩
  · rw [mem_preimage, ← hqx]
    have : q ∈ Subtype.val ⁻¹' U := by rw [hUt]; exact hqt
    exact this
  · rintro y ⟨⟨hyX, hyU⟩, hyA⟩
    have hyB : f y ∈ Bs := hmap y hyX
    have hyK : f y ∈ K := by
      have : (⟨f y, hyB⟩ : Bs) ∈ t := by rw [← hUt]; exact hyU
      exact hts this
    have hyD : f y ∈ D := by
      have : y ∈ Xs ∩ f ⁻¹' D := by rw [hD]; exact ⟨hyA, hyX⟩
      exact this.2
    exact ⟨hyX, hyK, hyD⟩

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

section Removal

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)
  {dec : BoundaryActualDecompositionV2b C.toChain} {zc : BoundaryZeroCuspExit74b C.toChain dec}

include C in
/-- **`∂M₁ ∩ slimPiece ⊆ relInt_{M₁} slimPiece`.** -/
theorem frontier_slim_relInt_OBDe (zc : BoundaryZeroCuspExit74b C.toChain dec) {x : W.Carrier}
    (hxf : x ∈ frontier C.toChain.M₁_BIFc) (hxs : x ∈ dec.slim.piece) :
    x ∈ relInt C.toChain.M₁_BIFc dec.slim.piece := by
  have hM1c : IsClosed C.toChain.M₁_BIFc := by
    rw [← C.regionM1_eq_OBD zc]
    exact isClosed_regionM1_GSAFE zc.zero zc.cusp
  have hxX : x ∈ dec.bases.source 2 := hxs.1
  have hfx := dec.slim.faces_subset ⟨x, ⟨hxf, hxX⟩, rfl⟩
  exact relInt_slimPiece_of_faces_OBDe (f := C.toChain.stageMap 2)
    (C.contMDiff_stageMap_OBD 2).continuous (dec.bases.isOpen_source 2 (by decide))
    (fun y hy => by rw [← dec.bases.image_eq 2]; exact ⟨y, hy, rfl⟩)
    (dec.zero.slimSource_inter_preimage_BIF) hxX (hM1c.frontier_subset hxf) hfx

include C in
/-- **The removal property `hKR` of the cusp-aware kit** for the zero / cusp exit `zc` of the
produced cut: every zero model face and every cusp front meets the slim set only in the relative
interior of the slim set inside `M₁`. -/
theorem hKR_OBDe (geom : BoundaryGeometricExports74b C.toChain dec)
    (P : BoundaryStageGeometry74b zc) :
    ∀ F : NeighbourFace P.stageGeometry.zero P.stageGeometry.cusp,
      neighbourSet F ∩ P.cut.slimSet ⊆
        relInt (regionM1 P.stageGeometry.zero P.stageGeometry.cusp) P.cut.slimSet := by
  intro F x ⟨hxF, hxs⟩
  have hM1 : regionM1 P.stageGeometry.zero P.stageGeometry.cusp = C.toChain.M₁_BIFc :=
    C.regionM1_eq_OBD zc
  have hS : P.cut.slimSet = dec.slim.piece := C.cut_slimSet_eq_OBD P
  rw [hM1, hS]
  rw [hS] at hxs
  refine C.frontier_slim_relInt_OBDe zc ?_ hxs
  rw [geom.frontierM₁]
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

end BoundaryGaf02ChainE

end Removal

end DifferentialGeometry.Geometry.Collapse
