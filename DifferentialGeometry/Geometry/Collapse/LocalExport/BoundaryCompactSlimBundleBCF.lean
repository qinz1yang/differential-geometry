import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCompactSlimFacesBCF

/-!
# BCF01.a: `S` is the proper whole-fibre restriction of the slim bundle over `K₃ ∩ D₃`
(lane B-BCF134)

Blueprint `master207B.tex`, BCF01 (B:9657–9658): "The first is the actual proper whole `S²` or `T²`
bundle over `K₃ ∩ D₃`." On the interface (`S = X₃ ∩ f₃⁻¹(K₃ ∩ D₃)`, `f₃ = C.stageMap 2`):

* `BoundaryCompactSlimChoice.piece_eq_iUnion_fibre_BCF`: `S = ⋃_{y ∈ K₃ ∩ D₃} X₃ ∩ f₃⁻¹{y}` — `S` is
  the union of the WHOLE slim fibres over its base;
* `stageMap_image_piece_BCF`: `f₃(S) = K₃ ∩ D₃` — the base of `S` is exactly `K₃ ∩ D₃`;
* `isCompact_piece_inter_preimage_BCF`: `f₃|S` is proper over `K₃ ∩ D₃`;
* `fibre_subset_piece_BCF`: every whole fibre over a point of `K₃ ∩ D₃` lies in `S`.

The fibre TYPE (`S²` or `T²`) is the whole-fibre layer's (BIFACEc v2, D69-1); it is not restated
here.
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
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}

namespace BoundaryCompactSlimChoice

variable {Bs : BoundaryGaf02Bases C} {ZC : BoundaryInitialCoresSpec C}
  (Kc : BoundaryCompactSlimChoice Bs ZC)

/-- **`S` is the union of the whole slim fibres over `K₃ ∩ D₃`**. -/
theorem piece_eq_iUnion_fibre_BCF :
    Kc.piece = ⋃ y ∈ Kc.K₃ ∩ Bs.slimBaseDomain_BIF ZC, Bs.fibre 2 y := by
  ext p
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hpX, hpy⟩
    exact ⟨_, hpy, hpX, rfl⟩
  · rintro ⟨y, hy, hpX, hpy⟩
    have hpy' : C.stageMap 2 p = y := mem_singleton_iff.mp hpy
    exact ⟨hpX, show C.stageMap 2 p ∈ _ by rw [hpy']; exact hy⟩

/-- Every whole fibre over a point of `K₃ ∩ D₃` lies in `S`. -/
theorem fibre_subset_piece_BCF {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ Kc.K₃ ∩ Bs.slimBaseDomain_BIF ZC) : Bs.fibre 2 y ⊆ Kc.piece := by
  rw [Kc.piece_eq_iUnion_fibre_BCF]
  exact subset_biUnion_of_mem (u := fun y => Bs.fibre 2 y) hy

/-- **The base of `S` is exactly `K₃ ∩ D₃`**: `f₃(S) = K₃ ∩ D₃`. -/
theorem stageMap_image_piece_BCF :
    C.stageMap 2 '' Kc.piece = Kc.K₃ ∩ Bs.slimBaseDomain_BIF ZC := by
  refine Subset.antisymm (image_subset_iff.mpr fun p hp => hp.2) fun y hy => ?_
  obtain ⟨p, ⟨-, hpX⟩, rfl⟩ := hy.2
  exact ⟨p, ⟨hpX, hy⟩, rfl⟩

/-- **`f₃|S` is proper over `K₃ ∩ D₃`**. -/
theorem isCompact_piece_inter_preimage_BCF
    {L : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))}
    (hL : L ⊆ Kc.K₃ ∩ Bs.slimBaseDomain_BIF ZC) (hLc : IsCompact L) :
    IsCompact (Kc.piece ∩ C.stageMap 2 ⁻¹' L) := by
  have h : Kc.piece ∩ C.stageMap 2 ⁻¹' L = Bs.source 2 ∩ C.stageMap 2 ⁻¹' L := by
    ext p
    exact ⟨fun hp => ⟨hp.1.1, hp.2⟩, fun hp => ⟨⟨hp.1, hL hp.2⟩, hp.2⟩⟩
  rw [h]
  exact Bs.proper 2 L (hL.trans (inter_subset_left.trans Kc.K₃_subset_base_BCF)) hLc

end BoundaryCompactSlimChoice

end DifferentialGeometry.Geometry.Collapse
