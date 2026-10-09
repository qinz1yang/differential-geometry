import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPiecesCornersBC2

/-!
# BCF02 rim clauses, G1: strict face inequalities give ambient interior points (lane S-RIM81)

External review 81 (b): on the v2 objects `(Bs, Kc, er)` a point of the edge source `X₂` at which
every labelled face function `h_ℓ ∘ f₂` is strictly positive lies in the AMBIENT interior of `M₂`.

* `BoundaryRelativeEdgeRestrictionV2.mem_M₂_iff_faces_nonneg_RM1`: on `X₂`, `p ∈ M₂` iff all
  `h_ℓ (f₂ p) ≥ 0` (`saturated` and `base_eq`);
* **`BoundaryRelativeEdgeRestrictionV2.mem_interior_M₂_of_faces_pos_RM1`**: a boundary point of
  `M₂` in `X₂` carries a vanishing label (`face_complete`), so strict positivity forces an interior
  point.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
    Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}

namespace BoundaryRelativeEdgeRestrictionV2

variable {Kc : BoundaryCompactSlimChoiceV2 Bs} (er : BoundaryRelativeEdgeRestrictionV2 Kc)

/-- **Sublevel description of `M₂` on `X₂`**: for `p ∈ X₂`, `p ∈ M₂` iff every labelled face
function `h_ℓ ∘ f₂` is nonnegative at `p` (`saturated`, `base_eq`). -/
theorem mem_M₂_iff_faces_nonneg_RM1 {p : W.Carrier} (hp : p ∈ Bs.source 1) :
    p ∈ Kc.M₂ ↔ ∀ ℓ, 0 ≤ er.faceFun ℓ (C.stageMap 1 p) := by
  have hb : C.stageMap 1 p ∈ Bs.base 1 := Bs.image_eq 1 ▸ mem_image_of_mem _ hp
  constructor
  · intro hM
    have h2 : C.stageMap 1 p ∈ C.stageMap 1 '' (Kc.M₂ ∩ Bs.source 1) :=
      mem_image_of_mem _ ⟨hM, hp⟩
    rw [er.base_eq] at h2
    exact h2.2
  · intro hnn
    have h2 : C.stageMap 1 p ∈ C.stageMap 1 '' (Kc.M₂ ∩ Bs.source 1) := by
      rw [er.base_eq]
      exact ⟨hb, hnn⟩
    have h3 : p ∈ Bs.source 1 ∩ C.stageMap 1 ⁻¹' (C.stageMap 1 '' (Kc.M₂ ∩ Bs.source 1)) :=
      ⟨hp, h2⟩
    rw [← er.saturated] at h3
    exact h3.1

/-- **G1 (review 81 (b))**: a point of `X₂` where all labelled face functions are strictly positive
is an AMBIENT interior point of `M₂`. A frontier point of `M₂` in `X₂` has a vanishing label by
`face_complete`. -/
theorem mem_interior_M₂_of_faces_pos_RM1 {p : W.Carrier} (hp : p ∈ Bs.source 1)
    (hpos : ∀ ℓ, 0 < er.faceFun ℓ (C.stageMap 1 p)) : p ∈ interior Kc.M₂ := by
  have hM : p ∈ Kc.M₂ := (er.mem_M₂_iff_faces_nonneg_RM1 hp).mpr fun ℓ => (hpos ℓ).le
  by_contra hint
  obtain ⟨ℓ, hℓ⟩ := er.face_complete p ⟨⟨subset_closure hM, hint⟩, hp⟩
  exact (hpos ℓ).ne' hℓ

end BoundaryRelativeEdgeRestrictionV2

end DifferentialGeometry.Geometry.Collapse
