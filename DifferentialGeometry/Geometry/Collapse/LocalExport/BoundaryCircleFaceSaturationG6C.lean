import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersZeroConfigG6C

/-!
# G6c: the faces of the circle base are unions of whole circle fibres (lane O-G6C, G2d)

On the actual v2 slot `f₁ = E`, and every horizontal face (zero face, cusp front, slim end fibre) is
defined through `E` (zero markers, `J_b(E)`, `f₃ = π₂ ∘ E` with `X₃ = f₃⁻¹(B₃)`), so it is saturated
by the whole fibres of `f₁`; the vertical face is saturated inside `M₂` (F1 nesting).

* `BoundaryGaf02ChainE.edgeFaceSet_iff_of_E_eq_G6C`: `E q = E p → (q ∈ face ℓ ↔ p ∈ face ℓ)`;
* `BoundaryGaf02ChainE.fibre_subset_circleFace_of_mem_G6C`: a whole circle fibre inside `M₂` that
  meets a face lies in it;
* `BoundaryGaf02ChainE.fibre_disjoint_faces_of_labels_empty_G6C`: with no label the whole fibre
  misses every face (the input of the interior configuration).
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

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

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
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

/-- **Horizontal faces are defined through `E`.** -/
theorem edgeFaceSet_iff_of_E_eq_G6C {C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj}
    {Bs : BoundaryGaf02BasesV2 C.toChain}
    {Kc : BoundaryCompactSlimChoiceV2 Bs} {ℓ : Kc.EdgeFaceLabel_BIFc} {p q : W.Carrier}
    (hE : C.toChain.E q = C.toChain.E p) :
    q ∈ Kc.edgeFaceSet_BIFc ℓ ↔ p ∈ Kc.edgeFaceSet_BIFc ℓ := by
  have hst : ∀ st, C.toChain.stageMap st q = C.toChain.stageMap st p := fun st => by
    change (actualSlotsV2_BAUGD S).stageProj st (C.toChain.E q) =
      (actualSlotsV2_BAUGD S).stageProj st (C.toChain.E p)
    rw [hE]
  rcases ℓ with k | i | ⟨j, e⟩
  · change (9 / 10 * S.zeroRadius_BAUGC k ≤ (C.toChain.E q (Sum.inl (S.zeroTag_BAUGC k))).snd ∧
        ((C.toChain.E q (Sum.inl (S.zeroTag_BAUGC k))).fst : ℝ²) 0 =
          2 / 5 * (C.toChain.E q (Sum.inl (S.zeroTag_BAUGC k))).snd) ↔
      (9 / 10 * S.zeroRadius_BAUGC k ≤ (C.toChain.E p (Sum.inl (S.zeroTag_BAUGC k))).snd ∧
        ((C.toChain.E p (Sum.inl (S.zeroTag_BAUGC k))).fst : ℝ²) 0 =
          2 / 5 * (C.toChain.E p (Sum.inl (S.zeroTag_BAUGC k))).snd)
    rw [hE]
  · change (9 / 10 ≤ (augmentedBoundaryCoord_BC7C i (C.toChain.E q)).2 ∧
        (augmentedBoundaryCoord_BC7C i (C.toChain.E q)).1 =
          40 * (augmentedBoundaryCoord_BC7C i (C.toChain.E q)).2) ↔
      (9 / 10 ≤ (augmentedBoundaryCoord_BC7C i (C.toChain.E p)).2 ∧
        (augmentedBoundaryCoord_BC7C i (C.toChain.E p)).1 =
          40 * (augmentedBoundaryCoord_BC7C i (C.toChain.E p)).2)
    rw [hE]
  · change q ∈ Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {_} ↔
      p ∈ Bs.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {_}
    rw [Bs.slim_source_eq]
    simp only [mem_inter_iff, mem_preimage, hst 2]

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **A whole circle fibre inside `M₂` meeting a face of the circle base lies in it.** -/
theorem fibre_subset_circleFace_of_mem_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    {Kc : BoundaryCompactSlimChoiceV2 Bs}
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hM : Bs.fibre 0 y ⊆ Kc.M₂) (f : CircleFaceLabel74 Kc) {p : W.Carrier}
    (hp : p ∈ Bs.fibre 0 y) (hpf : p ∈ circleFaceSet74 Kc f) :
    Bs.fibre 0 y ⊆ circleFaceSet74 Kc f := by
  rcases f with ℓ | u
  · intro q hq
    have hE : C.toChain.E q = C.toChain.E p := by
      rw [← C.toChain.stageMap_zero_eq_E_OF1, ← C.toChain.stageMap_zero_eq_E_OF1]
      exact (hq.2 : C.toChain.stageMap 0 q = y).trans (hp.2 : C.toChain.stageMap 0 p = y).symm
    exact (edgeFaceSet_iff_of_E_eq_G6C hE).mpr hpf
  · exact C.fibre_subset_verticalFace_G6C hM hp hpf

/-- **With no label, the whole fibre misses every face** (input of the interior configuration). -/
theorem fibre_disjoint_faces_of_labels_empty_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    {Kc : BoundaryCompactSlimChoiceV2 Bs}
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hM : Bs.fibre 0 y ⊆ Kc.M₂) (hL : circleLabelsAt_G6C Kc y = ∅) (f : CircleFaceLabel74 Kc) :
    Disjoint (Bs.fibre 0 y) (circleFaceSet74 Kc f) := by
  refine Set.disjoint_left.mpr fun p hp hpf => ?_
  have hf : f ∈ circleLabelsAt_G6C Kc y :=
    mem_circleLabelsAt_G6C.mpr (C.fibre_subset_circleFace_of_mem_G6C hM f hp hpf)
  rw [hL] at hf
  exact Finset.notMem_empty f hf

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
