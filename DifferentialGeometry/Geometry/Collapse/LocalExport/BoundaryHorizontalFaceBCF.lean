import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspFrontComponentBCF

/-!
# BCF03 G7 part 1, first pieces (P1, P3): the horizontal face is a union of WHOLE edge fibres
(lane S-BCF134c, suffix `_BCF`; text v3.1 G7: "disks are `Y ∩` whole horizontal edge fibres")

On the arc form `Kc` with BCF02's relative edge restriction `er` (labelled descended face functions
`h_ℓ`), the horizontal face `H_e = ∂M₂ ∩ X₂` is exactly the set of points of `P_e = M₂ ∩ X₂` where
some `h_ℓ ∘ f₂` vanishes:

* `BoundaryGaf02ChainE.edgeFaceSet_inter_M₂_subset_frontier_BCF`: a point of `M₂` on a labelled
  face (zero face, cusp front, new slim end fibre) lies in `∂M₂` (F4c: zero faces / fronts lie in
  `∂M₁`; points of `M₂ ∩ ∂M₁` are not in `S`, G3; a slim end fibre in `M₂` lies in
  `S ∩ M₂ = ∂S \ ∂M₁`);
* `horizontalFace_eq_labelled_BCF`: `H_e = {p ∈ P_e | ∃ ℓ, h_ℓ (f₂ p) = 0}`;
* **`horizontalFace_saturated_BCF`** (P1): `H_e` is a union of whole edge fibres;
* `isPreconnected_edgeFibre_BCF` and **`edgeFibre_subset_component_BCF`** (P3): every edge fibre
  meeting `H_e` lies in `H_e` and in ONE connected component of `∂M₂`.
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

/-- The closed cell is preconnected (convexity). -/
theorem closedCell_preconnectedSpace_BCF (n : ℕ) : PreconnectedSpace (ClosedCell n) := by
  have hconv : Convex ℝ ({x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ 1} : Set _) := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 : ℝ))
  exact Subtype.preconnectedSpace hconv.isPreconnected

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
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **A point of `M₂` on a labelled edge face lies in `∂M₂`** (zero face, cusp front or new slim end
fibre; numerical premises of F4c). -/
theorem edgeFaceSet_inter_M₂_subset_frontier_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) (ℓ : Kc.EdgeFaceLabel_BIFc)
    {p : W.Carrier} (hpM : p ∈ Kc.M₂) (hpℓ : p ∈ Kc.edgeFaceSet_BIFc ℓ) : p ∈ frontier Kc.M₂ := by
  have hF4c := C.frontier_M₁_BGR Z hrd hrd4 hrdc hprem hθ
  obtain ⟨hG1', hG2', -⟩ := bcf01_faces_BCF01 Z Kc.slimCut_BIFc
  have hG1 : Kc.piece ∩ Kc.M₂ = frontier Kc.piece \ frontier C.toChain.M₁_BIFc := hG1'
  have hG2 : frontier Kc.M₂ = (frontier C.toChain.M₁_BIFc \ Kc.piece) ∪
      (frontier Kc.piece \ frontier C.toChain.M₁_BIFc) := hG2'
  have hM₁ : p ∈ C.toChain.M₁_BIFc := hpM.1
  -- a point of `M₂` on `∂M₁` is not in `S`, hence in `∂M₂`
  have hbd : p ∈ frontier C.toChain.M₁_BIFc → p ∈ frontier Kc.M₂ := fun hpf => by
    have hpS : p ∉ Kc.piece := fun hS => (hG1.subset ⟨hS, hpM⟩).2 hpf
    rw [hG2]
    exact Or.inl ⟨hpf, hpS⟩
  rcases ℓ with k | i | ⟨j, e⟩
  · exact hbd (hF4c ▸ Or.inl (mem_iUnion.mpr ⟨k, hpℓ⟩))
  · exact hbd (hF4c ▸ Or.inr (mem_iUnion.mpr ⟨i, hpℓ⟩))
  · have hpX : p ∈ Bs.source 2 := hpℓ.1
    have hpy : C.toChain.stageMap 2 p = Kc.arc j (BoundaryCompactSlimChoiceV2.arcEnd_BIFc e) :=
      hpℓ.2
    have hend : BoundaryCompactSlimChoiceV2.arcEnd_BIFc e ∈ Icc (0 : ℝ) 1 := by
      cases e <;> simp [BoundaryCompactSlimChoiceV2.arcEnd_BIFc]
    have hyK : C.toChain.stageMap 2 p ∈ Kc.K₃ := hpy ▸ mem_iUnion.mpr ⟨j, _, hend, rfl⟩
    have hpS : p ∈ Kc.piece := ⟨hpX, hyK, p, ⟨hM₁, hpX⟩, rfl⟩
    have hp1 : p ∈ frontier Kc.piece \ frontier C.toChain.M₁_BIFc := hG1.subset ⟨hpS, hpM⟩
    rw [hG2]
    exact Or.inr hp1

/-- **The horizontal face is the labelled zero set** (BCF02's `face_complete` / `face_label` with
the previous lemma): `H_e = ∂M₂ ∩ X₂ = {p ∈ P_e | ∃ ℓ, h_ℓ (f₂ p) = 0}`. -/
theorem horizontalFace_eq_labelled_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) :
    Kc.horizontalFace = {p | p ∈ Kc.M₂ ∩ Bs.source 1 ∧
      ∃ ℓ, er.faceFun ℓ (C.toChain.stageMap 1 p) = 0} := by
  have hM₂c : IsClosed Kc.M₂ := isClosed_sdiff_relInterior_BCF C.toChain.isClosed_M₁_BCF Kc.piece
  ext p
  constructor
  · intro hp
    exact ⟨⟨hM₂c.frontier_subset hp.1, hp.2⟩, er.face_complete p hp⟩
  · rintro ⟨hpM, ℓ, hℓ⟩
    exact ⟨C.edgeFaceSet_inter_M₂_subset_frontier_BCF Z hrd hrd4 hrdc hprem hθ Kc ℓ hpM.1
      (er.face_label ℓ p hpM hℓ), hpM.2⟩

/-- **P1: the horizontal face is a union of WHOLE edge fibres**: every point of the edge fibre
through a horizontal face point is a horizontal face point (saturation of `M₂ ∩ X₂`, BCF02). -/
theorem horizontalFace_saturated_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) :
    ∀ p ∈ Kc.horizontalFace, ∀ q ∈ Bs.fibre 1 (C.toChain.stageMap 1 p), q ∈ Kc.horizontalFace := by
  intro p hp q hq
  rw [C.horizontalFace_eq_labelled_BCF Z hrd hrd4 hrdc hprem hθ Kc er] at hp ⊢
  obtain ⟨⟨hpM, hpX⟩, ℓ, hℓ⟩ := hp
  have hqf : C.toChain.stageMap 1 q = C.toChain.stageMap 1 p := hq.2
  have hqsat : q ∈ Bs.source 1 ∩ C.toChain.stageMap 1 ⁻¹'
      (C.toChain.stageMap 1 '' (Kc.M₂ ∩ Bs.source 1)) := ⟨hq.1, p, ⟨hpM, hpX⟩, hqf.symm⟩
  rw [← er.saturated] at hqsat
  exact ⟨hqsat, ℓ, by rw [hqf]; exact hℓ⟩

end BoundaryGaf02ChainE

namespace BoundaryWholeFiberSpecV2

variable {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}

/-- **Whole edge fibres are preconnected** (`≃ₜ ClosedCell 2`). -/
theorem isPreconnected_edgeFibre_BCF (WF : BoundaryWholeFiberSpecV2 C Bs)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Bs.base 1) :
    IsPreconnected (Bs.fibre 1 y) := by
  obtain ⟨ed, -⟩ := WF.edge_fibre_BIFc y hy
  have := closedCell_preconnectedSpace_BCF 2
  have hrange : Bs.fibre 1 y = range (fun z : ClosedCell 2 => ((ed.symm z : Bs.fibre 1 y) :
      W.Carrier)) := by
    ext q
    constructor
    · intro hq
      exact ⟨ed ⟨q, hq⟩, by simp⟩
    · rintro ⟨z, rfl⟩
      exact (ed.symm z).2
  rw [hrange]
  exact isPreconnected_range (continuous_subtype_val.comp ed.symm.continuous)

end BoundaryWholeFiberSpecV2

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **P3: an edge fibre meeting the horizontal face lies in it and in ONE connected component of
`∂M₂`.** -/
theorem edgeFibre_subset_component_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) {p : W.Carrier} (hp : p ∈ Kc.horizontalFace) :
    Bs.fibre 1 (C.toChain.stageMap 1 p) ⊆ Kc.horizontalFace ∧
      Bs.fibre 1 (C.toChain.stageMap 1 p) ⊆ connectedComponentIn (frontier Kc.M₂) p := by
  have hy : C.toChain.stageMap 1 p ∈ Bs.base 1 := Bs.image_eq 1 ▸ mem_image_of_mem _ hp.2
  have hsat := C.horizontalFace_saturated_BCF Z hrd hrd4 hrdc hprem hθ Kc er p hp
  refine ⟨fun q hq => hsat q hq, ?_⟩
  have hpf : p ∈ Bs.fibre 1 (C.toChain.stageMap 1 p) := ⟨hp.2, rfl⟩
  exact (WF.isPreconnected_edgeFibre_BCF hy).subset_connectedComponentIn hpf
    fun q hq => (hsat q hq).1

/-- **P3, component form** (the shape of the frozen `val '' P.disk i = Y ∩ fibre`): if the connected
component `Y` of `∂M₂` at `x` meets the edge fibre over a horizontal face value `y`, then `Y`
contains the WHOLE fibre. -/
theorem component_inter_edgeFibre_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) {x : W.Carrier}
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)}
    (hy : y ∈ C.toChain.stageMap 1 '' Kc.horizontalFace)
    (hmeet : (connectedComponentIn (frontier Kc.M₂) x ∩ Bs.fibre 1 y).Nonempty) :
    connectedComponentIn (frontier Kc.M₂) x ∩ Bs.fibre 1 y = Bs.fibre 1 y := by
  obtain ⟨p₀, hp₀, rfl⟩ := hy
  obtain ⟨q, hqY, hqf⟩ := hmeet
  refine Subset.antisymm inter_subset_right fun z hz => ⟨?_, hz⟩
  have hsat := C.horizontalFace_saturated_BCF Z hrd hrd4 hrdc hprem hθ Kc er p₀ hp₀ q hqf
  have hqf' : C.toChain.stageMap 1 q = C.toChain.stageMap 1 p₀ := hqf.2
  have hzq : z ∈ Bs.fibre 1 (C.toChain.stageMap 1 q) := by rw [hqf']; exact hz
  have hzc := (C.edgeFibre_subset_component_BCF WF Z hrd hrd4 hrdc hprem hθ Kc er hsat).2 hzq
  rw [← connectedComponentIn_eq hqY] at hzc
  exact hzc

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
