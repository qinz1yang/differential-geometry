import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceFibresV2b
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryChainBasesSplit
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimFibreEFE

/-!
# BCG07 F1, conjunct 2: a rim point in `X₁` makes the rim ONE whole circle fibre (lane O-F1, G2)

Boundary twin of `Gaf02ChainEJA.edp06_rim_eq_whole_fibre_EFE` (lane S-EDP-FDC2 G5; blueprint
EDP06, B:7092–7133). On the actual v2 slot `actualSlotsV2_BAUGD S` the stage-`0` projection is the
identity (`stageProj_zero_V2_BAUGD`), so `f₁ = π₀ ∘ E = E` and the NESTING `(f₂, T) = G ∘ f₁` is
`f₁ q = f₁ p ⟹ E q = E p ⟹ f₂ q = f₂ p ∧ T q = T p` (no rank-2 argument).

* `BoundaryGaf02Chain.stageMap_zero_eq_E_OF1`: `f₁ = E` on the actual v2 slot;
* `BoundaryGaf02Chain.edgeData_eq_of_stageMap_zero_eq_OF1`: the nesting `f₁ q = f₁ p ⟹
  f₂ q = f₂ p ∧ T q = T p`;
* `BoundaryWholeFiberSpecV2b.circleFibre_subset_rim_OF1`: for `p ∈ X₁` on the rim of the whole
  edge disk over `y`, the whole circle fibre `Bs.fibre 0 (f₁ p)` lies in the rim
  `Bs.fibre 1 y ∩ {T = 4Δ}`;
* **`BoundaryWholeFiberSpecV2b.rim_eq_circleFibre_of_mem_source_OF1`**: and it is EQUAL to the rim
  (an embedded circle inside the boundary circle of an embedded disk fills it,
  `circle_range_eq_boundary_EFE`);
* **`BoundaryWholeFiberSpecV2b.diskRim_of_rim_subset_source_OF1`**: the F1 / `diskRim` shape
  (`TargetsBoundary-v3.1` l.388, `BoundaryGeometricExports74.diskRim`) from conjunct 1 (`rim ⊆ X₁`).
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
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {D : BoundaryAugmentedData S (actualSlotsV2_BAUGD S)} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

namespace BoundaryGaf02Chain

variable (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)

/-- On the actual v2 slot the circle stage map is `E` (`π₀ = id`). -/
theorem stageMap_zero_eq_E_OF1 (p : W.Carrier) : C.stageMap 0 p = C.E p :=
  stageProj_zero_V2_BAUGD S (C.E p)

/-- **The nesting `(f₂, T) = G ∘ f₁`** on the actual v2 slot: `f₁ q = f₁ p` gives `f₂ q = f₂ p`
and `T q = T p` (both are functions of `E = f₁`). -/
theorem edgeData_eq_of_stageMap_zero_eq_OF1 {p q : W.Carrier}
    (h : C.stageMap 0 q = C.stageMap 0 p) :
    C.stageMap 1 q = C.stageMap 1 p ∧ C.heightRatio q = C.heightRatio p := by
  have hE : C.E q = C.E p := by
    rw [← C.stageMap_zero_eq_E_OF1, ← C.stageMap_zero_eq_E_OF1]
    exact h
  refine ⟨?_, ?_⟩
  · change (actualSlotsV2_BAUGD S).stageProj 1 (C.E q) =
      (actualSlotsV2_BAUGD S).stageProj 1 (C.E p)
    rw [hE]
  · change S.heightCoord_BIF (C.E q) / S.scaleMarker_BIF (C.E q) =
      S.heightCoord_BIF (C.E p) / S.scaleMarker_BIF (C.E p)
    rw [hE]

end BoundaryGaf02Chain

namespace BoundaryWholeFiberSpecV2b

variable {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}
  (WF : BoundaryWholeFiberSpecV2b C Bs)
include WF

omit WF in
/-- **The whole circle fibre through a rim point of `X₁` lies in the rim**: for `p ∈ X₁` with
`f₂ p = y ∈ B₂` and `T p = 4Δ`, every `q` with `q ∈ X₁`, `f₁ q = f₁ p` lies in
`X₂ ∩ f₂⁻¹{y} ∩ {T = 4Δ}`. -/
theorem circleFibre_subset_rim_OF1
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Bs.base 1)
    {p : W.Carrier} (hp : p ∈ Bs.fibre 1 y) (hT : C.heightRatio p = 4 * Δ) :
    Bs.fibre 0 (C.stageMap 0 p) ⊆ Bs.fibre 1 y ∩ {q | C.heightRatio q = 4 * Δ} := by
  intro q hq
  have hpy : C.stageMap 1 p = y := hp.2
  have hqp : C.stageMap 0 q = C.stageMap 0 p := hq.2
  obtain ⟨h1, h2⟩ := C.edgeData_eq_of_stageMap_zero_eq_OF1 hqp
  have hqy : C.stageMap 1 q = y := h1.trans hpy
  have hqT : C.heightRatio q = 4 * Δ := h2.trans hT
  refine ⟨⟨?_, hqy⟩, hqT⟩
  rw [Bs.edge_source_eq]
  exact ⟨by rw [mem_preimage, hqy]; exact hy, le_of_eq hqT⟩

/-- **EDP06 on the boundary: the rim is ONE whole circle fibre** (given a rim point in `X₁`):
for `p ∈ X₁` on the rim of the whole edge disk over `y ∈ B₂` (`f₂ p = y`, `T p = 4Δ`), the rim
`Bs.fibre 1 y ∩ {T = 4Δ}` IS the whole circle fibre `Bs.fibre 0 (f₁ p)`. -/
theorem rim_eq_circleFibre_of_mem_source_OF1
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Bs.base 1)
    {p : W.Carrier} (hp : p ∈ Bs.fibre 1 y) (hT : C.heightRatio p = 4 * Δ)
    (h0 : p ∈ Bs.source 0) :
    Bs.fibre 1 y ∩ {q | C.heightRatio q = 4 * Δ} = Bs.fibre 0 (C.stageMap 0 p) := by
  have hb0 : C.stageMap 0 p ∈ Bs.base 0 := by
    rw [← Bs.image_eq 0]
    exact mem_image_of_mem _ h0
  obtain ⟨ec⟩ := WF.circle_fibre_OWF _ hb0
  obtain ⟨ed, hed⟩ := WF.edge_fibre_OWF y hy
  let f : Circle → W.Carrier := fun z => (ec.symm z).val
  let d : CellBoundary 2 → W.Carrier := fun x => (ed.symm (cellBoundaryInclusion 2 x)).val
  have hf : IsEmbedding f := IsEmbedding.subtypeVal.comp ec.symm.isEmbedding
  have hd : IsEmbedding d := IsEmbedding.subtypeVal.comp
    (ed.symm.isEmbedding.comp (cellBoundaryInclusion_isEmbedding_EFE 2))
  have hrf : range f = Bs.fibre 0 (C.stageMap 0 p) := by
    ext q
    constructor
    · rintro ⟨z, rfl⟩
      exact (ec.symm z).2
    · intro hq
      exact ⟨ec ⟨q, hq⟩, by simp [f]⟩
  have hrd : range d = Bs.fibre 1 y ∩ {q | C.heightRatio q = 4 * Δ} := by
    rw [← hed]
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨ed.symm (cellBoundaryInclusion 2 x), ?_, rfl⟩
      change ‖(ed (ed.symm (cellBoundaryInclusion 2 x))).1‖ = 1
      rw [Homeomorph.apply_symm_apply]
      exact x.2
    · rintro ⟨u, hu, rfl⟩
      refine ⟨⟨(ed u).1, hu⟩, ?_⟩
      change (ed.symm ⟨(ed u).1, _⟩).val = u.val
      have : (⟨(ed u).1, le_of_eq hu⟩ : ClosedCell 2) = ed u := rfl
      rw [this, Homeomorph.symm_apply_apply]
  have hsub : range f ⊆ range d := by
    rw [hrf, hrd]
    exact circleFibre_subset_rim_OF1 hy hp hT
  rw [← hrd, ← hrf]
  exact (circle_range_eq_boundary_EFE hf hd hsub).symm

/-- **F1 (`diskRim` shape) from conjunct 1**: if the rim of every whole edge disk lies in `X₁`,
then every rim is ONE whole circle fibre of the same final map (`TargetsBoundary-v3.1` l.388,
`BoundaryGeometricExports74.diskRim`). -/
theorem diskRim_of_rim_subset_source_OF1
    (hrim : ∀ y ∈ Bs.base 1, ∀ p ∈ Bs.fibre 1 y, C.heightRatio p = 4 * Δ → p ∈ Bs.source 0) :
    ∀ y ∈ Bs.base 1, ∀ p ∈ Bs.fibre 1 y, C.heightRatio p = 4 * Δ →
      p ∈ Bs.source 0 ∧
        Bs.fibre 1 y ∩ {q | C.heightRatio q = 4 * Δ} = Bs.fibre 0 (C.stageMap 0 p) :=
  fun y hy p hp hT => ⟨hrim y hy p hp hT,
    WF.rim_eq_circleFibre_of_mem_source_OF1 hy hp hT (hrim y hy p hp hT)⟩

end BoundaryWholeFiberSpecV2b

end DifferentialGeometry.Geometry.Collapse
