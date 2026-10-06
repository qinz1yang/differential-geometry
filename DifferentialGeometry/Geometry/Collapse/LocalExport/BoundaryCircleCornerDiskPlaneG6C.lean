import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornerIndependenceG6CApplications
import DifferentialGeometry.Topology.Ehresmann.SlicePlaneG6C

/-!
# G6c corners: the tangent plane of the edge disk (lane O-G6C, G2i)

`BoundaryGaf02ChainE.exists_edgeDiskPlane_G6C`: at a point `p` of the edge source `X₂` there is a
plane `P ⊆ T_pW` (the tangent plane of the whole edge disk through `p`, from the edge chart
`WF.edge_chart`) on which `df₂` vanishes, and on which the differential of every function constant
on the edge disk vanishes. Consumer: `BoundaryGaf02ChainE.surjective_zeroDefFn_height_of_disk_G6C`
(corner independence at a rim point whose whole edge disk lies in a zero face).
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

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

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

/-- **The tangent plane of the edge disk.** -/
theorem exists_edgeDiskPlane_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) {p : W.Carrier} (hp : p ∈ Bs.source 1) :
    ∃ P : Submodule ℝ (TangentSpace W.model p), Module.finrank ℝ P = 2 ∧
      (∀ v ∈ P, mvfderiv W.model (C.toChain.stageMap 1) p v = 0) ∧
      ∀ G : W.Carrier → ℝ, MDifferentiableAt W.model 𝓘(ℝ, ℝ) G p →
        (∀ q ∈ Bs.fibre 1 (C.toChain.stageMap 1 p), G q = G p) →
        ∀ v ∈ P, mvfderiv W.model G p v = 0 := by
  have hy : C.toChain.stageMap 1 p ∈ Bs.base 1 := Bs.image_eq 1 ▸ mem_image_of_mem _ hp
  obtain ⟨σ, φ, O, h0, -, hσ, -, -, -, hφ, hr, hf, -⟩ := WF.edge_chart _ hy
  have hpr : p ∈ range φ := by
    rw [hr]
    exact ⟨hp, ⟨0, h0⟩⟩
  obtain ⟨⟨x₀, w₀⟩, rfl⟩ := hpr
  have hx₀ : x₀ = 0 := hσ.injective (by rw [← hf x₀ w₀, h0])
  subst hx₀
  have hφd : MDifferentiableAt ((𝓡 1).prod (𝓡∂ 2)) W.model φ (0, w₀) :=
    hφ.contMDiff.mdifferentiableAt (by simp)
  have hslice : ∀ w, φ (0, w) ∈ Bs.fibre 1 (C.toChain.stageMap 1 (φ (0, w₀))) := fun w => by
    have hmem : φ (0, w) ∈ range φ := mem_range_self _
    rw [hr] at hmem
    exact ⟨hmem.1, by rw [mem_preimage, mem_singleton_iff, hf, hf]⟩
  refine ⟨slicePlane_G6C (IF := 𝓡∂ 2) (I := W.model) φ 0 w₀, ?_, ?_, ?_⟩
  · rw [finrank_slicePlane_G6C hφ]
    exact finrank_euclideanSpace_fin
  · intro v hv
    have hf₂ : MDifferentiableAt W.model
        𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
        (C.toChain.stageMap 1) (φ (0, w₀)) :=
      (C.stageMap_contMDiff_BAUGD 1 _).mdifferentiableAt (by simp)
    have h := mfderiv_eq_zero_of_mem_slicePlane_G6C hφd hf₂ (fun w => by rw [hf, hf]) v hv
    have h' : mvfderiv W.model (C.toChain.stageMap 1) (φ (0, w₀)) v =
        mfderiv W.model 𝓘(ℝ, BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
          (C.toChain.stageMap 1) (φ (0, w₀)) v := rfl
    rw [h', h]
    rfl
  · intro G hG hconst v hv
    have h := mfderiv_eq_zero_of_mem_slicePlane_G6C hφd hG
      (fun w => hconst _ (hslice w)) v hv
    have h' : mvfderiv W.model G (φ (0, w₀)) v = mfderiv W.model 𝓘(ℝ, ℝ) G (φ (0, w₀)) v := rfl
    rw [h', h]
    rfl

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
