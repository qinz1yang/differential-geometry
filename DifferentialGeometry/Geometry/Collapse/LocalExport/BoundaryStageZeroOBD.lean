import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRimCoreOBD

/-!
# The circle stage map is `E` (lane S-BD2c)

Lane O-BD1 (by S-BD2c, suffix `_OBD`), group G11c (hlift, junction primitives): the actual stage
tags are nested (`Q₃ ⊆ Q₂ ⊆ Q₁ = all`, `stageTagsV2_BAUGD`), so on the enhanced chain the circle
stage map is `f₀ = π_all ∘ E = E`, and every function of `E` (in particular `T = A/s`) is constant
on the fibres of `f₀`:

* `stageMap_zero_eq_E_OBD`: `C.stageMap 0 = C.E`;
* `heightRatio_fibreConst_OBD`: `f₀ p = f₀ q → T p = T q` (the fibre constancy of `T` needed by the
  corner descent and the vertical points of `local_faces`).
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


section Stage0

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The circle stage map is `E`** (the stage-`0` tags are all tags). -/
theorem stageMap_zero_eq_E_OBD (p : W.Carrier) : C.toChain.stageMap 0 p = C.toChain.E p := by
  have e0 : S.stageTagsV2_BAUGD 0 = Finset.univ := rfl
  have h0 : (actualSlotsV2_BAUGD S).stageTagsAug 0 = Finset.univ := by
    ext t
    change t ∈ (S.stageTagsV2_BAUGD 0).disjSum Finset.univ ↔ _
    rw [e0]
    rcases t with t | t <;> simp
  ext i
  change blockRestrict ((actualSlotsV2_BAUGD S).stageTagsAug 0) (C.toChain.E p) i = _
  rw [blockRestrict_apply, h0]
  simp

/-- **`T = A/s` is constant on the fibres of the circle stage map.** -/
theorem heightRatio_fibreConst_OBD {p q : W.Carrier}
    (h : C.toChain.stageMap 0 p = C.toChain.stageMap 0 q) :
    C.toChain.heightRatio p = C.toChain.heightRatio q := by
  rw [C.stageMap_zero_eq_E_OBD, C.stageMap_zero_eq_E_OBD] at h
  unfold BoundaryGaf02Chain.heightRatio BoundaryGaf02Chain.height BoundaryGaf02Chain.scale
  rw [h]

end BoundaryGaf02ChainE

end Stage0

end DifferentialGeometry.Geometry.Collapse
