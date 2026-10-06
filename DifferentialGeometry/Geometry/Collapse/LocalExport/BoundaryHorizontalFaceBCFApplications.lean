import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryHorizontalFaceBCF

/-!
# Consumer of P1 / P3: `A_Y = Y ∩ H_e` is a union of whole horizontal fibres (lane S-BCF134c)

`BoundaryGaf02ChainE.component_inter_horizontalFace_eq_BCF`: for a connected component `Y` of
`∂M₂`, `Y ∩ H_e` is the union of the WHOLE edge fibres over the horizontal face values `y` whose
fibre meets `Y` — the set-level content of BCF03.a ("`A_Y` is a finite disjoint union of whole
horizontal disks"; finiteness and the disk parametrizations are the remaining pieces P2, P5).
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
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **`A_Y` is a union of whole horizontal fibres** (set level): the part of a component `Y` of
`∂M₂` in the horizontal face is the union of the whole edge fibres over the horizontal face values
whose fibre meets `Y`. -/
theorem component_inter_horizontalFace_eq_BCF {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) (x : W.Carrier) :
    connectedComponentIn (frontier Kc.M₂) x ∩ Kc.horizontalFace =
      ⋃ y ∈ {y | y ∈ C.toChain.stageMap 1 '' Kc.horizontalFace ∧
        (connectedComponentIn (frontier Kc.M₂) x ∩ Bs.fibre 1 y).Nonempty}, Bs.fibre 1 y := by
  ext z
  constructor
  · rintro ⟨hzY, hzH⟩
    exact mem_iUnion₂.mpr ⟨C.toChain.stageMap 1 z, ⟨⟨z, hzH, rfl⟩, z, hzY, hzH.2, rfl⟩, hzH.2, rfl⟩
  · intro hz
    obtain ⟨y, ⟨hy, hmeet⟩, hzy⟩ := mem_iUnion₂.mp hz
    have hfull := C.component_inter_edgeFibre_BCF WF Z hrd hrd4 hrdc hprem hθ Kc er hy hmeet
    obtain ⟨p₀, hp₀, rfl⟩ := hy
    exact ⟨hfull.symm ▸ hzy |>.1, C.horizontalFace_saturated_BCF Z hrd hrd4 hrdc hprem hθ Kc er p₀
      hp₀ z hzy⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
