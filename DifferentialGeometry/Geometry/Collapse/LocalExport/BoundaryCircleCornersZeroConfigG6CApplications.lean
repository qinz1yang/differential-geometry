import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersZeroConfigG6C

/-!
# Consumer of the pure zero-face configuration (lane O-G6C, G2c)

`BoundaryGaf02ChainE.circleBaseCornersV32_of_localDescription_nonZero_G6C`: the reduction
`circleBaseCornersV32_of_localDescription_G6C` with the local description required ONLY at the
boundary points whose whole fibre is not in a zero face off the vertical face (the pure zero-face
configuration is discharged by `zeroOnly_localData_G6C`).
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

/-- **The V32 corner record with the pure zero-face configuration discharged.** -/
theorem circleBaseCornersV32_of_localDescription_nonZero_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (Kc : BoundaryCompactSlimChoiceV2 Bs) (hrem : Kc.remainder ⊆ Bs.source 0)
    (hsat : Kc.remainder =
      Bs.source 0 ∩ C.toChain.stageMap 0 ⁻¹' (C.toChain.stageMap 0 '' Kc.remainder))
    (hRP : Kc.edgePiece ∩ Kc.remainder ⊆ Kc.verticalFace) (hPe : IsClosed Kc.edgePiece)
    (hloc : ∀ y ∈ C.toChain.stageMap 0 '' Kc.remainder,
      y ∉ relInterior_BIF (Bs.base 0) (C.toChain.stageMap 0 '' Kc.remainder) →
      (∀ k, Bs.fibre 0 y ⊆ C.toChain.actualZeroFace_BIFc k → Bs.fibre 0 y ⊆ Kc.verticalFace) →
      ∃ (U : Set W.Carrier) (O : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)))
        (φ : CircleFaceLabel74 Kc →
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) → ℝ),
        IsOpen U ∧ Bs.fibre 0 y ⊆ U ∧ IsOpen O ∧ y ∈ O ∧
        (∀ f ∈ circleLabelsAt_G6C Kc y, ContDiffOn ℝ ∞ (φ f) O ∧ φ f y = 0) ∧
        (∀ p ∈ Bs.source 0 ∩ U, p ∈ Kc.remainder ↔
          ∀ f ∈ circleLabelsAt_G6C Kc y, φ f (C.toChain.stageMap 0 p) ≤ 0) ∧
        (∀ f ∈ circleLabelsAt_G6C Kc y, ∀ p ∈ Kc.remainder ∩ U,
          p ∈ circleFaceSet74 Kc f ↔ φ f (C.toChain.stageMap 0 p) = 0) ∧
        (∀ p ∈ Bs.fibre 0 y, Surjective fun v : TangentSpace W.model p =>
          fun f : circleLabelsAt_G6C Kc y =>
            mvfderiv W.model (fun q => φ f (C.toChain.stageMap 0 q)) p v)) :
    CircleBaseCornersV32 Kc := by
  refine C.circleBaseCornersV32_of_localDescription_G6C WF Z hrd hrd4 hrdc hprem hθ Kc hrem hsat
    fun y hy hyr => ?_
  by_cases hz : ∃ k, Bs.fibre 0 y ⊆ C.toChain.actualZeroFace_BIFc k ∧
    ¬ Bs.fibre 0 y ⊆ Kc.verticalFace
  · obtain ⟨k, hk, hV⟩ := hz
    exact C.zeroOnly_localData_G6C Z hrd hrd4 hrdc hprem hθ Kc hrem hsat hRP hPe hy hk hV
  · exact hloc y hy hyr fun k hk => by
      by_contra hV
      exact hz ⟨k, hk, hV⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
