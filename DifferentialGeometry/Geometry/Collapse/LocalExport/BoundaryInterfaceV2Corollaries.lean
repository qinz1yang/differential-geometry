import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceSlimCutV2

/-!
# Boundary route interfaces v2: corollaries of the actual zero domains (lane BIFACEd, G3)

Text v3 (`docs/geometrization/chapter14/evidence/boundary/TargetsBoundary-v3.lean.txt`) row F4d
(`M₁_saturated_BAUGF`, "one line from `Z.face_saturated`", owner BIFACE) on the plain chain, and its
two consequences for BCF01 / G3 (the `S ⊆ M₁` input `hSM` of `relative_interior_removal`):

* `BoundaryActualZeroDomains_BIFc.M₁_saturated_BIF` (F4d): for `st ≠ 1`, `M₁ ∩ X_st` is the WHOLE
  `f_st`-preimage of its image in `X_st` (D69-4: false for arbitrary cores, true for the actual
  zero domains of the same chain by `face_saturated`);
* `BoundaryActualZeroDomains_BIFc.slimSource_inter_preimage_BIF`: `X₃ ∩ f₃⁻¹(D₃) = M₁ ∩ X₃`;
* `BoundaryActualZeroDomains_BIFc.slimPieceOf_subset_M₁_BIF`: for EVERY set `K` of the slim base,
  `S_K = X₃ ∩ f₃⁻¹(K ∩ D₃) ⊆ M₁` (in particular for every slim cut and for the arc form).

Consumer: `BoundaryGaf02Chain.emptyDecompositionV2_corollaries_BIF` (the three statements on the
empty-family decomposition of BIFACEc G1b, with `K = ∅` and the arc-form `K₃`).
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
    δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ} {Kj : ℕ}
  {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

namespace BoundaryActualZeroDomains_BIFc

variable {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ} {Bs : BoundaryGaf02BasesV2 C}
  (Z : BoundaryActualZeroDomains_BIFc C Bs)
include Z

/-- **F4d** (text v3, `M₁_saturated_BAUGF` on the plain chain): for `st ≠ 1`, `M₁ ∩ X_st` is the
whole `f_st`-preimage of its image in `X_st`. -/
theorem M₁_saturated_BIF (st : Fin 3) (hst : st ≠ 1) :
    C.M₁_BIFc ∩ Bs.source st =
      Bs.source st ∩ C.stageMap st ⁻¹' (C.stageMap st '' (C.M₁_BIFc ∩ Bs.source st)) := by
  ext q
  constructor
  · rintro ⟨hqM, hqX⟩
    exact ⟨hqX, q, ⟨hqM, hqX⟩, rfl⟩
  · rintro ⟨hqX, p, ⟨hpM, hpX⟩, hpq⟩
    exact ⟨Z.face_saturated st hst p hpX q hqX hpq.symm hpM, hqX⟩

/-- `X₃ ∩ f₃⁻¹(D₃) = M₁ ∩ X₃`. -/
theorem slimSource_inter_preimage_BIF :
    Bs.source 2 ∩ C.stageMap 2 ⁻¹' Bs.slimBaseDomain_BIFc = C.M₁_BIFc ∩ Bs.source 2 :=
  (Z.M₁_saturated_BIF 2 (by decide)).symm

/-- **The slim piece of ANY set of the slim base lies in `M₁`** (`hSM` of BCF01 / G3). -/
theorem slimPieceOf_subset_M₁_BIF
    (Kset : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))) :
    Bs.slimPieceOf_BIFc Kset ⊆ C.M₁_BIFc := by
  rintro q ⟨hqX, -, hqD⟩
  have hq : q ∈ Bs.source 2 ∩ C.stageMap 2 ⁻¹' Bs.slimBaseDomain_BIFc := ⟨hqX, hqD⟩
  rw [Z.slimSource_inter_preimage_BIF] at hq
  exact hq.1

end BoundaryActualZeroDomains_BIFc

namespace BoundaryGaf02Chain

variable {D : BoundaryAugmentedData S S.emptySlots_BIF}
  (C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ)
  (hc : ∀ st, S.stageCentres_BIF st = ∅) (hF : Continuous S.boundaryOriginalMap)

/-- **Consumer (G3)**: on the empty-family decomposition, F4d at the circle stage, the slim domain
identity, and `S ⊆ M₁` for the empty cut and for the arc-form `K₃`. -/
theorem emptyDecompositionV2_corollaries_BIF
    (hz0 : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      S.family.zero.centres = ∅) :
    C.M₁_BIFc ∩ (C.emptyDecompositionV2_BIFc hc hF hz0).bases.source 0 =
        (C.emptyDecompositionV2_BIFc hc hF hz0).bases.source 0 ∩ C.stageMap 0 ⁻¹'
          (C.stageMap 0 '' (C.M₁_BIFc ∩ (C.emptyDecompositionV2_BIFc hc hF hz0).bases.source 0)) ∧
      (C.emptyDecompositionV2_BIFc hc hF hz0).bases.source 2 ∩
          C.stageMap 2 ⁻¹' (C.emptyDecompositionV2_BIFc hc hF hz0).bases.slimBaseDomain_BIFc =
        C.M₁_BIFc ∩ (C.emptyDecompositionV2_BIFc hc hF hz0).bases.source 2 ∧
      (C.emptyDecompositionV2_BIFc hc hF hz0).bases.slimPieceOf_BIFc ∅ ⊆ C.M₁_BIFc ∧
      (C.emptyDecompositionV2_BIFc hc hF hz0).slim.piece ⊆ C.M₁_BIFc :=
  ⟨(C.emptyDecompositionV2_BIFc hc hF hz0).zero.M₁_saturated_BIF 0 (by decide),
    (C.emptyDecompositionV2_BIFc hc hF hz0).zero.slimSource_inter_preimage_BIF,
    (C.emptyDecompositionV2_BIFc hc hF hz0).zero.slimPieceOf_subset_M₁_BIF ∅,
    (C.emptyDecompositionV2_BIFc hc hF hz0).zero.slimPieceOf_subset_M₁_BIF
      (C.emptyDecompositionV2_BIFc hc hF hz0).slim.K₃⟩

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
