import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryDiskRimFibreOF1
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRimSourceZeroOF1
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceDecompositionV2

/-!
# BCG07 F1 `wholeDiskBoundary_eq_wholeCircleFiber` on the enhanced boundary chain (lane O-F1, G3)

Composition of conjunct 1 (`BoundaryGaf02ChainE.rim_mem_source_zero_OF1`, G1: the rim of `X₂` lies
in `X₁`) and conjunct 2 (`BoundaryWholeFiberSpecV2b.rim_eq_circleFibre_of_mem_source_OF1`, G2: a
rim point in `X₁` makes the rim ONE whole circle fibre of the same final map):

* **`BoundaryGaf02ChainE.wholeDiskBoundary_eq_wholeCircleFiber_OF1`**: F1 on any v2 BASES exit
  `Bs` with a whole-fibre layer v2b (`TargetsBoundary-v3.1` l.388 shape);
* `BoundaryGaf02ChainE.wholeDiskBoundary_eq_wholeCircleFiber_v2_OF1`: the same with the frozen
  v2 layer `BoundaryWholeFiberSpecV2` (through `toV2b_OWF`); the frozen target
  `wholeDiskBoundary_eq_wholeCircleFiber_BAUGF` verbatim up to the numerical premises;
* `BoundaryGaf02ChainE.diskRim_v2_OF1`: the field `diskRim` of `BoundaryGeometricExports74`
  (decomposition v2); on O-BD1's decomposition v2b `dec` the field `diskRim` of
  `BoundaryGeometricExports74b` is `C.wholeDiskBoundary_eq_wholeCircleFiber_OF1 … dec.fibres`.

Numerical premises (parameters only): `3βc ≤ β 2 < 1`, `0 ≤ γ ≤ 3/4`, `c₃ < 10⁻⁵`,
`C_ρΛΔ < 10⁻⁶`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

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

namespace BoundaryGaf02ChainE

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}
  (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **BCG07 F1 (`wholeDiskBoundary_eq_wholeCircleFiber`) on the v2b layer**: the rim of every whole
edge disk lies in `X₁` and is ONE whole circle fibre `Bs.fibre 0 (f₁ p)` of the SAME final map. -/
theorem wholeDiskBoundary_eq_wholeCircleFiber_OF1 (h3βc : 3 * βc ≤ β 2) (hβ2 : β 2 < 1)
    (hγ : 0 ≤ γ) (hγ34 : γ ≤ 3 / 4) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    {Bs : BoundaryGaf02BasesV2 C.toChain} (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) :
    ∀ y ∈ Bs.base 1, ∀ p ∈ Bs.fibre 1 y, C.toChain.heightRatio p = 4 * Δ →
      p ∈ Bs.source 0 ∧
        Bs.fibre 1 y ∩ {q | C.toChain.heightRatio q = 4 * Δ} =
          Bs.fibre 0 (C.toChain.stageMap 0 p) :=
  WF.diskRim_of_rim_subset_source_OF1 fun _ _ _ hp hT =>
    C.rim_mem_source_zero_OF1 h3βc hβ2 hγ hγ34 hc hC Bs hp.1 hT

/-- **F1 on the frozen v2 layer** (`wholeDiskBoundary_eq_wholeCircleFiber_BAUGF`'s statement,
`TargetsBoundary-v3.1` l.388, plus the numerical premises). -/
theorem wholeDiskBoundary_eq_wholeCircleFiber_v2_OF1 (h3βc : 3 * βc ≤ β 2) (hβ2 : β 2 < 1)
    (hγ : 0 ≤ γ) (hγ34 : γ ≤ 3 / 4) (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    {Bs : BoundaryGaf02BasesV2 C.toChain} (WF : BoundaryWholeFiberSpecV2 C.toChain Bs) :
    ∀ y ∈ Bs.base 1, ∀ p ∈ Bs.fibre 1 y, C.toChain.heightRatio p = 4 * Δ →
      p ∈ Bs.source 0 ∧
        Bs.fibre 1 y ∩ {q | C.toChain.heightRatio q = 4 * Δ} =
          Bs.fibre 0 (C.toChain.stageMap 0 p) :=
  C.wholeDiskBoundary_eq_wholeCircleFiber_OF1 h3βc hβ2 hγ hγ34 hc hC WF.toV2b_OWF

/-- **The `diskRim` field of `BoundaryGeometricExports74`** (text v3.1 §R, decomposition v2). -/
theorem diskRim_v2_OF1 (h3βc : 3 * βc ≤ β 2) (hβ2 : β 2 < 1) (hγ : 0 ≤ γ) (hγ34 : γ ≤ 3 / 4)
    (hc : c 2 < 1 / 100000)
    (hC : 100 * (bder + 1) * (1 + bcut + cw 0 / Sg 0) * Λ * Δ < 1 / 1000000)
    (dec : BoundaryActualDecompositionV2 C.toChain) :
    ∀ y ∈ dec.bases.base 1, ∀ p ∈ dec.bases.fibre 1 y, C.toChain.heightRatio p = 4 * Δ →
      p ∈ dec.bases.source 0 ∧ dec.bases.fibre 1 y ∩ {q | C.toChain.heightRatio q = 4 * Δ} =
        dec.bases.fibre 0 (C.toChain.stageMap 0 p) :=
  C.wholeDiskBoundary_eq_wholeCircleFiber_v2_OF1 h3βc hβ2 hγ hγ34 hc hC dec.fibres

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
