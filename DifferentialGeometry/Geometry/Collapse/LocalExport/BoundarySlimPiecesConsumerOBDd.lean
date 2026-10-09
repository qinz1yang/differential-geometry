import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimPiecesOBDd
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimArcProductOBDd

/-!
# Consumer of the slim components (lane S-BD2d, suffix `_OBDd`), group G10c

**`BoundaryGaf02ChainE.exists_slimD3Products_OBDd`**: over each of the finitely many sub-arcs
`γ i` of `exists_slimD3Arcs_OBDd` (the components of `D₃ = K₃ ∩ C₃`) the slim stage has the whole
interval product `S² × [0, 1] → W` or `T² × [0, 1] → W` of `exists_arcProduct_OBDd`.
-/




set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

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

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

include C in
theorem exists_slimD3Products_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (hεr : εr < 1 / 2) {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ (N : ℕ) (γ : Fin N → SmoothEmbeddedBaseArc_EFE (dec.bases.base 2)),
      (Pairwise fun i j => Disjoint ((γ i).toFun '' Icc 0 1) ((γ j).toFun '' Icc 0 1)) ∧
      (⋃ i, (γ i).toFun '' Icc 0 1 = dec.slim.K₃ ∩ dec.bases.slimBaseDomain_BIFc) ∧
      ∀ i, (∃ m : ClosureSphere.{0} × Icc (0 : ℝ) 1 → W.Carrier,
        ContMDiff ((𝓡 2).prod (𝓡∂ 1)) W.model ∞ m ∧ Injective m ∧
        (∀ z, Injective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) W.model m z)) ∧
        (∀ z, C.toChain.stageMap 2 (m z) = (γ i).toFun z.2) ∧
        range m = dec.bases.source 2 ∩
          C.toChain.stageMap 2 ⁻¹' ((γ i).toFun '' Icc 0 1) ∧
        ∀ b, range (fun z => m (z, iccEnd b)) =
          dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {(γ i).toFun (iccEnd b)}) ∨
      (∃ m : Torus × Icc (0 : ℝ) 1 → W.Carrier,
        ContMDiff (torusModel.prod (𝓡∂ 1)) W.model ∞ m ∧ Injective m ∧
        (∀ z, Injective (mfderiv (torusModel.prod (𝓡∂ 1)) W.model m z)) ∧
        (∀ z, C.toChain.stageMap 2 (m z) = (γ i).toFun z.2) ∧
        range m = dec.bases.source 2 ∩
          C.toChain.stageMap 2 ⁻¹' ((γ i).toFun '' Icc 0 1) ∧
        ∀ b, range (fun z => m (z, iccEnd b)) =
          dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {(γ i).toFun (iccEnd b)}) := by
  obtain ⟨N, γ, hdisj, hunion, -, -⟩ := C.exists_slimD3Arcs_OBDd dec hεr hrd hrd4 hrdc hprem hθ
  obtain ⟨P, hP⟩ := C.exists_slimSubmersion_OBDd dec
  exact ⟨N, γ, hdisj, hunion, fun i => C.exists_arcProduct_OBDd dec P hP (γ i)⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
