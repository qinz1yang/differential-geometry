import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimArcProductOBDd

/-!
# Consumer of the slim interval products (lane S-BD2d, suffix `_OBDd`), group G10b

**`BoundaryGaf02ChainE.exists_arcProduct_decArc_OBDd`**: over EVERY arc `k` of the compact slim
choice `dec.slim` of the decomposition (`K₃ = ⋃ arcs`), the whole preimage `X₃ ∩ f₃⁻¹(arc k [0, 1])`
is the image of a smooth injective map `S² × [0, 1] → W` or `T² × [0, 1] → W` with injective
differential over the arc, whole end fibres included (`exists_arcProduct_OBDd` for the smooth
embedded base arc of `dec.slim`).
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
theorem exists_arcProduct_decArc_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (k : Fin dec.slim.arcCount) :
    (∃ m : ClosureSphere.{0} × Icc (0 : ℝ) 1 → W.Carrier,
      ContMDiff ((𝓡 2).prod (𝓡∂ 1)) W.model ∞ m ∧ Injective m ∧
      (∀ z, Injective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) W.model m z)) ∧
      (∀ z, C.toChain.stageMap 2 (m z) = dec.slim.arc k z.2) ∧
      range m = dec.bases.source 2 ∩
        C.toChain.stageMap 2 ⁻¹' (dec.slim.arc k '' Icc 0 1) ∧
      ∀ b, range (fun z => m (z, iccEnd b)) =
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {dec.slim.arc k (iccEnd b)}) ∨
    (∃ m : Torus × Icc (0 : ℝ) 1 → W.Carrier,
      ContMDiff (torusModel.prod (𝓡∂ 1)) W.model ∞ m ∧ Injective m ∧
      (∀ z, Injective (mfderiv (torusModel.prod (𝓡∂ 1)) W.model m z)) ∧
      (∀ z, C.toChain.stageMap 2 (m z) = dec.slim.arc k z.2) ∧
      range m = dec.bases.source 2 ∩
        C.toChain.stageMap 2 ⁻¹' (dec.slim.arc k '' Icc 0 1) ∧
      ∀ b, range (fun z => m (z, iccEnd b)) =
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {dec.slim.arc k (iccEnd b)}) := by
  obtain ⟨P, hP⟩ := C.exists_slimSubmersion_OBDd dec
  exact C.exists_arcProduct_OBDd dec P hP
    { toFun := dec.slim.arc k
      smooth := dec.slim.arc_smooth k
      injOn := dec.slim.arc_injOn k
      deriv_ne := dec.slim.arc_deriv k
      mapsTo := fun t ht => dec.slim.arc_subset_base k ⟨t, ht, rfl⟩ }

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
