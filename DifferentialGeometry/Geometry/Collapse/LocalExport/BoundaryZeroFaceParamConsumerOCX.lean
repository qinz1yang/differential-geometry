import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroFaceParamOCX
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutCapped

/-!
# Consumer of BCG07 `face_param` (lane O-CROSS, G4): the actual zero faces are nonempty and
connected

What F5z (07.i) reads off `face_param`: every actual zero face of `C.E` is the continuous image of
`S²` or `T²`, hence nonempty and preconnected (`actualZeroFace_isConnected_OCX`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
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

/-- **Every actual zero face is nonempty and connected** (`face_param`: a continuous image of
`S²` or `T²`). -/
theorem actualZeroFace_isConnected_OCX (hεr : εr < 1 / 2) (k : S.ZeroIdx_BAUGC) :
    IsConnected (C.toChain.actualZeroFace_BIFc k) := by
  rcases C.face_param_OCX hεr k with ⟨e₀, he, hr⟩ | ⟨e₀, he, hr⟩
  · have := GC.GraphManifold.Assembly.closureSphere_connectedSpace.{0}
    rw [← hr]
    exact isConnected_range he.isEmbedding.continuous
  · rw [← hr]
    exact isConnected_range he.isEmbedding.continuous

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
