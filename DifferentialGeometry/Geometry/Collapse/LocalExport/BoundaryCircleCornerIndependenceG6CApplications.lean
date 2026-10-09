import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornerIndependenceG6C

/-!
# Consumer of the corner independence (lane O-G6C, G2h)

`BoundaryGaf02ChainE.surjective_zeroDefFn_height_of_plane_G6C`: at a rim point of the edge parent
lying on the zero face `k`, the zero defining function and `T` have jointly onto differentials as
soon as `d(defFn_k)` and `df₂` vanish on a common plane (the tangent plane of the edge disk).
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

/-- **Zero-face corner independence from the edge-disk plane.** -/
theorem surjective_zeroDefFn_height_of_plane_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) (k : S.ZeroIdx_BAUGC) {p : W.Carrier}
    (hp : p ∈ Bs.edgeParent) (hT : C.toChain.heightRatio p = 4 * Δ)
    (hpk : p ∈ C.toChain.actualZeroFace_BIFc k)
    (P : Submodule ℝ (TangentSpace W.model p)) (hP : Module.finrank ℝ P = 2)
    (hFP : ∀ w ∈ P, mvfderiv W.model (Z.defFn k) p w = 0)
    (hfP : ∀ w ∈ P, mvfderiv W.model (C.toChain.stageMap 1) p w = 0) :
    Surjective fun v : TangentSpace W.model p =>
      (mvfderiv W.model (Z.defFn k) p v, mvfderiv W.model C.toChain.heightRatio p v) := by
  have h0 : Z.defFn k p = 0 := by
    rw [Z.face_eq k] at hpk
    exact hpk
  have hFn : mvfderiv W.model (Z.defFn k) p ≠ 0 := by
    intro h
    apply Z.defFn_regular k p h0
    ext v
    have h1 := congrArg (fun L => L v) h
    exact h1
  exact C.surjective_faceFun_height_of_plane_G6C hp hT (Z.defFn k) hFn P hP hFP hfP

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
