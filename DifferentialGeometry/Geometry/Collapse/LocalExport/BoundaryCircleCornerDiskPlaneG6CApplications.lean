import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornerDiskPlaneG6C

/-!
# Consumer of the edge-disk plane (lane O-G6C, G2i)

`BoundaryGaf02ChainE.surjective_zeroDefFn_height_of_disk_G6C`: at a rim point `p ∈ X₂ ∩ {T = 4Δ}`
whose WHOLE edge disk lies in the zero face `k`, `(d defFn_k, dT)` is onto `ℝ²` (corner
independence for zero faces, from `rank d(f₂, T) = 2`).
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

/-- **Zero-face corner independence from the whole edge disk.** -/
theorem surjective_zeroDefFn_height_of_disk_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs)
    (k : S.ZeroIdx_BAUGC) {p : W.Carrier} (hp : p ∈ Bs.source 1)
    (hT : C.toChain.heightRatio p = 4 * Δ)
    (hdisk : Bs.fibre 1 (C.toChain.stageMap 1 p) ⊆ C.toChain.actualZeroFace_BIFc k) :
    Surjective fun v : TangentSpace W.model p =>
      (mvfderiv W.model (Z.defFn k) p v, mvfderiv W.model C.toChain.heightRatio p v) := by
  obtain ⟨P, hP, hfP, hGP⟩ := C.exists_edgeDiskPlane_G6C WF hp
  have hzero : ∀ q ∈ Bs.fibre 1 (C.toChain.stageMap 1 p), Z.defFn k q = 0 := fun q hq => by
    have h := hdisk hq
    rw [Z.face_eq k] at h
    exact h
  have hpk : p ∈ C.toChain.actualZeroFace_BIFc k := hdisk ⟨hp, rfl⟩
  have hFP := hGP (Z.defFn k) ((Z.defFn_smooth k p).mdifferentiableAt (by simp))
    fun q hq => by rw [hzero q hq, hzero p ⟨hp, rfl⟩]
  exact C.surjective_zeroDefFn_height_of_plane_G6C Z k (Bs.source_one_subset_edgeParent_BIFc hp)
    hT hpk P hP hFP hfP

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
