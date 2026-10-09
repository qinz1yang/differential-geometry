import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornersZeroLocalG6C
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryFrontierM1BGR

/-!
# Consumer of the zero-face local description (lane O-G6C, G2b)

`BoundaryGaf02ChainE.exists_open_M₁_zeroFace_G6C`: around the whole actual zero face `Z_k` there is
an open set `U` on which `M₁ = {defFn_k ≥ 0}` (other zero domains: pairwise disjoint compact; cusp
cores: compact, disjoint from the zero domains by E4b).
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

/-- **`M₁` near a whole zero face.** -/
theorem exists_open_M₁_zeroFace_G6C {Bs : BoundaryGaf02BasesV2 C.toChain}
    (Z : BoundaryActualZeroDomains_BIFc C.toChain Bs) {rd : ℝ} (hrd : 0 < rd)
    (hrd4 : rd < 1 / 10000) (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (k : S.ZeroIdx_BAUGC) :
    ∃ U : Set W.Carrier, IsOpen U ∧ C.toChain.actualZeroFace_BIFc k ⊆ U ∧
      C.toChain.M₁_BIFc ∩ U = {p | 0 ≤ Z.defFn k p} ∩ U := by
  have hcomp := (C.bcg06_on_boundary_chain_BGR hrd hrd4 hrdc hprem hθ).1
  obtain ⟨U, hUdef⟩ : ∃ U : Set W.Carrier, U = (⋂ j : {j : S.ZeroIdx_BAUGC // j ≠ k},
      (C.toChain.actualZeroDomain_BIFc j.1)ᶜ) ∩ ⋂ i, (C.toChain.cuspCore_BIF i)ᶜ := ⟨_, rfl⟩
  have hU : IsOpen U := by
    rw [hUdef]
    have h1 : ∀ j : {j : S.ZeroIdx_BAUGC // j ≠ k},
        IsOpen (C.toChain.actualZeroDomain_BIFc j.1)ᶜ := fun j =>
      (Z.isCompact_domain j.1).isClosed.isOpen_compl
    have h2 : ∀ i, IsOpen (C.toChain.cuspCore_BIF i)ᶜ := fun i =>
      (hcomp i).compact_core.isClosed.isOpen_compl
    exact (isOpen_iInter_of_finite h1).inter (isOpen_iInter_of_finite h2)
  have hZd : ∀ j, j ≠ k → Disjoint U (C.toChain.actualZeroDomain_BIFc j) := by
    intro j hjk
    rw [hUdef]
    exact Set.disjoint_left.mpr fun p hp => mem_iInter.mp hp.1 ⟨j, hjk⟩
  have hCd : Disjoint U C.toChain.cuspCores_BIF := by
    rw [hUdef, BoundaryGaf02Chain.cuspCores_BIF]
    exact Set.disjoint_left.mpr fun p hp hpc => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hpc
      exact mem_iInter.mp hp.2 i hi
  have hfU : C.toChain.actualZeroFace_BIFc k ⊆ U := by
    intro p hp
    have hpZ : p ∈ C.toChain.actualZeroDomain_BIFc k := by
      rw [Z.domain_eq k]
      rw [Z.face_eq k] at hp
      exact le_of_eq hp
    rw [hUdef]
    refine ⟨mem_iInter.mpr fun j => fun hpj => ?_, mem_iInter.mpr fun i => fun hpi => ?_⟩
    · exact Set.disjoint_left.mp (Z.pairwise_disjoint (Ne.symm j.2)) hpZ hpj
    · exact Set.disjoint_left.mp (C.cuspCore_disjoint_actualZeroDomain_BGR hrd hrd4 hrdc hprem hθ
        i k) hpi hpZ
  exact ⟨U, hU, hfU, M₁_inter_open_G6C Z.toBoundaryZeroDefining_BIFc k hU hZd hCd⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
