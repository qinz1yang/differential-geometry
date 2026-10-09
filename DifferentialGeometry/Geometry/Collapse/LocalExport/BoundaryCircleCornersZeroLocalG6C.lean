import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCircleCornerLabelsG6C

/-!
# G6c local description, zero faces: `M₁` near one zero face (lane O-G6C, G2 step L4)

* `interior_actualZeroDomain_G6C`: `int Z_k = {defFn_k < 0}` (closed sublevel, `∂Z_k = face`);
* `M₁_inter_open_G6C`: on an open set `U` that misses the other zero domains and the cusp cores,
  `M₁ ∩ U = {defFn_k ≥ 0} ∩ U` (`M₁ = W \ int(⋃ Z_j ∪ C_∂)`).
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

section ZeroLocal

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}

/-- **`int Z_k = {defFn_k < 0}`.** -/
theorem interior_actualZeroDomain_G6C (Zd : BoundaryZeroDefining_BIFc C) (k : S.ZeroIdx_BAUGC) :
    interior (C.actualZeroDomain_BIFc k) = {p | Zd.defFn k p < 0} := by
  rw [← self_sdiff_frontier, Zd.frontier_eq k, Zd.domain_eq k, Zd.face_eq k]
  ext p
  simp only [Set.mem_sdiff, mem_ofPred_eq]
  exact ⟨fun h => lt_of_le_of_ne h.1 h.2, fun h => ⟨h.le, h.ne⟩⟩

/-- **`M₁` near one zero face**: on an open `U` missing the other zero domains and the cusp cores,
`M₁ ∩ U = {defFn_k ≥ 0} ∩ U`. -/
theorem M₁_inter_open_G6C (Zd : BoundaryZeroDefining_BIFc C) (k : S.ZeroIdx_BAUGC)
    {U : Set W.Carrier} (hU : IsOpen U) (hZ : ∀ j, j ≠ k → Disjoint U (C.actualZeroDomain_BIFc j))
    (hcusp : Disjoint U C.cuspCores_BIF) :
    C.M₁_BIFc ∩ U = {p | 0 ≤ Zd.defFn k p} ∩ U := by
  have hA : ((⋃ j, C.actualZeroDomain_BIFc j) ∪ C.cuspCores_BIF) ∩ U =
      C.actualZeroDomain_BIFc k ∩ U := by
    ext p
    constructor
    · rintro ⟨hp | hp, hpU⟩
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hp
        by_cases hjk : j = k
        · exact ⟨hjk ▸ hj, hpU⟩
        · exact absurd hj (Set.disjoint_left.mp (hZ j hjk) hpU)
      · exact absurd hp (Set.disjoint_left.mp hcusp hpU)
    · rintro ⟨hp, hpU⟩
      exact ⟨Or.inl (mem_iUnion.mpr ⟨k, hp⟩), hpU⟩
  have hint : interior ((⋃ j, C.actualZeroDomain_BIFc j) ∪ C.cuspCores_BIF) ∩ U =
      interior (C.actualZeroDomain_BIFc k) ∩ U := by
    rw [← hU.interior_eq, ← interior_inter, hA, interior_inter, hU.interior_eq]
  ext p
  constructor
  · rintro ⟨hpM, hpU⟩
    refine ⟨?_, hpU⟩
    by_contra hneg
    have hlt : Zd.defFn k p < 0 := lt_of_not_ge hneg
    have hpi : p ∈ interior (C.actualZeroDomain_BIFc k) := by
      rw [interior_actualZeroDomain_G6C Zd k]
      exact hlt
    exact hpM (hint.symm.subset ⟨hpi, hpU⟩).1
  · rintro ⟨hp0, hpU⟩
    refine ⟨fun hpi => ?_, hpU⟩
    have h := (hint.subset ⟨hpi, hpU⟩).1
    rw [interior_actualZeroDomain_G6C Zd k] at h
    have hp0' : 0 ≤ Zd.defFn k p := hp0
    exact absurd hp0' (not_le.mpr h)

end ZeroLocal

end DifferentialGeometry.Geometry.Collapse
