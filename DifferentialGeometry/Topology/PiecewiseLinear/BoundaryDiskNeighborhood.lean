import DifferentialGeometry.Topology.PiecewiseLinear.DiskCollar
import DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
private theorem exists_boundary_manifold_neighborhood
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {D U : Set E}
    (hD : IsCompact D) (hDK : D ⊆ (boundaryComplex (n + 1) K).space)
    (hU : U ∈ 𝓝ˢ[K.space] D) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary (n + 1) L ∧ L.space ⊆ K.space ∧
      L.space ⊆ U ∧ D ⊆ (boundaryComplex (n + 1) L).space := by
  classical
  obtain ⟨O, hO, hDO, hOU⟩ := mem_nhdsSetWithin.mp hU
  have hDK' := hDK.trans (boundaryComplex_space_subset (n + 1) K)
  obtain ⟨K', L, hK', hfin, hL, hman, hLO, hnhds⟩ :=
    hK.exists_isSubdivision_neighborhood hD hDK' hO hDO
  have hLfin := hfin.subset hL
  let _ : Finite L.faces := hLfin.to_subtype
  have hLK : L.space ⊆ K.space := hK'.space_eq ▸ space_mono_of_faces_subset hL
  refine ⟨L, hLfin, hman, hLK, fun x hx => hOU ⟨hLO hx, hLK hx⟩, ?_⟩
  intro x hx
  exact inter_boundaryComplex_space_subset_of_subset K L hK hman hLK
    ⟨mem_of_mem_nhdsWithin (hDK' hx) (hnhds x hx), hDK hx⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLBall_inter_boundaryComplex_eq_subset
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {D U : Set E}
    (hD : IsPLBall 2 D) (hDK : D ⊆ (boundaryComplex 3 K).space)
    (hU : U ∈ 𝓝ˢ[K.space] D) :
    ∃ A : Geometry.SimplicialComplex ℝ E, A.faces.Finite ∧ IsPLBall 3 A.space ∧
      A.space ⊆ K.space ∧ A.space ⊆ U ∧ A.space ∩ (boundaryComplex 3 K).space = D ∧
      D ⊆ (boundaryComplex 3 A).space := by
  classical
  obtain ⟨L, hLfin, hL, hLK, hLU, hDL⟩ :=
    exists_boundary_manifold_neighborhood hK hD.isPolyhedron.isCompact hDK hU
  let _ : Finite L.faces := hLfin.to_subtype
  obtain ⟨A, hAfin, hA, hAL, hmeet, hDA⟩ := hL.exists_isPLBall_inter_boundaryComplex_eq hD hDL
  refine ⟨A, hAfin, hA, hAL.trans hLK, hAL.trans hLU, ?_, hDA⟩
  apply Subset.antisymm
  · rintro x ⟨hxA, hxK⟩
    exact hmeet ▸ ⟨hxA, inter_boundaryComplex_space_subset_of_subset K L hK hL hLK
      ⟨hAL hxA, hxK⟩⟩
  · intro x hx
    exact ⟨(hmeet.symm ▸ hx).1, hDK hx⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLBall_containing_boundary_disk_subset
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {D U : Set E}
    (hD : IsPLBall 2 D) (hDK : D ⊆ (boundaryComplex 3 K).space)
    (hU : U ∈ 𝓝ˢ[K.space] D) :
    ∃ C : Set E, IsPLBall 3 C ∧ C ⊆ K.space ∧ C ⊆ U ∧ D ⊆ C := by
  obtain ⟨A, _, hA, hAK, hAU, hmeet, _⟩ :=
    hK.exists_isPLBall_inter_boundaryComplex_eq_subset hD hDK hU
  exact ⟨A.space, hA, hAK, hAU, hmeet.symm.subset.trans inter_subset_left⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_collar_of_boundary_disk_subset
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {D U : Set E}
    (hD : IsPLBall 2 D) (hDK : D ⊆ (boundaryComplex 3 K).space)
    (hU : U ∈ 𝓝ˢ[K.space] D) :
    ∃ (C : Set E) (ρ : E × ℝ → E),
      IsPLHomeomorphOn ρ (D ×ˢ Icc 0 1) C ∧ C ⊆ K.space ∧ C ⊆ U ∧
      C ∩ (boundaryComplex 3 K).space = D ∧ (∀ x ∈ D, ρ (x, 0) = x) ∧
      MapsTo ρ (D ×ˢ Ioc 0 1) (K.space \ (boundaryComplex 3 K).space) := by
  classical
  obtain ⟨L, hLfin, hL, hLK, hLU, hDL⟩ :=
    exists_boundary_manifold_neighborhood hK hD.isPolyhedron.isCompact hDK hU
  let _ : Finite L.faces := hLfin.to_subtype
  obtain ⟨C, ρ, hρ, hCL, hmeet, hfix, hpos⟩ := hL.exists_collar_of_boundary_disk hD hDL
  have hbd := inter_boundaryComplex_space_subset_of_subset K L hK hL hLK
  refine ⟨C, ρ, hρ, hCL.trans hLK, hCL.trans hLU, ?_, hfix, ?_⟩
  · apply Subset.antisymm
    · rintro x ⟨hxC, hxK⟩
      exact hmeet ▸ ⟨hxC, hbd ⟨hCL hxC, hxK⟩⟩
    · intro x hx
      exact ⟨(hmeet.symm ▸ hx).1, hDK hx⟩
  · intro z hz
    have h := hpos hz
    exact ⟨hLK h.1, fun hb => h.2 (hbd ⟨h.1, hb⟩)⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_push_boundary_disk_subset
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {D U : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    (hDK : D ⊆ (boundaryComplex 3 K).space) (hU : U ∈ 𝓝ˢ[K.space] D) :
    ∃ (Q : Set E) (q : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) Q ∧ Q ⊆ K.space ∧ Q ⊆ U ∧
      q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 ∧
      Q ∩ (boundaryComplex 3 K).space = r '' stdSimplexBoundary 2 := by
  classical
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  obtain ⟨L, hLfin, hL, hLK, hLU, hDL⟩ :=
    exists_boundary_manifold_neighborhood hK hD.isPolyhedron.isCompact hDK hU
  let _ : Finite L.faces := hLfin.to_subtype
  obtain ⟨Q, q, hq, hQL, hqb, hmeet⟩ := hL.exists_isPLHomeomorphOn_push_boundary_disk hr hDL
  refine ⟨Q, q, hq, hQL.trans hLK, hQL.trans hLU, hqb, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨hxQ, hxK⟩
    exact hmeet ▸ ⟨hxQ, inter_boundaryComplex_space_subset_of_subset K L hK hL hLK
      ⟨hQL hxQ, hxK⟩⟩
  · intro x hx
    refine ⟨(hmeet.symm ▸ hx).1, hDK ?_⟩
    obtain ⟨z, hz, rfl⟩ := hx
    exact hr.bijOn.mapsTo hz.1

end DifferentialGeometry.Topology.PiecewiseLinear
