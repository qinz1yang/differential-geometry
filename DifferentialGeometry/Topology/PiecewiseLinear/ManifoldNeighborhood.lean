import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNhdsWithin

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem isPLSphere_or_isPLBall_geometricLink_of_manifold_neighborhood
    {n : ℕ} (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hL : IsCombinatorialManifoldWithBoundary (n + 1) L) (hLK : L.space ⊆ K.space)
    {p : E} (hp : {p} ∈ K.faces) (hnhds : L.space ∈ 𝓝[K.space] p) :
    IsPLSphere n (SimplicialComplex.geometricLink K {p}).space ∨
      IsPLBall n (SimplicialComplex.geometricLink K {p}).space := by
  classical
  obtain ⟨R, hR, hRfin, hRL⟩ := exists_isSubdivision_restrict_isSubdivision K L hLK
  let _ : Finite R.faces := hRfin.to_subtype
  let A := restrict R L.space
  let _ : Finite A.faces := (restrict_faces_finite R _).to_subtype
  have hpR : {p} ∈ R.faces := hR.singleton_mem hp
  have hnhds' : A.space ∈ 𝓝[R.space] p := by
    rw [hRL.space_eq, hR.space_eq]
    exact hnhds
  have hpA : {p} ∈ A.faces := mem_faces_of_mem_nhdsWithin_space
    (restrict_faces_subset R L.space) hpR (by simp) hnhds'
  have hlink := geometricLink_eq_of_space_mem_nhdsWithin (restrict_faces_subset R L.space) hnhds'
  have hA := hL.of_isSubdivision hRL p hpA
  rw [hlink] at hA
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_geometricLink_of_isSubdivision hR hp
  exact hA.imp (fun h => h.of_isPLHomeomorphOn hf) (fun h => h.of_isPLHomeomorphOn hf)

theorem isCombinatorialManifoldWithBoundary_of_isPLBall_neighborhoods
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hlocal : ∀ p ∈ K.space, ∃ C : Set E, IsPLBall (n + 1) C ∧
      C ⊆ K.space ∧ C ∈ 𝓝[K.space] p) : IsCombinatorialManifoldWithBoundary (n + 1) K := by
  intro p hp
  obtain ⟨C, hC, hCK, hCnhds⟩ := hlocal p (K.subset_space hp (Finset.mem_singleton_self p))
  obtain ⟨L, hLfin, hLC⟩ := hC.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLBall (n + 1) L.space := hLC.symm ▸ hC
  exact isPLSphere_or_isPLBall_geometricLink_of_manifold_neighborhood K L
    hL.isCombinatorialManifoldWithBoundary (hLC ▸ hCK) hp (hLC ▸ hCnhds)

end DifferentialGeometry.Topology.PiecewiseLinear
