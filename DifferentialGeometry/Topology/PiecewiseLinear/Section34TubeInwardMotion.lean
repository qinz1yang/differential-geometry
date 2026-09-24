import DifferentialGeometry.Topology.PiecewiseLinear.Section34OrientedTubeBicollar
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BicollarLocalization

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_inward_homeomorph
    {K A : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
    [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    (hA : IsCombinatorialManifoldWithBoundary 3 A) (hAK : A.space ⊆ interior K.space)
    {Z O : Set (EuclideanSpace ℝ (Fin 3))} (hZ : IsCompact Z)
    (hZB : Z ⊆ frontier A.space) (hO : IsOpen O) (hZO : Z ⊆ O)
    (hOK : O ⊆ interior K.space) :
    ∃ φ : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn φ univ univ ∧ EqOn φ id Oᶜ ∧ MapsTo φ A.space A.space ∧
      MapsTo φ Z (interior A.space) ∧
      ∀ x ∈ A.space, φ x ∈ frontier A.space → φ x = x := by
  let _ : DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _
  have hfrontA := frontier_space_eq_boundaryComplex_space hA
  have hfrontK := frontier_space_eq_boundaryComplex_space hK
  have hdis : Disjoint A.space (boundaryComplex 3 K).space := by
    rw [← hfrontK]
    exact disjoint_interior_frontier.mono_left hAK
  obtain ⟨W, ρ, hW, hWK, hn, hρ, hzero, hside⟩ :=
    hK.exists_oriented_boundary_bicollar hA (hAK.trans interior_subset) hdis
  rw [← hfrontA] at hn hρ hzero hside
  rw [← hfrontK, self_sdiff_frontier] at hWK
  have hBpoly : IsPolyhedron (frontier A.space) :=
    hfrontA ▸ isPolyhedron_space (boundaryComplex 3 A)
  have hBK : frontier A.space ⊆ interior K.space :=
    (isPolyhedron_space A).isClosed.frontier_subset.trans hAK
  have hBW : frontier A.space ⊆ interior W := by
    obtain ⟨V, hV, hBV, hVW⟩ := mem_nhdsSetWithin.mp hn
    exact fun x hx => interior_maximal
      (fun y hy => hVW ⟨hy.1, interior_subset hy.2⟩)
      (hV.inter isOpen_interior) ⟨hBV hx, hBK hx⟩
  obtain ⟨φ, hφ, hfix, hmap, hpush, hboundary⟩ :=
    hρ.exists_bicollar_inward_preserving_region hBpoly hW (isPolyhedron_space K)
      hBW hWK hzero (hρ.image_nonnegative_half_of_mem_iff hside) hZ hZB hO hZO hOK
  exact ⟨φ, hφ, hfix.mono (compl_subset_compl.mpr inter_subset_left),
    hmap, hpush, hboundary⟩

open Classical in
theorem IsPLHomeomorphInto.exists_inward_homeomorph_invFunOn_image
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsPLBall 3 P) {N : Set M}
    (hN : IsPolyhedralManifoldWithBoundary (n := 3) 3 N)
    (hNP : N ⊆ interior (u '' P)) {Z O : Set (EuclideanSpace ℝ (Fin 3))}
    (hZ : IsCompact Z) (hZB : Z ⊆ frontier (Function.invFunOn u P '' N))
    (hO : IsOpen O) (hZO : Z ⊆ O) (hOP : O ⊆ interior P) :
    ∃ φ : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn φ univ univ ∧ EqOn φ id Oᶜ ∧
      MapsTo φ (Function.invFunOn u P '' N) (Function.invFunOn u P '' N) ∧
      MapsTo φ Z (interior (Function.invFunOn u P '' N)) ∧
      ∀ x ∈ Function.invFunOn u P '' N,
        φ x ∈ frontier (Function.invFunOn u P '' N) → φ x = x := by
  obtain ⟨K, hKfin, hKspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsCombinatorialManifoldWithBoundary 3 K :=
    (hKspace.symm ▸ hP).isCombinatorialManifoldWithBoundary
  obtain ⟨A, hAfin, hAspace, hA⟩ :=
    hu.exists_simplicialComplex_invFunOn_image hN (hNP.trans interior_subset)
  let _ : Finite A.faces := hAfin.to_subtype
  have hAint : A.space ⊆ interior K.space := by
    rw [hAspace, hKspace]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := hu.image_interior.symm.subset (hNP hy)
    rw [← hxy, hu.injOn.leftInvOn_invFunOn (interior_subset hx)]
    exact hx
  have hZB' : Z ⊆ frontier A.space := hAspace.symm ▸ hZB
  obtain ⟨φ, hφ, hfix, hmap, hpush, hboundary⟩ :=
    hK.exists_inward_homeomorph hA hAint hZ hZB' hO hZO (hKspace.symm ▸ hOP)
  rw [hAspace] at hmap hpush hboundary
  exact ⟨φ, hφ, hfix, hmap, hpush, hboundary⟩

end DifferentialGeometry.Topology.PiecewiseLinear
