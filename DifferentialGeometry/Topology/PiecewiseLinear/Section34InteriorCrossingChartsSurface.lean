import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.BallStarring
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNhdsWithin

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.exists_surface_ball_chart_of_mem_open_disk
    {D : Set E} {f : (Fin 3 → ℝ) → E}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) {x : E}
    (hx : x ∈ D \ f '' stdSimplexBoundary 2) {N : Set E} (hN : N ∈ 𝓝 x) :
    ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → E),
      0 < r ∧ ContinuousOn g (Metric.ball c r) ∧ InjOn g (Metric.ball c r) ∧
        MapsTo g (Metric.ball c r) (D ∩ N) ∧ g c = x := by
  obtain ⟨T, hT, hcard, -, -, -⟩ :=
    exists_affineIndependent_openSimplex_subset (E := EuclideanSpace ℝ (Fin 2))
      (n := 1) (by simp) 0 Filter.univ_mem
  have hC : IsPLBall 2 (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2)))) :=
    isPLBall_convexHull_of_affineIndependent T hT hcard
  obtain ⟨k, hk⟩ := hC
  obtain ⟨z, hz, hzx⟩ : x ∈ f '' openSimplex (stdVertices 1) := by
    rwa [hf.image_openSimplex_stdVertices]
  let g := f ∘ Function.invFunOn k (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
  have hg : IsPLHomeomorphOn g (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2)))) D :=
    hk.symm.trans hf
  have hzc : k z ∈ interior (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2)))) := by
    rw [← hk.image_openSimplex_eq_interior]
    exact mem_image_of_mem k hz
  have hgc : g (k z) = x := by
    change f (Function.invFunOn k (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (k z)) = x
    rw [hk.bijOn.invOn_invFunOn.1 (openSimplex_stdVertices_subset_stdSimplex hz), hzx]
  have hgn : g ⁻¹' N ∈ 𝓝 (k z) :=
    (hg.isPiecewiseAffineOn.continuousOn.continuousAt
      (mem_interior_iff_mem_nhds.mp hzc)).preimage_mem_nhds (hgc.symm ▸ hN)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (isOpen_interior.mem_nhds hzc) hgn)
  have hballC := hball.trans (inter_subset_left.trans interior_subset)
  exact ⟨k z, r, g, hr, hg.isPiecewiseAffineOn.continuousOn.mono hballC,
    hg.bijOn.injOn.mono hballC,
    fun y hy => ⟨hg.bijOn.mapsTo (hballC hy), (hball hy).2⟩, hgc⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_surface_ball_chart_of_notMem_boundaryComplex
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {x : E} (hx : x ∈ K.space)
    (hnot : x ∉ (boundaryComplex 2 K).space) {N : Set E} (hN : N ∈ 𝓝 x) :
    ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → E),
      0 < r ∧ ContinuousOn g (Metric.ball c r) ∧ InjOn g (Metric.ball c r) ∧
        MapsTo g (Metric.ball c r) (K.space ∩ N) ∧ g c = x := by
  obtain ⟨D, hD, hDKN, hDn⟩ :=
    hK.exists_isPLBall_subset_of_mem_nhdsWithin hx (mem_nhdsWithin_of_mem_nhds hN)
  have hxD : x ∈ D := mem_of_mem_nhdsWithin hx hDn
  obtain ⟨L, hLfin, hLspace⟩ := hD.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLBall 2 L.space := hLspace.symm ▸ hD
  have hxL : x ∈ L.space := hLspace.symm ▸ hxD
  have hnotL : x ∉ (boundaryComplex 2 L).space := by
    intro hb
    exact hnot ((mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin K L hK
      hL.isCombinatorialManifoldWithBoundary
      (hLspace.subset.trans (hDKN.trans inter_subset_left)) hxL
      (hLspace.symm ▸ hDn)).mp hb)
  obtain ⟨f, hf⟩ := hD
  have hxcore : x ∈ D \ f '' stdSimplexBoundary 2 := by
    rw [hf.image_stdSimplexBoundary_eq_boundaryComplex L hLspace]
    exact ⟨hxD, hnotL⟩
  obtain ⟨c, r, g, hr, hgc, hgi, hgm, hgx⟩ :=
    hf.exists_surface_ball_chart_of_mem_open_disk hxcore hN
  exact ⟨c, r, g, hr, hgc, hgi,
    fun y hy => ⟨(hDKN (hgm hy).1).1, (hgm hy).2⟩, hgx⟩

theorem IsPLHomeomorphOn.exists_surface_ball_chart_of_mem_annulus_interior
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {J : Set F} {a b : ℝ} {A : Set E} {f : F × ℝ → E}
    (hf : IsPLHomeomorphOn f (J ×ˢ Icc a b) A) (hJ : IsPLSphere 1 J) (hab : a < b)
    {x : E} (hx : x ∈ A) (hnot : x ∉ f '' (J ×ˢ {a, b}))
    {N : Set E} (hN : N ∈ 𝓝 x) :
    ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → E),
      0 < r ∧ ContinuousOn g (Metric.ball c r) ∧ InjOn g (Metric.ball c r) ∧
        MapsTo g (Metric.ball c r) (A ∩ N) ∧ g c = x := by
  classical
  obtain ⟨K, hKfin, hK, -, hKspace, hKbd⟩ := hf.exists_annulus_complex hJ hab
  let _ : Finite K.faces := hKfin.to_subtype
  have hxK : x ∈ K.space := hKspace.symm ▸ hx
  have hnotK : x ∉ (boundaryComplex 2 K).space := by rwa [hKbd]
  simpa only [hKspace] using
    hK.exists_surface_ball_chart_of_notMem_boundaryComplex hxK hnotK hN

end DifferentialGeometry.Topology.PiecewiseLinear
