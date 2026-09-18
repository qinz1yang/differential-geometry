import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.AmbientPointMove
import DifferentialGeometry.Topology.PiecewiseLinear.ConePairExtension
import DifferentialGeometry.Topology.PiecewiseLinear.StdSimplexCone

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphOn.image_openSimplex_eq_interior {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {f : (Fin (n + 2) → ℝ) → EuclideanSpace ℝ (Fin (n + 1))}
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) P) :
    f '' openSimplex (stdVertices n) = interior P := by
  have hP : IsPLBall (n + 1) P := ⟨f, hf⟩
  rw [hf.image_openSimplex_stdVertices, hf.image_stdSimplexBoundary_eq_frontier,
    hP.isPolyhedron.isCompact.isClosed.frontier_eq, sdiff_sdiff_cancel_left interior_subset]

theorem isConnected_interior_of_isPLBall {n : ℕ} {P : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hP : IsPLBall (n + 1) P) : IsConnected (interior P) := by
  obtain ⟨f, hf⟩ := hP
  rw [← hf.image_openSimplex_eq_interior, hf.image_openSimplex_stdVertices]
  exact hf.isConnected_sdiff_image_stdSimplexBoundary

theorem IsPLBall.exists_isPLHomeomorphOn_stdSimplex_stdCenter_eq {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hP : IsPLBall (n + 1) P)
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ interior P) :
    ∃ f : (Fin (n + 2) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)),
      IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) P ∧ f (stdCenter n) = p := by
  obtain ⟨f, hf⟩ := hP
  have hP : IsPLBall (n + 1) P := ⟨f, hf⟩
  have hc0 : f (stdCenter n) ∈ interior P := by
    rw [← hf.image_openSimplex_eq_interior]
    exact mem_image_of_mem f (stdCenter_mem_openSimplex n)
  obtain ⟨h, hh, hfix, hhp⟩ := exists_isPLHomeomorphOn_map_point_eqOn_compl
    isOpen_interior (isConnected_interior_of_isPLBall hP).isPreconnected hc0 hp
  have hint : h '' interior P = interior P := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      by_contra hy
      have h2 : h x = x := h.injective (hfix hy)
      exact hy (by rw [h2]; exact hx)
    · intro y hy
      refine ⟨h.symm y, ?_, h.apply_symm_apply y⟩
      by_contra hx
      have h1 := hfix hx
      rw [h.apply_symm_apply, id_eq] at h1
      exact hx (by rw [← h1]; exact hy)
  have hcl := hP.closure_interior
  have hPP : h '' P = P :=
    calc h '' P = h '' closure (interior P) := by rw [hcl]
      _ = closure (h '' interior P) := h.image_closure _
      _ = closure (interior P) := by rw [hint]
      _ = P := hcl
  have hhP : IsPLHomeomorphOn h P P := by
    have hres := hh.restrict hP.isPolyhedron (subset_univ P)
    rwa [hPP] at hres
  exact ⟨h ∘ f, hf.trans hhP, hhp⟩

theorem IsPLBall.exists_isPLHomeomorphOn_coneSet_of_mem_interior {n : ℕ}
    {P : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hP : IsPLBall (n + 1) P)
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ interior P) :
    ∃ f : (Fin (n + 2) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)),
      IsPLHomeomorphOn f
          (coneSet (stdCenter n)
            (simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)).space) P ∧
        f (stdCenter n) = p := by
  obtain ⟨f, hf, hfc⟩ := hP.exists_isPLHomeomorphOn_stdSimplex_stdCenter_eq hp
  refine ⟨f, ?_, hfc⟩
  rwa [← coneComplex_space_eq_coneSet (isConeBase_std n), coneComplex_std_space]

end DifferentialGeometry.Topology.PiecewiseLinear
