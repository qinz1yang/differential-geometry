import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryBall
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_nonsingular_two_cell_of_isPLBall
    {D : Set (EuclideanSpace ℝ (Fin 3))} {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D) :
    ∃ A : SingularTwoCell (EuclideanSpace ℝ (Fin 3)),
      A.IsNonsingular ∧ A '' A.domain = D ∧ Set.range A.boundary = r '' stdSimplexBoundary 2 := by
  classical
  obtain ⟨T, hT, hcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (n := 1) (by simp) (0 : EuclideanSpace ℝ (Fin 2)) Filter.univ_mem
  have hP : IsPLBall 2 (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2)))) :=
    isPLBall_convexHull_of_affineIndependent T hT hcard
  obtain ⟨p, hp⟩ := hP
  let P := convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2)))
  let f := r ∘ Function.invFunOn p (stdSimplex ℝ (Fin 3))
  have hf : IsPLHomeomorphOn f P D := hp.symm.trans hr
  let A : SingularTwoCell (EuclideanSpace ℝ (Fin 3)) :=
    { domain := P
      isPLBall_domain := ⟨p, hp⟩
      toFun := f
      isPLOn := fun x hx => ⟨hf.isPiecewiseAffineOn.continuousOn x hx,
        hf.isPiecewiseAffineOn x hx⟩ }
  refine ⟨A, hf.bijOn.injOn, hf.image_eq, ?_⟩
  have hfront : p '' stdSimplexBoundary 2 = frontier P :=
    IsPLHomeomorphOn.image_stdSimplexBoundary_eq_frontier (n := 1) hp
  have hbound : Set.range A.boundary = f '' frontier P := by
    change Set.range (f ∘ (Subtype.val : frontier P → _)) = _
    rw [Set.range_comp, Subtype.range_coe]
  rw [hbound, ← hfront, image_image]
  apply Set.EqOn.image_eq
  intro x hx
  exact congrArg r (hp.bijOn.invOn_invFunOn.1 hx.1)

theorem exists_nonsingular_two_cell_of_boundary_ball
    {M BdM C D : Set (EuclideanSpace ℝ (Fin 3))}
    (hC : IsPLBall 3 C) (hCM : C ⊆ M)
    {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    (hDC : D ⊆ frontier C) (hCB : C ∩ BdM = D) :
    ∃ A : SingularTwoCell (EuclideanSpace ℝ (Fin 3)),
      A.IsNonsingular ∧ A '' A.domain ⊆ M ∧
      Set.range A.boundary = r '' stdSimplexBoundary 2 ∧
      A '' A.domain ∩ BdM = r '' stdSimplexBoundary 2 := by
  have hS := hC.isPLSphere_frontier
  have hD : IsPLBall 2 D := ⟨r, hr⟩
  have hclosed : IsClosed C := hC.isPolyhedron.isClosed
  have hfrontC : frontier C ⊆ C := hclosed.frontier_subset
  let Q := closure (frontier C \ D)
  have hQC : Q ⊆ C := (closure_minimal sdiff_subset isClosed_frontier).trans hfrontC
  obtain ⟨q, hq⟩ := hS.isPLBall_closure_sdiff hD hDC
  obtain ⟨A, hA, hAQ, hboundary⟩ := exists_nonsingular_two_cell_of_isPLBall hq
  have hQD : Q ∩ D = r '' stdSimplexBoundary 2 := by
    rw [inter_comm]
    exact hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hr hDC
  have hQBd : Q ∩ BdM = Q ∩ D := by
    rw [← hCB, ← inter_assoc, inter_eq_left.mpr hQC]
  refine ⟨A, hA, ?_, ?_, ?_⟩
  · rw [hAQ]
    exact hQC.trans hCM
  · rw [hboundary, hS.image_stdSimplexBoundary_complement hD hDC hq]
    exact hQD
  · rw [hAQ]
    exact hQBd.trans hQD

theorem exists_nonsingular_two_cell_in_boundary_ball
    {M C D : Set (EuclideanSpace ℝ (Fin 3))}
    (hC : IsPLBall 3 C) (hCM : C ⊆ M)
    {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D)
    (hDC : D ⊆ C) (hDM : D ⊆ frontier M) :
    ∃ A : SingularTwoCell (EuclideanSpace ℝ (Fin 3)),
      A.IsNonsingular ∧ A '' A.domain ⊆ M ∧
      Set.range A.boundary = r '' stdSimplexBoundary 2 ∧
      A '' A.domain ∩ frontier M = r '' stdSimplexBoundary 2 := by
  obtain ⟨Q, hQ, hQM, hQB, hDQ⟩ := exists_isPLBall_inter_frontier_eq_of_subset
    (n := 2) (by simp) hC hCM ⟨r, hr⟩ hDC hDM
  exact exists_nonsingular_two_cell_of_boundary_ball hQ hQM hr hDQ hQB

theorem exists_nonsingular_two_cell_in_ball
    {M D : Set (EuclideanSpace ℝ (Fin 3))} (hM : IsPLBall 3 M)
    {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D) (hDM : D ⊆ frontier M) :
    ∃ A : SingularTwoCell (EuclideanSpace ℝ (Fin 3)),
      A.IsNonsingular ∧ A '' A.domain ⊆ M ∧
      Set.range A.boundary = r '' stdSimplexBoundary 2 ∧
      A '' A.domain ∩ frontier M = r '' stdSimplexBoundary 2 :=
  exists_nonsingular_two_cell_in_boundary_ball hM subset_rfl hr
    (hDM.trans hM.isPolyhedron.isClosed.frontier_subset) hDM

open Classical in
theorem exists_nhdsWithin_nonsingular_two_cells
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ frontier K.space) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 3)), U ∈ 𝓝[K.space] x ∧
      ∀ (D : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D → D ⊆ U → D ⊆ frontier K.space →
        ∃ A : SingularTwoCell (EuclideanSpace ℝ (Fin 3)),
          A.IsNonsingular ∧ A '' A.domain ⊆ K.space ∧
          Set.range A.boundary = r '' stdSimplexBoundary 2 ∧
          A '' A.domain ∩ frontier K.space = r '' stdSimplexBoundary 2 := by
  obtain ⟨U, hU, hballs⟩ := exists_nhdsWithin_boundary_disk_balls K hK hx
  refine ⟨U, hU, ?_⟩
  intro D r hr hDU hDK
  obtain ⟨Q, hQ, hQK, hQB, hDQ⟩ := hballs D ⟨r, hr⟩ hDU hDK
  exact exists_nonsingular_two_cell_of_boundary_ball hQ hQK hr hDQ hQB

end DifferentialGeometry.Topology.PiecewiseLinear
