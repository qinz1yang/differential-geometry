import DifferentialGeometry.Topology.PiecewiseLinear.FiberCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.ConvexFrontier

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.exists_isPLHomeomorphOn_disk_of_subset_fiber {J : Set E}
    (hJ : IsPLSphere 1 J) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {r : ℝ} (hJr : J ⊆ {x | ℓ x = r})
    {W : Set E} (hW : IsOpen W) (hWconv : Convex ℝ W) (hJW : J ⊆ W) :
    ∃ (D : Set E) (f : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn f (stdSimplex ℝ (Fin 3)) D ∧
      f '' stdSimplexBoundary 2 = J ∧ D ⊆ W ∩ {x | ℓ x = r} := by
  obtain ⟨e, π, hleft, hfixed, heheight⟩ := exists_affine_coordinates_of_linear_fiber hdimE ℓ hℓ r
  have hπinj : InjOn π J := by
    intro x hx y hy hxy
    exact ((hfixed x).mpr (hJr hx)).symm.trans ((congrArg e hxy).trans ((hfixed y).mpr (hJr hy)))
  have hπ : IsPLHomeomorphOn π J (π '' J) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hJ.isPolyhedron
      ((isPiecewiseAffineOn_of_affine π.toAffineMap isOpen_univ).mono_of_isPolyhedron
        hJ.isPolyhedron (subset_univ _))
      ⟨mapsTo_image _ _, hπinj, fun _ h => h⟩
  have hJ' : IsPLSphere 1 (π '' J) := hJ.of_isPLHomeomorphOn hπ
  let A := closure (Schoenflies.inside (π '' J))
  have hA : IsPLBall 2 A := isPLBall_closure_inside_of_isPLSphere_one hJ'
  have hfront : frontier A = π '' J := frontier_closure_inside_of_isPLSphere_one hJ'
  have heπJ : e '' (π '' J) = J := by
    rw [image_image]
    have heq : EqOn (e ∘ π) id J := fun x hx => (hfixed x).mpr (hJr hx)
    exact heq.image_eq.trans (image_id _)
  have heA : IsPLHomeomorphOn e A (e '' A) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hA.isPolyhedron
      ((isPiecewiseAffineOn_of_affine e isOpen_univ).mono_of_isPolyhedron hA.isPolyhedron (subset_univ _))
      ⟨mapsTo_image _ _, hleft.injective.injOn, fun _ h => h⟩
  have hJW' : π '' J ⊆ e ⁻¹' W := by
    rintro y ⟨x, hx, rfl⟩
    change e (π x) ∈ W
    rw [(hfixed x).mpr (hJr hx)]
    exact hJW hx
  have hAW : A ⊆ e ⁻¹' W := Topology.subset_of_isCompact_of_frontier_subset_open_convex
    hA.isPolyhedron.isCompact (hW.preimage e.continuous_of_finiteDimensional)
    (hWconv.affine_preimage e) ((hJ.nonempty.image π).mono hJW') (hfront.trans_le hJW')
  obtain ⟨u, hu⟩ := hA
  refine ⟨e '' A, e ∘ u, hu.trans heA, ?_, ?_⟩
  · rw [image_comp, hu.image_stdSimplexBoundary, hfront, heπJ]
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨hAW hy, heheight y⟩

end DifferentialGeometry.Topology.PiecewiseLinear
