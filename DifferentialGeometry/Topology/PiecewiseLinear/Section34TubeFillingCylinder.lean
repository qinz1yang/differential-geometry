import DifferentialGeometry.Topology.PiecewiseLinear.Section34TubeSurfaceDisk
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressedFillingCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelRegionTransport

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_cylindrical_model_of_interior_torus_carrier
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (D : Geometry.SimplicialComplex ℝ E)
    (S R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite D.faces] [Finite S.faces] [Finite R.faces] (hD : IsPLBall 2 D.space)
    (hS : IsCombinatorialManifoldWithBoundary 3 S)
    {f : E × ℝ → EuclideanSpace ℝ (Fin 3)} (hf : IsCylindricalDiagram f D.space S.space)
    (hends : ∀ x ∈ D.space, f (x, 0) = f (x, 1))
    (hR : IsCombinatorialManifoldWithBoundary 3 R) (hRS : R.space ⊆ interior S.space)
    (hT : IsPLTorus (frontier R.space))
    (hgen : CarriesFundamentalGroupOnto (frontier R.space) S.space)
    {P : Set F} (hP : IsPLBall 2 P) (hdim : Module.finrank ℝ F = 2) :
    IsTopologicalSolidTorus R.space ∧
      ∃ g : F × ℝ → EuclideanSpace ℝ (Fin 3), IsCylindricalDiagram g P R.space ∧
        (∀ x ∈ P, g (x, 0) = g (x, 1)) ∧
        frontier R.space = g '' (frontier P ×ˢ Icc (0 : ℝ) 1) := by
  have hfront : frontier R.space ⊆ R.space := (isPolyhedron_space R).isClosed.frontier_subset
  obtain ⟨Q, q, hq, hQS, hmeet, hb, hess⟩ :=
    hf.exists_essential_disk_of_interior_torus_carrier D S hD hS hends hT
      (hfront.trans hRS) hgen
  have hne : (frontier R.space).Nonempty :=
    hq.isPLSphere_image_stdSimplexBoundary.nonempty.mono hb
  have hu : IsPLHomeomorphInto 3
      (id : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) (interior S.space) :=
    (isPLHomeomorphInto_id_of_isPolyhedron (isPolyhedron_space S)).mono_of_isOpen
      isOpen_interior interior_subset
  obtain ⟨-, hsolid, -, g, hg, hgend, hgfront⟩ :=
    exists_cylindrical_model_of_essential_disk_and_carrier hP hdim
      (hf.isTopologicalSolidTorus_of_eq_ends hD hends) hgen hne R hR hT isOpen_interior
      hu hRS (by simpa only [image_id] using interior_subset (s := S.space))
      (by simpa only [image_id] using hfront) hq hQS hmeet ⟨hb, hess⟩
  exact ⟨hsolid, g, hg, hgend, hgfront⟩

end DifferentialGeometry.Topology.PiecewiseLinear
