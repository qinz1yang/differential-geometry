import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronIn

open Set
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [HasGroupoid X (plGroupoid n)]
  (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))

noncomputable def chartPieceOfComplex (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X)
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) [Finite K.faces]
    (hK : K.space ⊆ e.target) : PLPieceIn (EuclideanSpace ℝ (Fin n)) n X (e.symm '' K.space) where
  complex := K
  finite_faces := Set.toFinite K.faces
  map := e.symm
  bijOn := (injOn_symm_of_subset_target e hK).bijOn_image
  continuousOn := e.continuousOn_symm.mono hK
  isPiecewiseAffineOn_chart :=
    isPiecewiseAffineOn_chart_symm_chart_of_isPolyhedron e he (isPolyhedron_space K) hK
  isPiecewiseAffineOn_chart_symm :=
    isPiecewiseAffineOn_chart_chart_symm_of_isPolyhedron e he (isPolyhedron_space K) hK

theorem isPolyhedralBall_chart_symm_image (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X)
    {m : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))} (hC : IsPLBall m C) (hCe : C ⊆ e.target) :
    IsPolyhedralBall (n := n) m (e.symm '' C) := by
  obtain ⟨K, hfin, hKspace⟩ := hC.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hfin.to_subtype
  rw [← hKspace]
  exact ⟨⟨n, chartPieceOfComplex e he K (hKspace.symm ▸ hCe)⟩, hKspace.symm ▸ hC⟩

theorem isPolyhedralSphere_chart_symm_image (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X)
    {m : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))} (hC : IsPLSphere m C) (hCe : C ⊆ e.target) :
    IsPolyhedralSphere (n := n) m (e.symm '' C) := by
  obtain ⟨K, hfin, hKspace⟩ := hC.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hfin.to_subtype
  rw [← hKspace]
  exact ⟨⟨n, chartPieceOfComplex e he K (hKspace.symm ▸ hCe)⟩, hKspace.symm ▸ hC⟩

end DifferentialGeometry.Topology.PiecewiseLinear
