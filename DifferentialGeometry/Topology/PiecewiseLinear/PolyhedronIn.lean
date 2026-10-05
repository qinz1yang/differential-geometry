import DifferentialGeometry.Topology.PiecewiseLinear.ChartPiece
import DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

abbrev PolyhedronIn (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] (P : Set X) : Type u :=
  PLPiece n X P

def IsPolyhedralBall (m : ℕ) (P : Set X) : Prop :=
  ∃ T : PLPiece n X P, IsPLBall m T.piece.complex.space

def IsPolyhedralSphere (m : ℕ) (P : Set X) : Prop :=
  ∃ T : PLPiece n X P, IsPLSphere m T.piece.complex.space

theorem PLPieceIn.isPLHomeomorphOn_chart_image {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {P : Set X} (T : PLPieceIn E n X P)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) (hP : P ⊆ e.source) :
    IsPLHomeomorphOn (e ∘ T.map) T.complex.space (e '' P) := by
  have hfin := T.finite_faces.to_subtype
  have hpl : IsPiecewiseAffineOn (e ∘ T.map) T.complex.space := by
    have h := T.isPiecewiseAffineOn_chart e he
    rwa [inter_eq_left.mpr fun x hx => mem_preimage.mpr (hP (T.bijOn.mapsTo hx))] at h
  have hinj : InjOn (e ∘ T.map) T.complex.space :=
    e.injOn.comp T.bijOn.injOn fun x hx => hP (T.bijOn.mapsTo hx)
  have himg : (e ∘ T.map) '' T.complex.space = e '' P := by
    rw [image_comp, T.bijOn.image_eq]
  obtain ⟨L, -, hL, hpl'⟩ := exists_isPLHomeomorphOn_image T.complex hpl hinj
  rw [hL, himg] at hpl'
  exact hpl'

theorem PLPieceIn.isPolyhedron_chart_image {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {P : Set X} (T : PLPieceIn E n X P)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) (hP : P ⊆ e.source) :
    IsPolyhedron (e '' P) := by
  have hfin := T.finite_faces.to_subtype
  have h := T.isPLHomeomorphOn_chart_image e he hP
  rw [← h.image_eq]
  exact (PiecewiseLinear.isPolyhedron_space T.complex).image_of_isPiecewiseAffineOn
    h.isPiecewiseAffineOn h.bijOn.injOn

theorem IsPolyhedralBall.isPLBall_chart_image {m : ℕ} {P : Set X}
    (hB : IsPolyhedralBall (n := n) m P) (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) (hP : P ⊆ e.source) :
    IsPLBall m (e '' P) := by
  obtain ⟨T, hT⟩ := hB
  exact hT.of_isPLHomeomorphOn (T.piece.isPLHomeomorphOn_chart_image e he hP)

theorem IsPolyhedralSphere.isPLSphere_chart_image {m : ℕ} {P : Set X}
    (hS : IsPolyhedralSphere (n := n) m P)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) (hP : P ⊆ e.source) :
    IsPLSphere m (e '' P) := by
  obtain ⟨T, hT⟩ := hS
  exact hT.of_isPLHomeomorphOn (T.piece.isPLHomeomorphOn_chart_image e he hP)

theorem isPolyhedralBall_of_isPLBall_chart {m : ℕ} [HasGroupoid X (plGroupoid n)]
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsHPolytope C) (hCe : C ⊆ e.target) (hB : IsPLBall m C) :
    IsPolyhedralBall (n := n) m (e.symm '' C) := by
  refine ⟨⟨n, chartPiece e he hC hCe⟩, ?_⟩
  change IsPLBall m (chartPiece e he hC hCe).complex.space
  rw [chartPiece_space]
  exact hB

end DifferentialGeometry.Topology.PiecewiseLinear
