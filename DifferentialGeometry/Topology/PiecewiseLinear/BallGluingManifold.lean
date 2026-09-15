import DifferentialGeometry.Topology.PiecewiseLinear.BallGluing
import DifferentialGeometry.Topology.PiecewiseLinear.PieceInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralBallTopology

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isPolyhedralBall_union_of_boundary_disk_in_piece {Y C₁ C₂ : Set X}
    (T : PLPieceIn E 3 X Y) (h₁ : IsPolyhedralBall (n := 3) 3 C₁)
    (h₂ : IsPolyhedralBall (n := 3) 3 C₂) (hD : IsPolyhedralBall (n := 3) 2 (C₁ ∩ C₂))
    (hD₁ : C₁ ∩ C₂ ⊆ frontier C₁) (hD₂ : C₁ ∩ C₂ ⊆ frontier C₂)
    (hCY : C₁ ∪ C₂ ⊆ Y) : IsPolyhedralBall (n := 3) 3 (C₁ ∪ C₂) := by
  classical
  let _ : DecidableEq E := Classical.decEq _
  have h₁Y : C₁ ⊆ Y := subset_union_left.trans hCY
  have h₂Y : C₂ ⊆ Y := subset_union_right.trans hCY
  obtain ⟨S₁, hspace₁, hmap₁⟩ := T.exists_restrict_of_isPolyhedralBall h₁ h₁Y
  obtain ⟨S₂, hspace₂, hmap₂⟩ := T.exists_restrict_of_isPolyhedralBall h₂ h₂Y
  let _ : Finite S₁.complex.faces := S₁.finite_faces.to_subtype
  let _ : Finite S₂.complex.faces := S₂.finite_faces.to_subtype
  have hK₁ : IsPLBall 3 S₁.complex.space := hspace₁.symm ▸ h₁.isPLBall_inter_preimage T h₁Y
  have hK₂ : IsPLBall 3 S₂.complex.space := hspace₂.symm ▸ h₂.isPLBall_inter_preimage T h₂Y
  have hinter : S₁.complex.space ∩ S₂.complex.space =
      T.complex.space ∩ T.map ⁻¹' (C₁ ∩ C₂) := by
    rw [hspace₁, hspace₂]
    ext x
    simp only [mem_inter_iff, mem_preimage]
    tauto
  have hKD : IsPLBall 2 (S₁.complex.space ∩ S₂.complex.space) := by
    rw [hinter]
    exact hD.isPLBall_inter_preimage T (inter_subset_left.trans h₁Y)
  have hDK₁ : S₁.complex.space ∩ S₂.complex.space ⊆ (boundaryComplex 3 S₁.complex).space := by
    intro x hx
    have hxC₁ : T.map x ∈ C₁ := (hspace₁ ▸ hx.1).2
    have hxC₂ : T.map x ∈ C₂ := (hspace₂ ▸ hx.2).2
    have hxfront : S₁.map x ∈ frontier C₁ := by rw [hmap₁]; exact hD₁ ⟨hxC₁, hxC₂⟩
    rw [S₁.frontier_eq_image_boundaryComplex hK₁.isCombinatorialManifoldWithBoundary] at hxfront
    obtain ⟨y, hy, hyx⟩ := hxfront
    exact S₁.bijOn.injOn (boundaryComplex_space_subset 3 S₁.complex hy) hx.1 hyx ▸ hy
  have hDK₂ : S₁.complex.space ∩ S₂.complex.space ⊆ (boundaryComplex 3 S₂.complex).space := by
    intro x hx
    have hxC₁ : T.map x ∈ C₁ := (hspace₁ ▸ hx.1).2
    have hxC₂ : T.map x ∈ C₂ := (hspace₂ ▸ hx.2).2
    have hxfront : S₂.map x ∈ frontier C₂ := by rw [hmap₂]; exact hD₂ ⟨hxC₁, hxC₂⟩
    rw [S₂.frontier_eq_image_boundaryComplex hK₂.isCombinatorialManifoldWithBoundary] at hxfront
    obtain ⟨y, hy, hyx⟩ := hxfront
    exact S₂.bijOn.injOn (boundaryComplex_space_subset 3 S₂.complex hy) hx.2 hyx ▸ hy
  have hball := isPLBall_union_of_boundary_disk S₁.complex S₂.complex hK₁ hK₂ hKD hDK₁ hDK₂
  have hsub : S₁.complex.space ∪ S₂.complex.space ⊆ T.complex.space := by
    rw [hspace₁, hspace₂]
    exact union_subset inter_subset_left inter_subset_left
  have himage₁ : T.map '' S₁.complex.space = C₁ := by rw [← hmap₁]; exact S₁.bijOn.image_eq
  have himage₂ : T.map '' S₂.complex.space = C₂ := by rw [← hmap₂]; exact S₂.bijOn.image_eq
  have h := T.isPolyhedralBall_image hball hsub
  rwa [image_union, himage₁, himage₂] at h

theorem isPolyhedralBall_union_of_inter_isPolyhedralBall_two
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 3 K) :
    letI := combinatorialChartedSpace K hK
    ∀ {C₁ C₂ : Set K.space}, IsPolyhedralBall (n := 3) 3 C₁ → IsPolyhedralBall (n := 3) 3 C₂ →
      IsPolyhedralBall (n := 3) 2 (C₁ ∩ C₂) → C₁ ∩ C₂ ⊆ frontier C₁ →
      C₁ ∩ C₂ ⊆ frontier C₂ → IsPolyhedralBall (n := 3) 3 (C₁ ∪ C₂) := by
  let _ := combinatorialChartedSpace K hK
  intro C₁ C₂ h₁ h₂ hD hD₁ hD₂
  obtain ⟨p, -⟩ := h₁.nonempty
  exact isPolyhedralBall_union_of_boundary_disk_in_piece (combinatorialPLPieceIn K hK p)
    h₁ h₂ hD hD₁ hD₂ (subset_univ _)

end DifferentialGeometry.Topology.PiecewiseLinear
