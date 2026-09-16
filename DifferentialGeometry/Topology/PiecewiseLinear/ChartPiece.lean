import DifferentialGeometry.Topology.PiecewiseLinear.PieceRestrict
import DifferentialGeometry.Topology.PiecewiseLinear.Groupoid

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

noncomputable def chartComplex {C : Set (EuclideanSpace ℝ (Fin n))} (hC : IsHPolytope C) :
    Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)) :=
  hC.isPolyhedron.exists_simplicialComplex.choose

theorem chartComplex_faces_finite {C : Set (EuclideanSpace ℝ (Fin n))} (hC : IsHPolytope C) :
    (chartComplex hC).faces.Finite :=
  hC.isPolyhedron.exists_simplicialComplex.choose_spec.1

theorem chartComplex_space {C : Set (EuclideanSpace ℝ (Fin n))} (hC : IsHPolytope C) :
    (chartComplex hC).space = C :=
  hC.isPolyhedron.exists_simplicialComplex.choose_spec.2

variable (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))

omit [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] in
theorem injOn_symm_of_subset_target {C : Set (EuclideanSpace ℝ (Fin n))} (hCe : C ⊆ e.target) :
    InjOn e.symm C :=
  e.symm.injOn.mono (by
    rw [OpenPartialHomeomorph.symm_source]
    exact hCe)

theorem isPiecewiseAffineOn_chart_symm_chart_of_isPolyhedron [HasGroupoid X (plGroupoid n)]
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsPolyhedron C) (hCe : C ⊆ e.target) (e' : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he' : e' ∈ atlas (EuclideanSpace ℝ (Fin n)) X) :
    IsPiecewiseAffineOn (e' ∘ e.symm) (C ∩ e.symm ⁻¹' e'.source) := by
  have hpl : IsPiecewiseAffineOn (e.symm ≫ₕ e') (e.target ∩ e.symm ⁻¹' e'.source) := by
    have h := (mem_plGroupoid_iff.mp (StructureGroupoid.compatible (plGroupoid n) he he')).1
    rwa [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at h
  have h := hpl.inter_of_isPolyhedron hC
  have hdom : e.target ∩ e.symm ⁻¹' e'.source ∩ C = C ∩ e.symm ⁻¹' e'.source := by
    ext y
    constructor
    · rintro ⟨⟨-, hy⟩, hyC⟩
      exact ⟨hyC, hy⟩
    · rintro ⟨hyC, hy⟩
      exact ⟨⟨hCe hyC, hy⟩, hyC⟩
  rw [hdom] at h
  exact h.congr fun _ _ => rfl

theorem isPiecewiseAffineOn_chart_chart_symm_of_isPolyhedron [HasGroupoid X (plGroupoid n)]
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsPolyhedron C) (hCe : C ⊆ e.target) (e' : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he' : e' ∈ atlas (EuclideanSpace ℝ (Fin n)) X) :
    IsPiecewiseAffineOn (Function.invFunOn e.symm C ∘ e'.symm)
      (e'.target ∩ e'.symm ⁻¹' (e.symm '' C)) := by
  have hpl : IsPiecewiseAffineOn (e'.symm ≫ₕ e) (e'.target ∩ e'.symm ⁻¹' e.source) := by
    have h := (mem_plGroupoid_iff.mp (StructureGroupoid.compatible (plGroupoid n) he' he)).1
    rwa [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at h
  have h := hpl.inter_preimage_of_isPolyhedron hC
  have himg : e.symm '' C = e.source ∩ e ⁻¹' C := e.symm_image_eq_source_inter_preimage hCe
  have hdom : e'.target ∩ e'.symm ⁻¹' e.source ∩ (e'.symm ≫ₕ e) ⁻¹' C =
      e'.target ∩ e'.symm ⁻¹' (e.symm '' C) := by
    rw [himg]
    ext y
    simp only [mem_inter_iff, mem_preimage, OpenPartialHomeomorph.trans_apply]
    tauto
  rw [hdom] at h
  refine h.congr fun y hy => ?_
  obtain ⟨-, hy⟩ := hy
  rw [mem_preimage, himg] at hy
  change Function.invFunOn e.symm C (e'.symm y) = e (e'.symm y)
  calc
    Function.invFunOn e.symm C (e'.symm y) = Function.invFunOn e.symm C (e.symm (e (e'.symm y))) := by
      rw [e.left_inv hy.1]
    _ = e (e'.symm y) := (injOn_symm_of_subset_target e hCe).leftInvOn_invFunOn hy.2

theorem isPiecewiseAffineOn_chart_symm_chart [HasGroupoid X (plGroupoid n)]
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsHPolytope C) (hCe : C ⊆ e.target) (e' : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he' : e' ∈ atlas (EuclideanSpace ℝ (Fin n)) X) :
    IsPiecewiseAffineOn (e' ∘ e.symm) (C ∩ e.symm ⁻¹' e'.source) :=
  isPiecewiseAffineOn_chart_symm_chart_of_isPolyhedron e he hC.isPolyhedron hCe e' he'

theorem isPiecewiseAffineOn_chart_chart_symm [HasGroupoid X (plGroupoid n)]
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsHPolytope C) (hCe : C ⊆ e.target) (e' : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (he' : e' ∈ atlas (EuclideanSpace ℝ (Fin n)) X) :
    IsPiecewiseAffineOn (Function.invFunOn e.symm C ∘ e'.symm)
      (e'.target ∩ e'.symm ⁻¹' (e.symm '' C)) :=
  isPiecewiseAffineOn_chart_chart_symm_of_isPolyhedron e he hC.isPolyhedron hCe e' he'

noncomputable def chartPiece [HasGroupoid X (plGroupoid n)]
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsHPolytope C) (hCe : C ⊆ e.target) :
    PLPieceIn (EuclideanSpace ℝ (Fin n)) n X (e.symm '' C) where
  complex := chartComplex hC
  finite_faces := chartComplex_faces_finite hC
  map := e.symm
  bijOn := by
    rw [chartComplex_space]
    exact (injOn_symm_of_subset_target e hCe).bijOn_image
  continuousOn := by
    rw [chartComplex_space]
    exact e.continuousOn_symm.mono hCe
  isPiecewiseAffineOn_chart := fun e' he' => by
    rw [chartComplex_space]
    exact isPiecewiseAffineOn_chart_symm_chart e he hC hCe e' he'
  isPiecewiseAffineOn_chart_symm := fun e' he' => by
    rw [chartComplex_space]
    exact isPiecewiseAffineOn_chart_chart_symm e he hC hCe e' he'

theorem chartPiece_map [HasGroupoid X (plGroupoid n)] (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X)
    {C : Set (EuclideanSpace ℝ (Fin n))} (hC : IsHPolytope C) (hCe : C ⊆ e.target) :
    (chartPiece e he hC hCe).map = e.symm := rfl

theorem chartPiece_space [HasGroupoid X (plGroupoid n)]
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin n)) X) {C : Set (EuclideanSpace ℝ (Fin n))}
    (hC : IsHPolytope C) (hCe : C ⊆ e.target) : (chartPiece e he hC hCe).complex.space = C :=
  chartComplex_space hC

theorem exists_isHPolytope_image_symm_mem_nhds (x : X) :
    ∃ C : Set (EuclideanSpace ℝ (Fin n)), IsHPolytope C ∧
      C ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x).target ∧
      (chartAt (EuclideanSpace ℝ (Fin n)) x).symm '' C ∈ 𝓝 x := by
  have hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := mem_chart_source _ x
  obtain ⟨C, hC, hCe, hCnhds⟩ := exists_isHPolytope_subset_mem_nhds
    ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_target.mem_nhds
      ((chartAt (EuclideanSpace ℝ (Fin n)) x).map_source hx))
  refine ⟨C, hC, hCe, ?_⟩
  rw [(chartAt (EuclideanSpace ℝ (Fin n)) x).symm_image_eq_source_inter_preimage hCe]
  exact Filter.inter_mem ((chartAt (EuclideanSpace ℝ (Fin n)) x).open_source.mem_nhds hx)
    (((chartAt (EuclideanSpace ℝ (Fin n)) x).continuousAt hx).preimage_mem_nhds hCnhds)

end DifferentialGeometry.Topology.PiecewiseLinear
