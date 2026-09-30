/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.StarSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.IsomorphicSubdivision

open Set
open LeanEval.Topology.ClassificationOfSurfaces.Moise
  (Plane standardTrianglePosition standardTrianglePosition_affineIndependent)

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [DecidableEq E]

theorem exists_isSubdivision_subcomplex_isGlueIso_planar
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {D : Set E} (hD : IsPLBall 2 D) (hDK : D ⊆ K.space) :
    ∃ (R A : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ Plane)
      (φ : E → Plane) (ψ : Plane → E),
      IsSubdivision R K ∧ R.faces.Finite ∧ A.faces ⊆ R.faces ∧ A.faces.Finite ∧
      A.space = D ∧ L.faces.Finite ∧ IsPLBall 2 L.space ∧ IsGlueIso A L φ ψ ∧
      ∀ s ∈ R.faces, ∃ v ∈ K.vertices, (⋃ w ∈ s, closedStar R w) ⊆ openStar K v := by
  classical
  obtain ⟨R₀, hR₀, hR₀fin, hD₀, hstars₀⟩ :=
    exists_isSubdivision_subcomplexes_closedStars_subset_openStar K
      (fun _ : Unit => D) (fun _ => hD.isPolyhedron) (fun _ => hDK)
  let _ : Finite R₀.faces := hR₀fin.to_subtype
  let A₀ := restrict R₀ D
  let _ : Finite A₀.faces := (restrict_faces_finite R₀ D).to_subtype
  have hA₀ : A₀.space = D := hD₀ ()
  let Q : Set Plane := convexHull ℝ (range standardTrianglePosition)
  have hQ : IsPLBall 2 Q := isPLBall_two_of_isTriangle
    ⟨standardTrianglePosition, standardTrianglePosition_affineIndependent, rfl⟩
  obtain ⟨C, hCfin, hCspace⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite C.faces := hCfin.to_subtype
  obtain ⟨f, hf⟩ := hD
  obtain ⟨g, hg⟩ := hQ
  let φ := g ∘ Function.invFunOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
  have hφ : IsPLHomeomorphOn φ A₀.space C.space := by
    rw [hA₀, hCspace]
    exact hf.symm.trans hg
  obtain ⟨A, L, ψ, hA, hAfin, hL, hLfin, hiso, -⟩ :=
    exists_isGlueIso_of_isPLHomeomorphOn A₀ C hφ
  let _ : Finite A.faces := hAfin.to_subtype
  have hc := centroid_mem_openSimplex_of_mem_faces R₀
  let R := relDerived (restrict_faces_subset R₀ D) hA hc
  have hR : IsSubdivision R R₀ := relDerived_isSubdivision _ _ _
  have hAR : A.faces ⊆ R.faces := faces_subset_relDerived _ _ _
  have hRfin : R.faces.Finite := relDerived_faces_finite _ _ _
  have hAL : IsPLBall 2 L.space := by
    rw [hL.space_eq, hCspace]
    exact ⟨g, hg⟩
  have hcover₀ : ∀ t ∈ R₀.faces,
      ∃ v : K.vertices, (⋃ w ∈ t, closedStar R₀ w) ⊆ openStar K v := by
    intro t ht
    obtain ⟨v, hv, hvt⟩ := hstars₀ t ht
    exact ⟨⟨v, hv⟩, hvt⟩
  refine ⟨R, A, L, φ, ψ, hR.trans hR₀, hRfin, hAR, hAfin,
    hA.space_eq.trans hA₀, hLfin, hAL, hiso, ?_⟩
  intro s hs
  obtain ⟨v, hv⟩ := hR.closedStars_subset_cover hcover₀ s hs
  exact ⟨v, v.property, hv⟩

theorem exists_isSubdivision_isGlueIso_planar [DecidableEq Plane]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space) :
    ∃ (A : Geometry.SimplicialComplex ℝ E) (L : Geometry.SimplicialComplex ℝ Plane)
      (φ : E → Plane) (ψ : Plane → E), IsSubdivision A K ∧ A.faces.Finite ∧
        L.faces.Finite ∧ IsPLBall 2 L.space ∧ IsGlueIso A L φ ψ := by
  classical
  let Q : Set Plane := convexHull ℝ (range standardTrianglePosition)
  have hQ : IsPLBall 2 Q := isPLBall_two_of_isTriangle
    ⟨standardTrianglePosition, standardTrianglePosition_affineIndependent, rfl⟩
  obtain ⟨C, hCfin, hCspace⟩ := hQ.isPolyhedron.exists_simplicialComplex
  have : Finite C.faces := hCfin.to_subtype
  obtain ⟨f, hf⟩ := hK
  obtain ⟨g, hg⟩ := hQ
  have hφ : IsPLHomeomorphOn (g ∘ Function.invFunOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))) K.space C.space := by
    rw [hCspace]
    exact hf.symm.trans hg
  obtain ⟨A, L, ψ, hA, hAfin, hL, hLfin, hiso, -⟩ := exists_isGlueIso_of_isPLHomeomorphOn K C hφ
  refine ⟨A, L, _, ψ, hA, hAfin, hLfin, ?_, hiso⟩
  rw [hL.space_eq, hCspace]
  exact ⟨g, hg⟩

end DifferentialGeometry.Topology.PiecewiseLinear
