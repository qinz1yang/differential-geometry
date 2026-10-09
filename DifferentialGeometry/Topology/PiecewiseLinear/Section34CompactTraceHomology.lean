/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.NonseparatingPolygonCarrier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_simplicialComplex_subcomplex_of_isPolyhedron {P Q : Set E3} (hP : IsPolyhedron P)
    (hQ : IsPolyhedron Q) (hQP : Q ⊆ P) :
    ∃ A B : Geometry.SimplicialComplex ℝ E3, A.faces.Finite ∧ B.faces ⊆ A.faces ∧
      A.space = P ∧ B.space = Q := by
  obtain ⟨A₀, hA₀fin, hA₀sp⟩ := hP.exists_simplicialComplex
  obtain ⟨G, hGfin, hGsp⟩ := hQ.exists_simplicialComplex
  have : Finite A₀.faces := hA₀fin.to_subtype
  have : Finite G.faces := hGfin.to_subtype
  obtain ⟨A, hA, hAfin, hGA⟩ := exists_isSubdivision_restrict_isSubdivision A₀ G
    (by rw [hGsp, hA₀sp]; exact hQP)
  exact ⟨A, restrict A G.space, hAfin, restrict_faces_subset A _, hA.space_eq.trans hA₀sp,
    hGA.space_eq.trans hGsp⟩

section Leaves

variable {C V : Set (EuclideanSpace ℝ (Fin 3))}
  {h f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
  {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {env : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}

theorem compactTraceHomology
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    (henv : Section34CompactFaceEnvelopes K K' h H (section34CompactVertexBallImage src f₁)
      env)
    (s : Section34CompactSimplexIndex K 3)
    (hgen : CarriesFundamentalGroupOnto (h '' section34CompactSimplexRim s.1)
      (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))
    {B BBd : Set (EuclideanSpace ℝ (Fin 3))}
    (hB : IsPLCellOn 3 B BBd) (hrim : h '' section34CompactSimplexRim s.1 ⊆ interior B)
    (hBenv : B ⊆ env s) :
    CarriesIntegralFirstHomologyOnto
      (BBd ∩ frontier (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s))
      (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) := by
  obtain ⟨-, -, -, -, -, -, -, -, hnest, -, -⟩ := hgraph
  obtain ⟨S₁, S₂, -, -, hT, -⟩ := hnest s
  obtain ⟨-, -, -, -, -, haux, -⟩ := henv
  obtain ⟨A, hA, hRA, hAT⟩ := haux s
  have hTpoly := hT.isPolyhedron
  have hR : CarriesFirstHomologyOnto (h '' section34CompactSimplexRim s.1)
      (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) :=
    hgen.carriesFirstHomologyOnto
      ((section34CompactSimplexRim_nonempty (by rw [s.2.2]; norm_num)).image h)
      hT.1.isPathConnected
  have hBA : B ∩ A ⊆
      interior (section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s) :=
    fun y hy => hAT ⟨hBenv hy.1, hy.2⟩
  have hint := hB.carriesFirstHomologyOnto_inter_interior hA.isPLCellOn_frontier.isCompact
    hA.isPLCellOn_frontier.subsingleton_integralSingularHomology_one
    (hRA.trans interior_subset) hrim hBA hR
  have hBdpoly : IsPolyhedron BBd := by
    rw [hB.boundary_eq_frontier]
    exact hB.isPLBall_three.isPLSphere_frontier.isPolyhedron
  obtain ⟨Ac, Bc, hAcfin, hBcAc, hAcsp, hBcsp⟩ :=
    exists_simplicialComplex_subcomplex_of_isPolyhedron (hBdpoly.inter hTpoly)
      (hBdpoly.inter hTpoly.frontier) (inter_subset_inter_right _ hTpoly.isClosed.frontier_subset)
  have : Finite Ac.faces := hAcfin.to_subtype
  have hfinal := hint.inter_frontier_of_chart hBdpoly.isClosed hTpoly.isClosed
    hB.subsingleton_integralSingularHomology_one_boundary
    (c := chartAt E3 (0 : E3)) (by rw [chartAt_self_eq]; exact subset_univ _) Ac Bc hBcAc
    (by rw [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, image_id]; exact hAcsp)
    (by rw [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, image_id]; exact hBcsp)
  exact hfinal

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
