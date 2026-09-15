import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryOfBall
import DifferentialGeometry.Topology.PiecewiseLinear.StdSimplexCone
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundaryImage

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
theorem exists_isPLHomeomorphOn_of_boundaryComplex [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [DecidableEq E] [DecidableEq F]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    (hK : IsPLBall (n + 1) K.space) (hL : IsPLBall (n + 1) L.space) {g : E → F}
    (hg : IsPLHomeomorphOn g (boundaryComplex (n + 1) K).space (boundaryComplex (n + 1) L).space) :
    ∃ G : E → F, IsPLHomeomorphOn G K.space L.space ∧ EqOn G g (boundaryComplex (n + 1) K).space := by
  obtain ⟨f₁, hf₁⟩ := hK
  obtain ⟨f₂, hf₂⟩ := hL
  let B := simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)
  have : Finite B.faces := (simplexBoundary_faces_finite _ _).to_subtype
  have hBsub : B.space ⊆ stdSimplex ℝ (Fin (n + 2)) := simplexBoundary_stdVertices_space_subset n
  have hBK := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hf₁
  have hBL := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex L hf₂
  have hf₁B : IsPLHomeomorphOn f₁ B.space (boundaryComplex (n + 1) K).space := by
    rw [hBK]
    exact hf₁.restrict (isPolyhedron_space B) hBsub
  have hf₂B : IsPLHomeomorphOn f₂ B.space (boundaryComplex (n + 1) L).space := by
    rw [hBL]
    exact hf₂.restrict (isPolyhedron_space B) hBsub
  have hb := (hf₁B.trans hg).trans hf₂B.symm
  obtain ⟨H, hH, hHb, -, -⟩ := exists_isPLHomeomorphOn_coneComplex
    (isConeBase_std n) (isConeBase_std n) hb
  rw [coneComplex_std_space] at hH
  refine ⟨_, (hf₁.symm.trans hH).trans hf₂, ?_⟩
  intro x hx
  rw [hBK] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  change f₂ (H (Function.invFunOn f₁ (stdSimplex ℝ (Fin (n + 2))) (f₁ z))) = g (f₁ z)
  rw [hf₁.bijOn.invOn_invFunOn.1 (hBsub hz), hHb hz]
  exact hf₂B.bijOn.invOn_invFunOn.2 (hg.bijOn.mapsTo (hf₁B.bijOn.mapsTo hz))

theorem exists_isPLHomeomorphOn_of_stdSimplexBoundary
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {n : ℕ} {P : Set E} {Q : Set F}
    {fP : (Fin (n + 2) → ℝ) → E} {fQ : (Fin (n + 2) → ℝ) → F}
    (hfP : IsPLHomeomorphOn fP (stdSimplex ℝ (Fin (n + 2))) P)
    (hfQ : IsPLHomeomorphOn fQ (stdSimplex ℝ (Fin (n + 2))) Q) {g : E → F}
    (hg : IsPLHomeomorphOn g (fP '' stdSimplexBoundary (n + 1))
      (fQ '' stdSimplexBoundary (n + 1))) :
    ∃ G : E → F, IsPLHomeomorphOn G P Q ∧ EqOn G g (fP '' stdSimplexBoundary (n + 1)) := by
  classical
  let _ : DecidableEq E := Classical.decEq _
  let _ : DecidableEq F := Classical.decEq _
  have hP : IsPLBall (n + 1) P := ⟨fP, hfP⟩
  have hQ : IsPLBall (n + 1) Q := ⟨fQ, hfQ⟩
  obtain ⟨K, hfinK, hKspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hfinL, hLspace⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hfinK.to_subtype
  let _ : Finite L.faces := hfinL.to_subtype
  have hfK : IsPLHomeomorphOn fP (stdSimplex ℝ (Fin (n + 2))) K.space := hKspace.symm ▸ hfP
  have hfL : IsPLHomeomorphOn fQ (stdSimplex ℝ (Fin (n + 2))) L.space := hLspace.symm ▸ hfQ
  have hBK := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hfK
  have hBL := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex L hfL
  rw [simplexBoundary_stdVertices_space] at hBK hBL
  have hg' : IsPLHomeomorphOn g (boundaryComplex (n + 1) K).space
      (boundaryComplex (n + 1) L).space := by rw [hBK, hBL]; exact hg
  obtain ⟨G, hG, hGg⟩ := exists_isPLHomeomorphOn_of_boundaryComplex K L ⟨fP, hfK⟩ ⟨fQ, hfL⟩ hg'
  rw [hKspace, hLspace] at hG
  rw [hBK] at hGg
  exact ⟨G, hG, hGg⟩

end DifferentialGeometry.Topology.PiecewiseLinear
