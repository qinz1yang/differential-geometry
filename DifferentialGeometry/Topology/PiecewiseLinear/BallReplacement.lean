import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundaryImage
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsPLHomeomorphOn.isPLSphere_image_stdSimplexBoundary {n : ℕ} {P : Set E}
    {f : (Fin (n + 2) → ℝ) → E}
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) P) :
    IsPLSphere n (f '' stdSimplexBoundary (n + 1)) := by
  classical
  let B := simplexBoundary (stdVertices n) (stdVertices_affineIndependent n)
  let _ : Finite B.faces := (simplexBoundary_faces_finite _ _).to_subtype
  have h := (isPLSphere_simplexBoundary_std n).of_isPLHomeomorphOn
    (hf.restrict (isPolyhedron_space B) (simplexBoundary_stdVertices_space_subset n))
  rwa [simplexBoundary_stdVertices_space] at h

theorem exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary {n : ℕ} {P : Set E} {Q : Set F}
    {f : (Fin (n + 2) → ℝ) → E} {g : (Fin (n + 2) → ℝ) → F}
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) P)
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin (n + 2))) Q) {b : E → F}
    (hb : IsPLHomeomorphOn b (f '' stdSimplexBoundary (n + 1)) (g '' stdSimplexBoundary (n + 1))) :
    ∃ H : E → F, IsPLHomeomorphOn H P Q ∧ EqOn H b (f '' stdSimplexBoundary (n + 1)) := by
  classical
  have hP : IsPLBall (n + 1) P := ⟨f, hf⟩
  have hQ : IsPLBall (n + 1) Q := ⟨g, hg⟩
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hLfin, hLQ⟩ := hQ.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hfK : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) K.space := hKP.symm ▸ hf
  have hgL : IsPLHomeomorphOn g (stdSimplex ℝ (Fin (n + 2))) L.space := hLQ.symm ▸ hg
  have hKboundary := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hfK
  have hLboundary := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex L hgL
  rw [simplexBoundary_stdVertices_space] at hKboundary hLboundary
  have hbKL : IsPLHomeomorphOn b (boundaryComplex (n + 1) K).space (boundaryComplex (n + 1) L).space := by
    rwa [hKboundary, hLboundary]
  obtain ⟨H, hH, hHb⟩ := exists_isPLHomeomorphOn_of_boundaryComplex K L
    (⟨f, hfK⟩ : IsPLBall (n + 1) K.space) (⟨g, hgL⟩ : IsPLBall (n + 1) L.space) hbKL
  rw [hKP, hLQ] at hH
  rw [hKboundary] at hHb
  exact ⟨H, hH, hHb⟩

theorem exists_isPLHomeomorphOn_replace_ball {n : ℕ} {P Q R J : Set E}
    (hP : IsPolyhedron P) {f g : (Fin (n + 2) → ℝ) → E}
    (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (n + 2))) Q)
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin (n + 2))) R)
    (hfJ : f '' stdSimplexBoundary (n + 1) = J) (hgJ : g '' stdSimplexBoundary (n + 1) = J)
    (hPQ : P ∩ Q = J) (hPR : P ∩ R = J) :
    ∃ H : E → E, IsPLHomeomorphOn H (P ∪ Q) (P ∪ R) ∧ EqOn H id P := by
  have hQ : IsPLBall (n + 1) Q := ⟨f, hf⟩
  have hJ : IsPolyhedron J := hPQ ▸ hP.inter hQ.isPolyhedron
  have hJid : IsPLHomeomorphOn (id : E → E)
      (f '' stdSimplexBoundary (n + 1)) (g '' stdSimplexBoundary (n + 1)) := by
    rw [hfJ, hgJ]
    exact hJ.isPLHomeomorphOn_id
  obtain ⟨G, hG, hGJ⟩ := exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary hf hg hJid
  rw [hfJ] at hGJ
  have hfg : EqOn id G (P ∩ Q) := by
    rw [hPQ]
    exact hGJ.symm
  have hinter : SurjOn (id : E → E) (P ∩ Q) (P ∩ R) := by
    rw [hPQ, hPR]
    exact surjOn_id J
  obtain ⟨H, hH, hHP, -⟩ := exists_isPLHomeomorphOn_union hP hQ.isPolyhedron
    hP.isPLHomeomorphOn_id hG hfg hinter
  exact ⟨H, hH, hHP⟩

end DifferentialGeometry.Topology.PiecewiseLinear
