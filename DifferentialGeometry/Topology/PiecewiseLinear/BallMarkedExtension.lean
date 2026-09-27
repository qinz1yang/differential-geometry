import DifferentialGeometry.Topology.PiecewiseLinear.BallStarring

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_isPLHomeomorphOn_extension_marked {m : ℕ} {A : Set E} {A' : Set F}
    {f : (Fin (m + 2) → ℝ) → E} (hf : IsPLHomeomorphOn f (stdSimplex ℝ (Fin (m + 2))) A)
    {f' : (Fin (m + 2) → ℝ) → F} (hf' : IsPLHomeomorphOn f' (stdSimplex ℝ (Fin (m + 2))) A')
    {φ : E → F}
    (hφ : IsPLHomeomorphOn φ
      (f '' (simplexBoundary (stdVertices m) (stdVertices_affineIndependent m)).space)
      (f' '' (simplexBoundary (stdVertices m) (stdVertices_affineIndependent m)).space)) :
    ∃ G : E → F, IsPLHomeomorphOn G A A' ∧
      EqOn G φ (f '' (simplexBoundary (stdVertices m) (stdVertices_affineIndependent m)).space) ∧
      G (f (stdCenter m)) = f' (stdCenter m) := by
  classical
  have hBfin : Finite (simplexBoundary (stdVertices m) (stdVertices_affineIndependent m)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hBsub :
      (simplexBoundary (stdVertices m) (stdVertices_affineIndependent m)).space ⊆
        stdSimplex ℝ (Fin (m + 2)) := simplexBoundary_stdVertices_space_subset m
  have hBpoly :=
    isPolyhedron_space (simplexBoundary (stdVertices m) (stdVertices_affineIndependent m))
  have hfB := hf.restrict hBpoly hBsub
  have hf'B := hf'.restrict hBpoly hBsub
  have hψ := (hfB.trans hφ).trans hf'B.symm
  obtain ⟨Φ, hΦ, hΦeq, hΦc, -⟩ :=
    exists_isPLHomeomorphOn_coneComplex (isConeBase_std m) (isConeBase_std m) hψ
  rw [coneComplex_std_space] at hΦ
  have hcS : stdCenter m ∈ stdSimplex ℝ (Fin (m + 2)) :=
    openSimplex_stdVertices_subset_stdSimplex (stdCenter_mem_openSimplex m)
  refine ⟨f' ∘ (Φ ∘ Function.invFunOn f (stdSimplex ℝ (Fin (m + 2)))),
    (hf.symm.trans hΦ).trans hf', ?_, ?_⟩
  · intro x hx
    obtain ⟨b, hb, rfl⟩ := hx
    have hbS : b ∈ stdSimplex ℝ (Fin (m + 2)) := hBsub hb
    change f' (Φ (Function.invFunOn f (stdSimplex ℝ (Fin (m + 2))) (f b))) = φ (f b)
    rw [hf.bijOn.invOn_invFunOn.1 hbS, hΦeq hb]
    exact hf'B.bijOn.invOn_invFunOn.2 (hφ.bijOn.mapsTo (mem_image_of_mem f hb))
  · change
      f' (Φ (Function.invFunOn f (stdSimplex ℝ (Fin (m + 2))) (f (stdCenter m)))) =
        f' (stdCenter m)
    rw [hf.bijOn.invOn_invFunOn.1 hcS, hΦc]

theorem IsPLHomeomorphOn.image_stdSimplexBoundary_congr {m : ℕ} {P : Set E}
    {f₁ f₂ : (Fin (m + 2) → ℝ) → E}
    (h₁ : IsPLHomeomorphOn f₁ (stdSimplex ℝ (Fin (m + 2))) P)
    (h₂ : IsPLHomeomorphOn f₂ (stdSimplex ℝ (Fin (m + 2))) P) :
    f₁ '' stdSimplexBoundary (m + 1) = f₂ '' stdSimplexBoundary (m + 1) := by
  classical
  obtain ⟨K, hKfin, hKP⟩ := (IsPLBall.isPolyhedron ⟨f₁, h₁⟩).exists_simplicialComplex
  have : Finite K.faces := hKfin.to_subtype
  rw [h₁.image_stdSimplexBoundary_eq_boundaryComplex K hKP,
    h₂.image_stdSimplexBoundary_eq_boundaryComplex K hKP]

end DifferentialGeometry.Topology.PiecewiseLinear
