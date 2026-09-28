import DifferentialGeometry.Topology.PiecewiseLinear.Section34DisjointMeridianPullback
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PeriodicMeridianAlignment

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsCylindricalDiagram.exists_aligned_disk_of_disjoint_essential_meridian
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces] (hD : IsPLBall 2 D.space)
    {f : E × ℝ → F} {S J : Set F} (hf : IsCylindricalDiagram f D.space S)
    (hends : ∀ x ∈ D.space, f (x, 0) = f (x, 1)) (hJ : IsPLSphere 1 J)
    (hJside : J ⊆ f '' ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1))
    (hdis : Disjoint J (f '' (D.space ×ˢ ({0} : Set ℝ))))
    (hnon : ¬ (⟨inclusion hJside, continuous_inclusion hJside⟩ :
      C(J, f '' ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1))).Nullhomotopic) :
    ∃ (H : F → F) (q : (Fin 3 → ℝ) → F), IsPLHomeomorphOn H S S ∧
      EqOn H id (f '' ((boundaryComplex 2 D).space ×ˢ {0})) ∧
      IsCylindricalDiagram (H ∘ f) D.space S ∧
      (∀ x ∈ D.space, (H ∘ f) (x, 0) = (H ∘ f) (x, 1)) ∧
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) ((H ∘ f) '' (D.space ×ˢ {1 / 2})) ∧
      q '' stdSimplexBoundary 2 = J ∧ ((H ∘ f) '' (D.space ×ˢ {1 / 2})) ⊆ S := by
  obtain ⟨K, hK, hKA, hfK, hess⟩ :=
    hf.exists_essential_lateral_pullback_of_disjoint_seam D hD hJ hJside hdis hnon
  obtain ⟨H, q, hH, hfix, hg, hgends, hq, hqK, hQS⟩ :=
    hf.exists_aligned_meridian_disk D hD hends hK hKA hess
  exact ⟨H, q, hH, hfix, hg, hgends, hq, hqK.trans hfK.image_eq, hQS⟩

open Classical in
theorem IsCylindricalDiagram.exists_original_meridian_disk_of_disjoint_image
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces] (hD : IsPLBall 2 D.space)
    {f : E × ℝ → F} {S J : Set F} (hf : IsCylindricalDiagram f D.space S)
    (hends : ∀ x ∈ D.space, f (x, 0) = f (x, 1))
    {σ : F → F} (hσ : IsPLHomeomorphOn σ S S) (hJ : IsPLSphere 1 J) (hJS : J ⊆ S)
    (hJside : σ '' J ⊆ f '' ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1))
    (hdis : Disjoint (σ '' J) (f '' (D.space ×ˢ ({0} : Set ℝ))))
    (hnon : ¬ (⟨inclusion hJside, continuous_inclusion hJside⟩ :
      C(σ '' J, f '' ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1))).Nullhomotopic) :
    ∃ (H : F → F) (q : (Fin 3 → ℝ) → F), IsPLHomeomorphOn H S S ∧
      IsCylindricalDiagram (H ∘ f) D.space S ∧
      (∀ x ∈ D.space, (H ∘ f) (x, 0) = (H ∘ f) (x, 1)) ∧
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) ((H ∘ f) '' (D.space ×ˢ {1 / 2})) ∧
      q '' stdSimplexBoundary 2 = J ∧ ((H ∘ f) '' (D.space ×ˢ {1 / 2})) ⊆ S := by
  have hσJ : IsPLSphere 1 (σ '' J) :=
    hJ.of_isPLHomeomorphOn (hσ.restrict hJ.isPolyhedron hJS)
  obtain ⟨H, q, hH, -, -, -, hq, hqJ, hQS⟩ :=
    hf.exists_aligned_disk_of_disjoint_essential_meridian D hD hends hσJ hJside hdis hnon
  let τ := Function.invFunOn σ S
  let U := τ ∘ H
  have hU : IsPLHomeomorphOn U S S := hH.trans hσ.symm
  have hg := hf.postcomp_equivalence hU
  have hq' : IsPLHomeomorphOn (τ ∘ q) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
      ((U ∘ f) '' (D.space ×ˢ {1 / 2})) := by
    have ht := hq.trans (hσ.symm.restrict (IsPLBall.isPolyhedron ⟨q, hq⟩) hQS)
    rw [← image_comp] at ht
    exact ht
  refine ⟨U, τ ∘ q, hU, hg, fun x hx => congrArg U (hends x hx), hq', ?_, ?_⟩
  · rw [image_comp, hqJ, ← image_comp]
    exact (show EqOn (τ ∘ σ) id J from fun x hx =>
      hσ.bijOn.invOn_invFunOn.1 (hJS hx)).image_eq.trans (image_id J)
  · rw [← hg.image_eq]
    exact image_mono (fun z hz => ⟨hz.1,
      by rw [show z.2 = 1 / 2 from hz.2]; norm_num⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
