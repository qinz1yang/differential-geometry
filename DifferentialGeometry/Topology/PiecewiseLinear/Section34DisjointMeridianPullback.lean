import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalMeridianBarrier
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.BallHomotopy

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem IsCylindricalDiagram.exists_essential_lateral_pullback_of_disjoint_seam
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces] (hD : IsPLBall 2 D.space)
    {f : E × ℝ → F} {S J : Set F} (hf : IsCylindricalDiagram f D.space S)
    (hJ : IsPLSphere 1 J)
    (hJside : J ⊆ f '' ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1))
    (hdis : Disjoint J (f '' (D.space ×ˢ ({0} : Set ℝ))))
    (hnon : ¬ (⟨inclusion hJside, continuous_inclusion hJside⟩ :
      C(J, f '' ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1))).Nullhomotopic) :
    ∃ K : Set (E × ℝ), IsPLSphere 1 K ∧
      K ⊆ (boundaryComplex 2 D).space ×ˢ Ioo (0 : ℝ) 1 ∧
      IsPLHomeomorphOn f K J ∧
      ¬ ∃ (Q : Set (E × ℝ)) (q : (Fin 3 → ℝ) → E × ℝ),
        IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Q ∧
        Q ⊆ (boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1 ∧
        q '' stdSimplexBoundary 2 = K := by
  classical
  let B := (boundaryComplex 2 D).space
  let A := B ×ˢ Icc (0 : ℝ) 1
  have hB : IsPLSphere 1 B := isPLSphere_boundaryComplex_space_of_isPLBall D hD
  have hside : IsCylindricalDiagram f B (f '' A) :=
    hf.boundary D hD.isCombinatorialManifoldWithBoundary
  have hdis' : Disjoint J (f '' (B ×ˢ ({0} : Set ℝ))) :=
    hdis.mono_right (image_mono (prod_mono (boundaryComplex_space_subset 2 D) Subset.rfl))
  obtain ⟨a, b, ha, hab, hb, hJstrip⟩ :=
    hside.exists_strip_containing_of_disjoint_bottom hB.isPolyhedron.isCompact
      hJ.isPolyhedron.isClosed hJside hJ.nonempty hdis'
  let R := B ×ˢ Icc a b
  have hσ : IsPLHomeomorphOn f R (f '' R) :=
    hside.isPLHomeomorphOn_strip hB.isPolyhedron ha.le hb.le (Or.inl ha)
  let τ := Function.invFunOn f R
  let K := τ '' J
  have hτ : IsPLHomeomorphOn τ J K := hσ.symm.restrict hJ.isPolyhedron hJstrip
  have hK : IsPLSphere 1 K := hJ.of_isPLHomeomorphOn hτ
  have hKR : K ⊆ R := image_subset_iff.mpr (hσ.symm.bijOn.mapsTo.mono_left hJstrip)
  have hKA : K ⊆ A := fun _ hx =>
    ⟨(hKR hx).1, ha.le.trans (hKR hx).2.1, (hKR hx).2.2.trans hb.le⟩
  have hback : f '' K = J := by
    rw [show K = τ '' J from rfl, ← image_comp]
    exact (show EqOn (f ∘ τ) id J from fun _ hx =>
      hσ.bijOn.invOn_invFunOn.2 (hJstrip hx)).image_eq.trans (image_id J)
  have hfK : IsPLHomeomorphOn f K J := by
    rw [← hback]
    exact hσ.restrict hK.isPolyhedron hKR
  refine ⟨K, hK, fun _ hx =>
    ⟨(hKR hx).1, ha.trans_le (hKR hx).2.1, (hKR hx).2.2.trans_lt hb⟩, hfK, ?_⟩
  rintro ⟨Q, q, hq, hQA, hqK⟩
  have hKQ : K ⊆ Q := hqK ▸
    (image_mono (fun _ hx => hx.1)).trans hq.image_eq.subset
  have hnull := (show IsPLBall 2 Q from ⟨q, hq⟩).nullhomotopic_inclusion hKQ hQA
  let φ : C(A, f '' A) := ⟨fun x => ⟨f x, ⟨x, x.2, rfl⟩⟩,
    (hside.isPiecewiseAffineOn.continuousOn.comp_continuous continuous_subtype_val
      fun x => x.2).subtype_mk _⟩
  let ψ : C(J, K) := hfK.homeomorph.symm
  have heq : (φ.comp (⟨inclusion hKA, continuous_inclusion hKA⟩ : C(K, A))).comp ψ =
      (⟨inclusion hJside, continuous_inclusion hJside⟩ : C(J, f '' A)) := by
    ext y
    exact hfK.bijOn.invOn_invFunOn.2 y.2
  exact hnon (heq ▸ (hnull.comp_right φ).comp_left ψ)

end DifferentialGeometry.Topology.PiecewiseLinear
