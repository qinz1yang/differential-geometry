import DifferentialGeometry.Topology.Engulfing.Obstacle.Approximation.ObstacleApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.RelativeStellarApproximation

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n d p : ℕ}

omit [DecidableEq E] in
theorem ObstacleAugmentation.exists_stellar_approximation
    {K L : SimplicialComplex ℝ E}
    {T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))}
    {f : C(K.space, EuclideanSpace ℝ (Fin n))}
    (a : ObstacleAugmentation K L T f d p) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a.ambientDimension)),
      ∃ hP : P.faces.Finite, ∃ hspace : P.space = a.joint.space,
      ∃ w : EuclideanSpace ℝ (Fin a.ambientDimension) → EuclideanSpace ℝ (Fin n),
      ∃ H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n),
      ∃ g : C(K.space, EuclideanSpace ℝ (Fin n)),
      simplicialRefines P a.joint ∧ (∀ s ∈ P.faces, s.card ≤ d + 1) ∧
      (∀ A C, FiniteSimplexExpansionIn a.joint A C → FiniteSimplexExpansionIn P A C) ∧
      (∀ s : Finset (EuclideanSpace ℝ (Fin a.ambientDimension)),
        (s : Set (EuclideanSpace ℝ (Fin a.ambientDimension))) ⊆ P.vertices → s.card ≤ n + 1 →
          AffineIndependent ℝ (fun x : s => w x.val)) ∧
      (∀ x : P.space, x.val ∈ a.fixedImage.space →
        correctedInterpolant P hP w H x = a.oldMap (Homeomorph.setCongr hspace x)) ∧
      (∀ x, g x = correctedInterpolant P hP w H ((Homeomorph.setCongr hspace).symm (a.sourceMap x))) ∧
      (∀ x : K.space, x.val ∈ L.space → g x = f x) ∧
      (∀ x, ‖g x - f x‖ < ε) ∧
      (∀ y, ‖H y - y‖ < ε) ∧ (∀ y, ‖H.symm y - y‖ < ε) ∧
      (T.space = ⋃ s ∈ (complexRestriction P a.obstacleImage).faces,
        H '' convexHull ℝ (w '' (s : Set (EuclideanSpace ℝ (Fin a.ambientDimension))))) ∧
      (∃ R : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a.ambientDimension)),
        R.faces.Finite ∧ R.space = P.space ∧ simplicialRefines R P ∧
        (∀ s ∈ R.faces, s.card ≤ d + 1) ∧
        ∀ s ∈ R.faces, ∃ B : EuclideanSpace ℝ (Fin a.ambientDimension) →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
          ∀ x : P.space,
            x.val ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin a.ambientDimension))) →
              correctedInterpolant P hP w H x = B x.val) ∧
      (∀ s ∈ P.faces, ∀ x y : P.space,
        x.val ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin a.ambientDimension))) →
        y.val ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin a.ambientDimension))) →
        ‖interpolateVertices P hP w x - interpolateVertices P hP w y‖ < 5 * ε) := by
  classical
  obtain ⟨P, hP, hspace, w, H, href, hdim, hexp, hgp, hrel, hnear, hPL, hHsmall, hHinv, hosc⟩ :=
    exists_relative_stellar_approximation_preserving_expansions a.joint a.joint_finite
      a.fixedImage a.fixedImage_faces a.joint_dimension a.oldMap a.fixed_affine a.fixed_injective hε
  let e : P.space ≃ₜ a.joint.space := Homeomorph.setCongr hspace
  let C := correctedInterpolant P hP w H
  let g : C(K.space, EuclideanSpace ℝ (Fin n)) :=
    (C.comp (⟨e.symm, e.symm.continuous⟩ : C(a.joint.space, P.space))).comp a.sourceMap
  have hJimage : C '' {x : P.space | x.val ∈ a.obstacleImage.space} = T.space := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz⟩ := a.obstacleImage_space.subset hx
      have he : a.obstacleMap z = e x := Subtype.ext hz
      have hc : C x = a.oldMap (e x) := hrel x (a.obstacle_fixed hx)
      rw [hc, ← he, a.oldMap_obstacle]
      exact z.property
    · intro hy
      let z : T.space := ⟨y, hy⟩
      have hzT : (a.obstacleMap z).val ∈ a.obstacleImage.space :=
        a.obstacleImage_space.symm.subset (mem_range_self z)
      refine ⟨e.symm (a.obstacleMap z), hzT, ?_⟩
      have hc := hrel (e.symm (a.obstacleMap z)) (a.obstacle_fixed hzT)
      change C (e.symm (a.obstacleMap z)) = a.oldMap (e (e.symm (a.obstacleMap z))) at hc
      rw [e.apply_symm_apply, a.oldMap_obstacle] at hc
      exact hc
  refine ⟨P, hP, hspace, w, H, g, href, hdim, hexp, hgp, hrel,
    fun _ => rfl, ?_, ?_, hHsmall, hHinv, ?_, hPL, hosc⟩
  · intro x hx
    have he := hrel (e.symm (a.sourceMap x)) (a.source_fixed x hx)
    change g x = a.oldMap (e (e.symm (a.sourceMap x))) at he
    simpa only [e.apply_symm_apply, a.oldMap_source] using he
  · intro x
    have he := hnear (e.symm (a.sourceMap x))
    change ‖g x - a.oldMap (e (e.symm (a.sourceMap x)))‖ < ε at he
    simpa only [e.apply_symm_apply, a.oldMap_source] using he
  · let J := complexRestriction P a.obstacleImage
    have hJP : J.faces ⊆ P.faces := complexRestriction_faces_subset P a.obstacleImage
    have hJs : J.space = a.obstacleImage.space :=
      complexRestriction_space_of_refines P a.joint a.obstacleImage href hspace a.obstacleImage_faces
    rw [← correctedInterpolant_image_subcomplex P J hP hJP w H]
    exact hJimage.symm.trans (by rw [hJs])

end

end DifferentialGeometry.Topology.Engulfing
