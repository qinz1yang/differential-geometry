import DifferentialGeometry.Topology.Engulfing.Obstacle.Augmentation.ObstacleAugmentation

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n d p : ℕ}

omit [DecidableEq E] in
theorem correctedInterpolant_image_subcomplex
    (K J : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hJK : J.faces ⊆ K.faces)
    (w : E → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)) :
    correctedInterpolant K hK w H '' {x : K.space | x.val ∈ J.space} =
      ⋃ s ∈ J.faces, H '' convexHull ℝ (w '' (s : Set E)) := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    apply mem_iUnion₂.mpr
    refine ⟨s, hs, mem_image_of_mem H ?_⟩
    exact (interpolateVertices_image_face K hK w ⟨s, hJK hs⟩).subset
      (mem_image_of_mem _ hxs)
  · intro hy
    obtain ⟨s, hs, z, hz, rfl⟩ := mem_iUnion₂.mp hy
    obtain ⟨x, hx, he⟩ := (interpolateVertices_image_face K hK w ⟨s, hJK hs⟩).symm.subset hz
    refine ⟨x, J.convexHull_subset_space hs hx, ?_⟩
    exact congrArg H he

omit [DecidableEq E] in
theorem ObstacleAugmentation.exists_approximation
    {K L : SimplicialComplex ℝ E}
    {T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))}
    {f : C(K.space, EuclideanSpace ℝ (Fin n))}
    (a : ObstacleAugmentation K L T f d p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ w : EuclideanSpace ℝ (Fin a.ambientDimension) → EuclideanSpace ℝ (Fin n),
      ∃ H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n),
      ∃ g : C(K.space, EuclideanSpace ℝ (Fin n)),
      let P := barycentricSubdivisionIter a.joint N
      let hP := barycentricSubdivisionIter_finite_faces a.joint a.joint_finite N
      let hspace := barycentricSubdivisionIter_space a.joint N
      (∀ s : Finset (EuclideanSpace ℝ (Fin a.ambientDimension)),
        (s : Set (EuclideanSpace ℝ (Fin a.ambientDimension))) ⊆ P.vertices → s.card ≤ n + 1 →
          AffineIndependent ℝ (fun x : s => w x.val)) ∧
      (∀ x, g x = correctedInterpolant P hP w H ((Homeomorph.setCongr hspace).symm (a.sourceMap x))) ∧
      (∀ x : K.space, x.val ∈ L.space → g x = f x) ∧
      (∀ x, ‖g x - f x‖ < ε) ∧
      (∀ y, ‖H y - y‖ < ε) ∧ (∀ y, ‖H.symm y - y‖ < ε) ∧
      (T.space = ⋃ s ∈ (barycentricSubdivisionIter a.obstacleImage N).faces,
        H '' convexHull ℝ (w '' (s : Set (EuclideanSpace ℝ (Fin a.ambientDimension))))) ∧
      ∃ R : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a.ambientDimension)),
        R.faces.Finite ∧ R.space = P.space ∧ simplicialRefines R P ∧
        (∀ s ∈ R.faces, s.card ≤ d + 1) ∧
        ∀ s ∈ R.faces, ∃ B : EuclideanSpace ℝ (Fin a.ambientDimension) →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
          ∀ x : P.space,
            x.val ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin a.ambientDimension))) →
              correctedInterpolant P hP w H x = B x.val := by
  classical
  obtain ⟨N, w, H, hgp, hrel, hnear, hPL, hHsmall, hHinv⟩ :=
    exists_relative_barycentric_approximation a.joint a.joint_finite
      a.fixedImage a.fixedImage_faces a.joint_dimension a.oldMap a.fixed_affine a.fixed_injective hε
  let P := barycentricSubdivisionIter a.joint N
  let hP := barycentricSubdivisionIter_finite_faces a.joint a.joint_finite N
  let hspace := barycentricSubdivisionIter_space a.joint N
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
  refine ⟨N, w, H, g, hgp, fun _ => rfl, ?_, ?_, hHsmall, hHinv, ?_, hPL⟩
  · intro x hx
    have he := hrel (e.symm (a.sourceMap x)) (a.source_fixed x hx)
    change g x = a.oldMap (e (e.symm (a.sourceMap x))) at he
    simpa only [e.apply_symm_apply, a.oldMap_source] using he
  · intro x
    have he := hnear (e.symm (a.sourceMap x))
    change ‖g x - a.oldMap (e (e.symm (a.sourceMap x)))‖ < ε at he
    simpa only [e.apply_symm_apply, a.oldMap_source] using he
  · let J := barycentricSubdivisionIter a.obstacleImage N
    have hJP : J.faces ⊆ P.faces := barycentricSubdivisionIter_faces_subset a.obstacleImage_faces N
    have hJs : J.space = a.obstacleImage.space := barycentricSubdivisionIter_space a.obstacleImage N
    rw [← correctedInterpolant_image_subcomplex P J hP hJP w H]
    exact hJimage.symm.trans (by rw [hJs])

end

end DifferentialGeometry.Topology.Engulfing
