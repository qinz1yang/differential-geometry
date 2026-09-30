import DifferentialGeometry.Topology.Engulfing.Obstacle.Approximation.ObstacleApproximation

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

noncomputable section

variable {E F : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [DecidableEq E] in
theorem interpolateVertices_image_inter_face
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (w : E → F) (s t : K.faces) :
    interpolateVertices K hK w '' (Subtype.val ⁻¹'
      convexHull ℝ ((s.val : Set E) ∩ (t.val : Set E))) =
        convexHull ℝ (w '' ((s.val : Set E) ∩ (t.val : Set E))) := by
  classical
  by_cases hne : (s.val ∩ t.val).Nonempty
  · simpa only [Finset.coe_inter] using
      interpolateVertices_image_face K hK w
        ⟨s.val ∩ t.val, K.down_closed s.property Finset.inter_subset_left hne⟩
  · have he : (s.val : Set E) ∩ (t.val : Set E) = ∅ := by
      rw [← Finset.coe_inter, Finset.not_nonempty_iff_eq_empty.mp hne]
      exact Finset.coe_empty
    simp only [he, convexHull_empty, preimage_empty, image_empty]

variable {n d p : ℕ} {K L : SimplicialComplex ℝ E}
  {T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))}
  {f : C(K.space, EuclideanSpace ℝ (Fin n))}

omit [DecidableEq E] [FiniteDimensional ℝ E] in
theorem ObstacleAugmentation.shared_face_disjoint
    (a : ObstacleAugmentation K L T f d p)
    (w : EuclideanSpace ℝ (Fin a.ambientDimension) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    (hfixed : ∀ x : a.joint.space, x.val ∈ a.fixedImage.space →
      correctedInterpolant a.joint a.joint_finite w H x = a.oldMap x)
    (s t : Finset (EuclideanSpace ℝ (Fin a.ambientDimension)))
    (hs : s ∈ a.sourceImage.faces) (ht : t ∈ a.obstacleImage.faces)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (havoid : ∀ x : K.space, (a.sourceMap x).val ∈ convexHull ℝ
      (s : Set (EuclideanSpace ℝ (Fin a.ambientDimension))) → x.val ∈ L.space → f x ∉ X) :
    Disjoint (convexHull ℝ (w '' ((s : Set (EuclideanSpace ℝ (Fin a.ambientDimension))) ∩
      (t : Set (EuclideanSpace ℝ (Fin a.ambientDimension)))))) (H ⁻¹' X) := by
  apply Set.disjoint_left.mpr
  intro z hz hzX
  obtain ⟨y, hy, hyz⟩ :=
    (interpolateVertices_image_inter_face a.joint a.joint_finite w
      ⟨s, a.sourceImage_faces hs⟩ ⟨t, a.obstacleImage_faces ht⟩).symm.subset hz
  change y.val ∈ convexHull ℝ
    ((s : Set (EuclideanSpace ℝ (Fin a.ambientDimension))) ∩ (t : Set _)) at hy
  have hys : y.val ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin a.ambientDimension))) :=
    convexHull_mono inter_subset_left hy
  have hyt : y.val ∈ convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin a.ambientDimension))) :=
    convexHull_mono inter_subset_right hy
  obtain ⟨x, hxy⟩ := a.sourceImage_space.subset (a.sourceImage.convexHull_subset_space hs hys)
  change (a.sourceMap x).val = y.val at hxy
  have hxy' : a.sourceMap x = y := Subtype.ext hxy
  have hyO : y.val ∈ a.obstacleImage.space := a.obstacleImage.convexHull_subset_space ht hyt
  have hxL : x.val ∈ L.space := a.intersection_fixed x (by rw [hxy]; exact hyO)
  have hvalue : f x = H z := by
    calc
      f x = a.oldMap (a.sourceMap x) := (a.oldMap_source x).symm
      _ = a.oldMap y := congrArg a.oldMap hxy'
      _ = correctedInterpolant a.joint a.joint_finite w H y :=
        (hfixed y (a.obstacle_fixed hyO)).symm
      _ = H z := congrArg H hyz
  exact havoid x (by rw [hxy]; exact hys) hxL (hvalue.symm ▸ hzX)

omit [DecidableEq E] [FiniteDimensional ℝ E] in
theorem ObstacleAugmentation.shared_face_inter_subset
    (a : ObstacleAugmentation K L T f d p)
    (w : EuclideanSpace ℝ (Fin a.ambientDimension) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n))
    (hfixed : ∀ x : a.joint.space, x.val ∈ a.fixedImage.space →
      correctedInterpolant a.joint a.joint_finite w H x = a.oldMap x)
    (s t : Finset (EuclideanSpace ℝ (Fin a.ambientDimension)))
    (hs : s ∈ a.sourceImage.faces) (ht : t ∈ a.obstacleImage.faces)
    (X roof : Set (EuclideanSpace ℝ (Fin n)))
    (hroof : ∀ x : K.space, (a.sourceMap x).val ∈ convexHull ℝ
      (s : Set (EuclideanSpace ℝ (Fin a.ambientDimension))) → x.val ∈ L.space →
        f x ∈ X → H.symm (f x) ∈ roof) :
    convexHull ℝ (w '' ((s : Set (EuclideanSpace ℝ (Fin a.ambientDimension))) ∩
      (t : Set (EuclideanSpace ℝ (Fin a.ambientDimension))))) ∩ H ⁻¹' X ⊆ roof := by
  have hd := a.shared_face_disjoint w H hfixed s t hs ht (X \ H '' roof)
    (fun x hxs hxL hx => hx.2 ⟨H.symm (f x), hroof x hxs hxL hx.1, H.apply_symm_apply _⟩)
  intro z hz
  by_contra hzr
  apply Set.disjoint_left.mp hd hz.1
  refine ⟨hz.2, ?_⟩
  rintro ⟨y, hy, he⟩
  exact hzr ((H.injective he) ▸ hy)

end

end DifferentialGeometry.Topology.Engulfing
