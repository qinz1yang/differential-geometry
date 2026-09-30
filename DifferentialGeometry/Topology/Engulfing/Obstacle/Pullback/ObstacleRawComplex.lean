import DifferentialGeometry.Topology.Engulfing.Obstacle.Approximation.ObstacleGeneralPosition

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n d p : ℕ} {ε : ℝ} {K L : SimplicialComplex ℝ E}
  {T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))}
  {f : C(K.space, EuclideanSpace ℝ (Fin n))}

namespace RelativeGeneralPositionApproximation

variable (a : RelativeGeneralPositionApproximation K L T f d p ε)

def rawAmbient : EuclideanSpace ℝ (Fin a.augmentation.ambientDimension) →
    EuclideanSpace ℝ (Fin n) := by
  classical
  exact fun x => if hx : x ∈ a.augmentation.joint.space then
    interpolateVertices a.augmentation.joint a.augmentation.joint_finite a.vertices ⟨x, hx⟩
  else 0

@[simp] theorem rawAmbient_subtype (x : a.augmentation.joint.space) :
    a.rawAmbient x.val =
      interpolateVertices a.augmentation.joint a.augmentation.joint_finite a.vertices x := by
  simp only [rawAmbient, dite_eq_left x.property]
theorem rawAmbient_vertex {x : EuclideanSpace ℝ (Fin a.augmentation.ambientDimension)}
    (hx : x ∈ a.augmentation.joint.vertices) : a.rawAmbient x = a.vertices x := by
  rw [show a.rawAmbient x = interpolateVertices a.augmentation.joint a.augmentation.joint_finite
      a.vertices ⟨x, a.augmentation.joint.vertices_subset_space hx⟩ from
        a.rawAmbient_subtype ⟨x, a.augmentation.joint.vertices_subset_space hx⟩]
  exact interpolateVertices_vertex _ _ _ _ hx
theorem rawAmbient_affine : ∀ s ∈ a.augmentation.joint.faces,
    ∃ A : EuclideanSpace ℝ (Fin a.augmentation.ambientDimension) →ᵃ[ℝ]
      EuclideanSpace ℝ (Fin n), EqOn a.rawAmbient A
        (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension)))) := by
  intro s hs
  obtain ⟨A, -, hA⟩ := interpolateVertices_affineOn a.augmentation.joint
    a.augmentation.joint_finite a.vertices ⟨s, hs⟩
  refine ⟨A, fun x hx => ?_⟩
  exact (a.rawAmbient_subtype ⟨x, a.augmentation.joint.convexHull_subset_space hs hx⟩).trans
    (hA _ hx)
theorem rawAmbient_fixed (x : a.augmentation.joint.space)
    (hx : x.val ∈ a.augmentation.fixedImage.space) :
    a.correction (a.rawAmbient x.val) = a.augmentation.oldMap x := by
  rw [a.rawAmbient_subtype]
  exact a.fixed_exact x hx
theorem rawAmbient_injOn_fixed : InjOn a.rawAmbient a.augmentation.fixedImage.space := by
  intro x hx y hy he
  have hxJ : x ∈ a.augmentation.joint.space := by
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    exact a.augmentation.joint.convexHull_subset_space (a.augmentation.fixedImage_faces hs) hxs
  have hyJ : y ∈ a.augmentation.joint.space := by
    obtain ⟨s, hs, hys⟩ := SimplicialComplex.mem_space_iff.mp hy
    exact a.augmentation.joint.convexHull_subset_space (a.augmentation.fixedImage_faces hs) hys
  have hxy : a.augmentation.oldMap ⟨x, hxJ⟩ = a.augmentation.oldMap ⟨y, hyJ⟩ :=
    (a.rawAmbient_fixed ⟨x, hxJ⟩ hx).symm.trans
      ((congrArg a.correction he).trans (a.rawAmbient_fixed ⟨y, hyJ⟩ hy))
  exact congrArg Subtype.val (a.augmentation.fixed_injective hx hy hxy)
theorem rawAmbient_injOn_obstacle : InjOn a.rawAmbient a.augmentation.obstacleImage.space :=
  a.rawAmbient_injOn_fixed.mono a.augmentation.obstacle_fixed
theorem rawAmbient_affine_obstacle : ∀ s ∈ a.augmentation.obstacleImage.faces,
    ∃ A : EuclideanSpace ℝ (Fin a.augmentation.ambientDimension) →ᵃ[ℝ]
      EuclideanSpace ℝ (Fin n), EqOn a.rawAmbient A
        (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension)))) :=
  fun _ hs => a.rawAmbient_affine _ (a.augmentation.obstacleImage_faces hs)

def rawObstacleComplex : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)) :=
  injectiveImageComplex a.augmentation.obstacleImage a.rawAmbient
    a.rawAmbient_affine_obstacle a.rawAmbient_injOn_obstacle
theorem rawObstacleComplex_finite_faces : a.rawObstacleComplex.faces.Finite :=
  injectiveImageComplex_finite_faces a.augmentation.obstacleImage
    (a.augmentation.joint_finite.subset a.augmentation.obstacleImage_faces)
    a.rawAmbient a.rawAmbient_affine_obstacle a.rawAmbient_injOn_obstacle
theorem rawObstacleComplex_face_card_le :
    ∀ s ∈ a.rawObstacleComplex.faces, s.card ≤ p + 1 := by
  rintro _ ⟨t, ht, rfl⟩
  exact Finset.card_image_le.trans (a.augmentation.obstacleImage_dimension t ht)
theorem rawAmbient_obstacleMap (y : T.space) :
    a.rawAmbient (a.augmentation.obstacleMap y).val = a.correction.symm y.val := by
  have hyO : (a.augmentation.obstacleMap y).val ∈ a.augmentation.obstacleImage.space :=
    a.augmentation.obstacleImage_space.symm.subset (mem_range_self y)
  have h := a.rawAmbient_fixed (a.augmentation.obstacleMap y) (a.augmentation.obstacle_fixed hyO)
  rw [a.augmentation.oldMap_obstacle] at h
  exact (a.correction.symm_apply_apply _).symm.trans (congrArg a.correction.symm h)
theorem rawObstacleComplex_space : a.rawObstacleComplex.space = a.correction.symm '' T.space := by
  rw [rawObstacleComplex, injectiveImageComplex_space, a.augmentation.obstacleImage_space]
  apply Subset.antisymm
  · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y.val, y.property, (a.rawAmbient_obstacleMap y).symm⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨(a.augmentation.obstacleMap ⟨y, hy⟩).val, mem_range_self _, a.rawAmbient_obstacleMap _⟩
theorem rawObstacleComplex_faces :
    a.rawObstacleComplex.faces = {s | ∃ t ∈ a.augmentation.obstacleImage.faces,
      t.image a.vertices = s} := by
  have himage (t : Finset (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension)))
      (ht : t ∈ a.augmentation.obstacleImage.faces) : t.image a.rawAmbient = t.image a.vertices := by
    apply Finset.image_congr
    intro x hx
    exact a.rawAmbient_vertex (face_vertices_subset a.augmentation.joint
      ⟨t, a.augmentation.obstacleImage_faces ht⟩ hx)
  ext s
  change (∃ t ∈ a.augmentation.obstacleImage.faces, t.image a.rawAmbient = s) ↔ _
  constructor
  · rintro ⟨t, ht, he⟩
    exact ⟨t, ht, (himage t ht).symm.trans he⟩
  · rintro ⟨t, ht, he⟩
    exact ⟨t, ht, (himage t ht).trans he⟩

end RelativeGeneralPositionApproximation

end

end DifferentialGeometry.Topology.Engulfing
