import DifferentialGeometry.Topology.Engulfing.Obstacle.Pullback.ObstaclePullbackModel

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology

noncomputable section

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n d p : ℕ} {ε : ℝ} {K L : SimplicialComplex ℝ E}
  {T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))}
  {f : C(K.space, EuclideanSpace ℝ (Fin n))}

omit [FiniteDimensional ℝ E] in
theorem RelativeGeneralPositionApproximation.raw_image_oscillation
    (a : RelativeGeneralPositionApproximation K L T f d p ε)
    {s : Finset (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension))}
    (hs : s ∈ a.augmentation.joint.faces)
    {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ convexHull ℝ (a.vertices '' (s : Set _)))
    (hy : y ∈ convexHull ℝ (a.vertices '' (s : Set _))) : dist x y < 5 * ε := by
  have heq := interpolateVertices_image_face a.augmentation.joint
    a.augmentation.joint_finite a.vertices ⟨s, hs⟩
  obtain ⟨u, hu, rfl⟩ := heq.symm.subset hx
  obtain ⟨v, hv, rfl⟩ := heq.symm.subset hy
  rw [dist_eq_norm]
  exact a.raw_oscillation s hs u v hu hv

omit [FiniteDimensional ℝ E] in
theorem ObstaclePullbackModel.raw_oscillation
    {a : RelativeGeneralPositionApproximation K L T f d p ε} (m : ObstaclePullbackModel a)
    {s : Finset E} (hs : s ∈ m.source.faces) (x y : K.space)
    (hx : x.val ∈ convexHull ℝ (s : Set E))
    (hy : y.val ∈ convexHull ℝ (s : Set E)) :
    dist (a.rawMap x) (a.rawMap y) < 5 * ε := by
  obtain ⟨t, ht, _, _, himage⟩ := m.face_image s hs
  exact a.raw_image_oscillation (a.augmentation.sourceImage_faces ht)
    (himage.subset ⟨x, hx, rfl⟩) (himage.subset ⟨y, hy, rfl⟩)

omit [FiniteDimensional ℝ E] in
theorem ObstaclePullbackModel.raw_face_subset_ball_of_meets
    {a : RelativeGeneralPositionApproximation K L T f d p ε} (m : ObstaclePullbackModel a)
    {s : Finset E} (hs : s ∈ m.source.faces)
    (z : EuclideanSpace ℝ (Fin n)) {r R : ℝ} (hgap : r + 5 * ε ≤ R)
    (hmeet : ∃ x : K.space, x.val ∈ convexHull ℝ (s : Set E) ∧ a.rawMap x ∈ ball z r) :
    a.rawMap '' {x : K.space | x.val ∈ convexHull ℝ (s : Set E)} ⊆ ball z R := by
  obtain ⟨x, hx, hxball⟩ := hmeet
  rintro _ ⟨y, hy, rfl⟩
  apply mem_ball.mpr
  calc
    dist (a.rawMap y) z ≤ dist (a.rawMap y) (a.rawMap x) + dist (a.rawMap x) z :=
      dist_triangle _ _ _
    _ < 5 * ε + r := add_lt_add (m.raw_oscillation hs y x hy hx) (mem_ball.mp hxball)
    _ ≤ R := by linarith

end

end DifferentialGeometry.Topology.Engulfing
