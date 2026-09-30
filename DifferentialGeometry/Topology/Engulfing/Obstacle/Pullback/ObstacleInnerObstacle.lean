import DifferentialGeometry.Topology.Engulfing.Obstacle.Pullback.ObstacleFiniteGPModel
import DifferentialGeometry.Topology.Engulfing.Obstacle.Augmentation.ObstacleSharedFaces
import DifferentialGeometry.Topology.Engulfing.Obstacle.Pullback.ObstacleRawComplex
import DifferentialGeometry.Topology.Engulfing.Local.Charts.ChartCorrection

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n d p : ℕ} {ε : ℝ} {K L : SimplicialComplex ℝ E}
  {T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))}
  {f : C(K.space, EuclideanSpace ℝ (Fin n))}
  {M : Type*} [TopologicalSpace M]

namespace RelativeGeneralPositionApproximation

variable (a : RelativeGeneralPositionApproximation K L T f d p ε)
theorem correction_preimage_obstacle : a.correction ⁻¹' T.space =
    ⋃ t ∈ a.augmentation.obstacleImage.faces,
      convexHull ℝ (a.vertices ''
        (t : Set (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension)))) := by
  ext y
  constructor
  · intro hy
    obtain ⟨t, ht, z, hz, he⟩ := mem_iUnion₂.mp (a.obstacle_image.subset hy)
    have hzy : z = y := a.correction.injective he
    exact mem_iUnion₂.mpr ⟨t, ht, hzy ▸ hz⟩
  · intro hy
    obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.mp hy
    exact a.obstacle_image.symm.subset (mem_iUnion₂.mpr ⟨t, ht, y, hyt, rfl⟩)

theorem jointObstacle_contains_of_corrected_chart
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (X C : Set M) (Y : Set E)
    (hX : e '' (X ∩ C) ⊆ T.space)
    (hYtarget : a.totalRawMap '' Y ⊆ (correctedAffineChart e a.correction).target)
    (hYcore : (correctedAffineChart e a.correction).symm '' (a.totalRawMap '' Y) ⊆ C) :
    (correctedAffineChart e a.correction).symm ⁻¹' X ∩ a.totalRawMap '' Y ⊆
      ⋃ t ∈ a.augmentation.obstacleImage.faces,
        convexHull ℝ (a.vertices ''
          (t : Set (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension)))) := by
  intro y hy
  apply a.correction_preimage_obstacle.subset
  have hCy : (correctedAffineChart e a.correction).symm y ∈ C :=
    hYcore (mem_image_of_mem _ hy.2)
  have hcover := hX ⟨(correctedAffineChart e a.correction).symm y, ⟨hy.1, hCy⟩, rfl⟩
  change e (e.symm (a.correction y)) ∈ T.space at hcover
  have hyt : a.correction y ∈ e.target := hYtarget hy.2
  rwa [e.right_inv hyt] at hcover

end RelativeGeneralPositionApproximation

namespace ObstaclePullbackModel

variable {a : RelativeGeneralPositionApproximation K L T f d p ε} (m : ObstaclePullbackModel a)

def sourceJointFace (s : m.source.faces) :
    Finset (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension)) :=
  Classical.choose (m.face_image s.val s.property)

@[simp] theorem sourceJointFace_eq (s : m.source.faces) :
    m.sourceJointFace s = (m.toFiniteGPFaceModel.face s).val := rfl

theorem shared_avoids_of_fixed_avoidance
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (g : K.space → M) (X : Set M) (Y : Set E)
    (hsource : ∀ x : K.space, x.val ∈ Y → x.val ∈ L.space → g x ∈ e.source)
    (hlocal : ∀ x : K.space, x.val ∈ Y → x.val ∈ L.space → f x = e (g x))
    (havoid : ∀ x : K.space, x.val ∈ Y → x.val ∈ L.space → g x ∉ X) :
    ∀ s : m.source.faces, convexHull ℝ (s.val : Set E) ⊆ Y →
      ∀ t ∈ a.augmentation.obstacleImage.faces, Disjoint
        (convexHull ℝ (a.vertices ''
          ((m.sourceJointFace s : Set _) ∩ (t : Set _))))
        ((correctedAffineChart e a.correction).symm ⁻¹' X) := by
  intro s hsY t ht
  have hs := m.toFiniteGPFaceModel_face_mem_source s
  have havoid' : ∀ x : K.space, (a.augmentation.sourceMap x).val ∈
      convexHull ℝ (m.sourceJointFace s : Set _) →
      x.val ∈ L.space → f x ∉ e.symm ⁻¹' X := by
    intro x hxs hxL hxX
    obtain ⟨z, hz, he⟩ := (m.source_face_image _ hs).symm.subset hxs
    have hzx : z = x := a.augmentation.sourceMap_embedding.injective (Subtype.ext he)
    have hxface : x.val ∈ convexHull ℝ (s.val : Set E) := by
      rw [← m.toFiniteGPFaceModel_face_inverse s]
      exact hzx ▸ hz
    have hxY := hsY hxface
    apply havoid x hxY hxL
    change e.symm (f x) ∈ X at hxX
    rwa [hlocal x hxY hxL, e.left_inv (hsource x hxY hxL)] at hxX
  exact a.augmentation.shared_face_disjoint a.vertices a.correction a.fixed_exact
    (m.sourceJointFace s) t hs ht (e.symm ⁻¹' X) havoid'

end ObstaclePullbackModel

end

end DifferentialGeometry.Topology.Engulfing
