import DifferentialGeometry.Topology.Engulfing.Obstacle.Pullback.ObstaclePullbackIntersections
import DifferentialGeometry.Topology.Engulfing.Newman.Inner.NewmanInnerGeneralPosition

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

def totalRawMap : E → EuclideanSpace ℝ (Fin n) := by
  classical
  exact fun x => if hx : x ∈ K.space then a.rawMap ⟨x, hx⟩ else 0

@[simp] theorem totalRawMap_subtype (x : K.space) : a.totalRawMap x.val = a.rawMap x := by
  simp only [totalRawMap, dite_eq_left x.property]
theorem totalRawMap_image {S : Set E} (hS : S ⊆ K.space) :
    a.totalRawMap '' S = a.rawMap '' {x : K.space | x.val ∈ S} := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, hS hx⟩, hx, (a.totalRawMap_subtype ⟨x, hS hx⟩).symm⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.val, hx, a.totalRawMap_subtype x⟩

end RelativeGeneralPositionApproximation

namespace ObstaclePullbackModel

variable {a : RelativeGeneralPositionApproximation K L T f d p ε} (m : ObstaclePullbackModel a)

def toFiniteGPFaceModel : FiniteGPFaceModel m.source a.totalRawMap := by
  classical
  choose t ht hinverse hcard himage using fun s : m.source.faces => m.face_image s.val s.property
  have hK (s : m.source.faces) : convexHull ℝ (s.val : Set E) ⊆ K.space :=
    fun _ hx => m.space.subset (m.source.convexHull_subset_space s.property hx)
  refine
    { jointDimension := a.augmentation.ambientDimension
      joint := a.augmentation.joint
      finite_faces := a.augmentation.joint_finite
      vertices := a.vertices
      generalPosition := a.generalPosition
      face := fun s => ⟨t s, a.augmentation.sourceImage_faces (ht s)⟩
      face_card := hcard
      face_image := ?_
      shared := ?_ }
  · intro s
    rw [a.totalRawMap_image (hK s)]
    exact himage s
  · intro s u
    rw [a.totalRawMap_image (inter_subset_left.trans (hK s))]
    have h := m.shared_vertex_hull_subset_rawMap_inter (ht s) (ht u)
    rw [hinverse s, hinverse u] at h
    exact h

theorem toFiniteGPFaceModel_face_mem_source (s : m.source.faces) :
    (m.toFiniteGPFaceModel.face s).val ∈ a.augmentation.sourceImage.faces :=
  (Classical.choose_spec (m.face_image s.val s.property)).1

theorem toFiniteGPFaceModel_face_inverse (s : m.source.faces) :
    (m.toFiniteGPFaceModel.face s).val.image m.inverse = s.val :=
  (Classical.choose_spec (m.face_image s.val s.property)).2.1

@[simp] theorem toFiniteGPFaceModel_joint : m.toFiniteGPFaceModel.joint = a.augmentation.joint := rfl

@[simp] theorem toFiniteGPFaceModel_vertices : m.toFiniteGPFaceModel.vertices = a.vertices := rfl

end ObstaclePullbackModel

end

end DifferentialGeometry.Topology.Engulfing
