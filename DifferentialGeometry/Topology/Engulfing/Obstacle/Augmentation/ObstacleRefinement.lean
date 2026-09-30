import DifferentialGeometry.Topology.Engulfing.Obstacle.Augmentation.ObstacleAugmentation
import DifferentialGeometry.Topology.SimplicialComplex.Refinement.RefinementRestriction

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n d p : ℕ} {K L : SimplicialComplex ℝ E}
  {T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))}
  {f : C(K.space, EuclideanSpace ℝ (Fin n))}

def ObstacleAugmentation.refine
    (a : ObstacleAugmentation K L T f d p)
    (P : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a.ambientDimension)))
    (hP : P.faces.Finite) (href : simplicialRefines P a.joint)
    (hspace : P.space = a.joint.space) : ObstacleAugmentation K L T f d p := by
  let e := Homeomorph.setCongr hspace
  let S := complexRestriction P a.sourceImage
  let O := complexRestriction P a.obstacleImage
  let D := complexRestriction P a.fixedImage
  have hSs : S.space = a.sourceImage.space :=
    complexRestriction_space_of_refines P a.joint a.sourceImage href hspace a.sourceImage_faces
  have hOs : O.space = a.obstacleImage.space :=
    complexRestriction_space_of_refines P a.joint a.obstacleImage href hspace a.obstacleImage_faces
  have hDs : D.space = a.fixedImage.space :=
    complexRestriction_space_of_refines P a.joint a.fixedImage href hspace a.fixedImage_faces
  let s : C(K.space, P.space) :=
    (⟨e.symm, e.symm.continuous⟩ : C(a.joint.space, P.space)).comp a.sourceMap
  let o : C(T.space, P.space) :=
    (⟨e.symm, e.symm.continuous⟩ : C(a.joint.space, P.space)).comp a.obstacleMap
  let g : C(P.space, EuclideanSpace ℝ (Fin n)) :=
    a.oldMap.comp ⟨e, e.continuous⟩
  refine ⟨a.ambientDimension, P, hP, href.face_card_le_bound a.joint_dimension,
    s, e.symm.isClosedEmbedding.comp a.sourceMap_embedding,
    o, e.symm.isClosedEmbedding.comp a.obstacleMap_embedding,
    g, ?_, ?_, S, complexRestriction_faces_subset P a.sourceImage,
    ?_, (complexRestriction_refines_right P a.sourceImage).face_card_le_bound a.sourceImage_dimension,
    ?_, O, complexRestriction_faces_subset P a.obstacleImage,
    ?_, (complexRestriction_refines_right P a.obstacleImage).face_card_le_bound a.obstacleImage_dimension,
    D, complexRestriction_faces_subset P a.fixedImage, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact a.oldMap_source x
  · intro y
    exact a.oldMap_obstacle y
  · exact hSs.trans a.sourceImage_space
  · intro t ht
    obtain ⟨u, hu, htu⟩ := complexRestriction_refines_right P a.sourceImage t ht
    obtain ⟨v, hv, B, hB⟩ := a.sourceImage_sections u hu
    exact ⟨v, hv, B, fun y hy => hB y (htu hy)⟩
  · exact hOs.trans a.obstacleImage_space
  · intro x hx
    exact hDs.symm.subset (a.source_fixed x hx)
  · exact hOs.subset.trans (a.obstacle_fixed.trans hDs.symm.subset)
  · intro x hx y hy he
    exact e.injective (a.fixed_injective (x₁ := e x) (x₂ := e y)
      (hDs.subset hx) (hDs.subset hy) he)
  · intro t ht
    obtain ⟨u, hu, htu⟩ := complexRestriction_refines_right P a.fixedImage t ht
    obtain ⟨B, hB⟩ := a.fixed_affine u hu
    exact ⟨B, fun x hx => hB (e x) (htu hx)⟩
  · intro x hx
    exact a.intersection_fixed x (hOs.subset hx)

omit [DecidableEq E] in
@[simp] theorem ObstacleAugmentation.refine_ambientDimension
    (a : ObstacleAugmentation K L T f d p)
    (P : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a.ambientDimension)))
    (hP : P.faces.Finite) (href : simplicialRefines P a.joint)
    (hspace : P.space = a.joint.space) :
    (a.refine P hP href hspace).ambientDimension = a.ambientDimension := by
  classical
  exact rfl

omit [DecidableEq E] in
@[simp] theorem ObstacleAugmentation.refine_joint
    (a : ObstacleAugmentation K L T f d p)
    (P : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a.ambientDimension)))
    (hP : P.faces.Finite) (href : simplicialRefines P a.joint)
    (hspace : P.space = a.joint.space) :
    (a.refine P hP href hspace).joint = P := by
  classical
  exact rfl

omit [DecidableEq E] in
@[simp] theorem ObstacleAugmentation.refine_sourceMap_val
    (a : ObstacleAugmentation K L T f d p)
    (P : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a.ambientDimension)))
    (hP : P.faces.Finite) (href : simplicialRefines P a.joint)
    (hspace : P.space = a.joint.space) (x : K.space) :
    ((a.refine P hP href hspace).sourceMap x).val = (a.sourceMap x).val := by
  classical
  exact rfl

omit [DecidableEq E] in
@[simp] theorem ObstacleAugmentation.refine_sourceImage_space
    (a : ObstacleAugmentation K L T f d p)
    (P : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a.ambientDimension)))
    (hP : P.faces.Finite) (href : simplicialRefines P a.joint)
    (hspace : P.space = a.joint.space) :
    (a.refine P hP href hspace).sourceImage.space = a.sourceImage.space := by
  classical
  exact complexRestriction_space_of_refines P a.joint a.sourceImage href hspace a.sourceImage_faces

omit [DecidableEq E] in
@[simp] theorem ObstacleAugmentation.refine_obstacleImage_space
    (a : ObstacleAugmentation K L T f d p)
    (P : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a.ambientDimension)))
    (hP : P.faces.Finite) (href : simplicialRefines P a.joint)
    (hspace : P.space = a.joint.space) :
    (a.refine P hP href hspace).obstacleImage.space = a.obstacleImage.space := by
  classical
  exact complexRestriction_space_of_refines P a.joint a.obstacleImage href hspace a.obstacleImage_faces

omit [DecidableEq E] in
@[simp] theorem ObstacleAugmentation.refine_fixedImage_space
    (a : ObstacleAugmentation K L T f d p)
    (P : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a.ambientDimension)))
    (hP : P.faces.Finite) (href : simplicialRefines P a.joint)
    (hspace : P.space = a.joint.space) :
    (a.refine P hP href hspace).fixedImage.space = a.fixedImage.space := by
  classical
  exact complexRestriction_space_of_refines P a.joint a.fixedImage href hspace a.fixedImage_faces

end

end DifferentialGeometry.Topology.Engulfing
