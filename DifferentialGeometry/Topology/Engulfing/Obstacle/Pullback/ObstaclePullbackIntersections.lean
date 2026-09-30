import DifferentialGeometry.Topology.Engulfing.Obstacle.Pullback.ObstaclePullbackModel

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

noncomputable section

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n d p : ℕ} {ε : ℝ} {K L : SimplicialComplex ℝ E}
  {T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))}
  {f : C(K.space, EuclideanSpace ℝ (Fin n))}
  {a : RelativeGeneralPositionApproximation K L T f d p ε}

namespace ObstaclePullbackModel

variable (m : ObstaclePullbackModel a)

theorem rawMap_image_inter_faces
    {t u : Finset (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension))}
    (ht : t ∈ a.augmentation.sourceImage.faces) (hu : u ∈ a.augmentation.sourceImage.faces) :
    a.rawMap '' {x : K.space | x.val ∈
      convexHull ℝ (t.image m.inverse : Set E) ∩ convexHull ℝ (u.image m.inverse : Set E)} =
        convexHull ℝ (a.vertices ''
          ((t : Set (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension))) ∩ (u : Set _))) := by
  obtain ⟨A, hAv, hA⟩ := interpolateVertices_affineOn a.augmentation.joint
    a.augmentation.joint_finite a.vertices ⟨t, a.augmentation.sourceImage_faces ht⟩
  have himage : A '' ((t : Set _) ∩ (u : Set _)) =
      a.vertices '' ((t : Set _) ∩ (u : Set _)) :=
    image_congr (fun x hx => hAv x hx.1)
  have hsource (s : Finset (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension)))
      (hs : s ∈ a.augmentation.sourceImage.faces) (x : K.space)
      (hx : x.val ∈ convexHull ℝ (s.image m.inverse : Set E)) :
      (a.augmentation.sourceMap x).val ∈ convexHull ℝ (s : Set _) :=
    (m.source_face_image s hs).subset (mem_image_of_mem _ hx)
  rw [← himage, ← A.image_convexHull]
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hxt := hsource t ht x hx.1
    have hxu := hsource u hu x hx.2
    refine ⟨(a.augmentation.sourceMap x).val,
      a.augmentation.joint.inter_subset_convexHull
        (a.augmentation.sourceImage_faces ht) (a.augmentation.sourceImage_faces hu) ⟨hxt, hxu⟩, ?_⟩
    exact ((a.rawMap_source x).trans (hA _ hxt)).symm
  · rintro _ ⟨z, hz, rfl⟩
    have hzt : z ∈ convexHull ℝ (t : Set _) := convexHull_mono inter_subset_left hz
    have hzu : z ∈ convexHull ℝ (u : Set _) := convexHull_mono inter_subset_right hz
    obtain ⟨x, hx, hxt⟩ := (m.source_face_image t ht).symm.subset hzt
    obtain ⟨y, hy, hyu⟩ := (m.source_face_image u hu).symm.subset hzu
    have hxy : x = y := a.augmentation.sourceMap_embedding.injective
      (Subtype.ext (hxt.trans hyu.symm))
    refine ⟨x, ⟨hx, hxy.symm ▸ hy⟩, ?_⟩
    rw [a.rawMap_source, hA _ (hsource t ht x hx)]
    exact congrArg A hxt
theorem shared_vertex_hull_subset_rawMap_inter
    {t u : Finset (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension))}
    (ht : t ∈ a.augmentation.sourceImage.faces) (hu : u ∈ a.augmentation.sourceImage.faces) :
    convexHull ℝ (a.vertices ''
      ((t : Set (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension))) ∩ (u : Set _))) ⊆
      a.rawMap '' {x : K.space | x.val ∈
        convexHull ℝ (t.image m.inverse : Set E) ∩ convexHull ℝ (u.image m.inverse : Set E)} :=
  (m.rawMap_image_inter_faces ht hu).symm.subset

theorem shared_vertex_hull_subset_rawMap_of_inter_subset
    {t u : Finset (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension))}
    (ht : t ∈ a.augmentation.sourceImage.faces) (hu : u ∈ a.augmentation.sourceImage.faces)
    {roof : Set E}
    (hroof : convexHull ℝ (t.image m.inverse : Set E) ∩
      convexHull ℝ (u.image m.inverse : Set E) ⊆ roof) :
    convexHull ℝ (a.vertices ''
      ((t : Set (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension))) ∩ (u : Set _))) ⊆
        a.rawMap '' {x : K.space | x.val ∈ roof} := by
  rw [← m.rawMap_image_inter_faces ht hu]
  exact image_mono (fun _ hx => hroof hx)

theorem shared_vertex_hull_subset_rawMap_roof
    {t u : Finset (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension))}
    (ht : t ∈ a.augmentation.sourceImage.faces) (hu : u ∈ a.augmentation.sourceImage.faces)
    {covered roof : Set E}
    (hucovered : convexHull ℝ (u.image m.inverse : Set E) ⊆ covered)
    (hroof : convexHull ℝ (t.image m.inverse : Set E) ∩ covered ⊆ roof) :
    convexHull ℝ (a.vertices ''
      ((t : Set (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension))) ∩ (u : Set _))) ⊆
        a.rawMap '' {x : K.space | x.val ∈ roof} :=
  m.shared_vertex_hull_subset_rawMap_of_inter_subset ht hu
    (fun _ hx => hroof ⟨hx.1, hucovered hx.2⟩)

end ObstaclePullbackModel

end

end DifferentialGeometry.Topology.Engulfing
