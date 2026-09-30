import DifferentialGeometry.Topology.Engulfing.Simplex.Columns.ExceptionalSubsets

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology
open scoped ContinuousMap

variable {E : Type*} [DecidableEq E]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

structure FiniteGPFaceModel {n : ℕ} (K : SimplicialComplex ℝ E)
    (raw : E → EuclideanSpace ℝ (Fin n)) where
  jointDimension : ℕ
  joint : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin jointDimension))
  finite_faces : joint.faces.Finite
  vertices : EuclideanSpace ℝ (Fin jointDimension) → EuclideanSpace ℝ (Fin n)
  generalPosition : ∀ s : Finset (EuclideanSpace ℝ (Fin jointDimension)),
    (s : Set (EuclideanSpace ℝ (Fin jointDimension))) ⊆ joint.vertices → s.card ≤ n + 1 →
      AffineIndependent ℝ (fun x : s => vertices x.val)
  face : K.faces → joint.faces
  face_card : ∀ s, (face s).val.card = s.val.card
  face_image : ∀ s, raw '' convexHull ℝ (s.val : Set E) =
    convexHull ℝ (vertices '' ((face s).val : Set (EuclideanSpace ℝ (Fin jointDimension))))
  shared : ∀ s t, convexHull ℝ (vertices ''
      (((face s).val : Set (EuclideanSpace ℝ (Fin jointDimension))) ∩ (face t).val)) ⊆
        raw '' (convexHull ℝ (s.val : Set E) ∩ convexHull ℝ (t.val : Set E))

omit [DecidableEq E] [FiniteDimensional ℝ E] in
theorem FiniteGPFaceModel.exists_exceptional_columns {n p q : ℕ}
    {K : SimplicialComplex ℝ E} {raw : E → EuclideanSpace ℝ (Fin n)}
    (m : FiniteGPFaceModel K raw) (hK : K.faces.Finite)
    (hp : p + 3 ≤ n) (hqp : q ≤ p)
    (H : SimplicialComplex ℝ E) (hHK : H.faces ⊆ K.faces)
    (hHd : ∀ s ∈ H.faces, s.card ≤ p + 1)
    (O : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m.jointDimension)))
    (hOJ : O.faces ⊆ m.joint.faces) (hOd : ∀ t ∈ O.faces, t.card ≤ p + 1)
    {M : Type*} [TopologicalSpace M] (F : C(K.space, M))
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (X : Set M)
    (σ : K.faces) (hσdim : σ.val.card ≤ q + 2)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (s : SimplexSplit ι) (v : ι → EuclideanSpace ℝ (Fin n))
    (hv : AffineIndependent ℝ v)
    (hshape : convexHull ℝ (range v) = raw '' convexHull ℝ (σ.val : Set E))
    (hσtarget : convexHull ℝ (range v) ⊆ e.target)
    (hHcoords : ∀ x : K.space, x.val ∈ H.space →
      F x ∈ e.symm '' convexHull ℝ (range v) → e (F x) = raw x.val)
    (hroof : raw '' (H.space ∩ convexHull ℝ (σ.val : Set E)) ⊆ s.lowerRoof v)
    (hXcover : e.symm ⁻¹' X ∩ convexHull ℝ (range v) ⊆
      ⋃ t ∈ O.faces, convexHull ℝ (m.vertices ''
        (t : Set (EuclideanSpace ℝ (Fin m.jointDimension)))))
    (hXshared : ∀ t ∈ O.faces, Disjoint
      (convexHull ℝ (m.vertices '' (((m.face σ).val : Set (EuclideanSpace ℝ (Fin m.jointDimension))) ∩ t)))
      (e.symm ⁻¹' X)) :
    ∃ T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)), T.faces.Finite ∧
      (∀ u ∈ T.faces, u.card ≤ q) ∧ T.space ⊆ convexHull ℝ (range v) ∧
      s.columnSaturation v hv T.space = T.space ∧
      e.symm ⁻¹' (X ∪ F '' (Subtype.val ⁻¹' H.space)) ∩ convexHull ℝ (range v) ⊆
        s.lowerRoof v ∪ T.space := by
  classical
  let : Fintype H.faces := (hK.subset hHK).fintype
  let : Fintype O.faces := (m.finite_faces.subset hOJ).fintype
  let t : H.faces ⊕ O.faces → m.joint.faces := Sum.elim
    (fun r => m.face ⟨r.val, hHK r.property⟩) (fun r => ⟨r.val, hOJ r.property⟩)
  let P : H.faces ⊕ O.faces → Set (EuclideanSpace ℝ (Fin n)) := Sum.elim
    (fun r => raw '' convexHull ℝ (r.val : Set E))
    (fun r => e.symm ⁻¹' X ∩ convexHull ℝ (m.vertices ''
      (r.val : Set (EuclideanSpace ℝ (Fin m.jointDimension)))))
  have ht : ∀ i, (t i).val.card ≤ p + 1 := by
    intro i
    cases i with
    | inl r => exact (m.face_card ⟨r.val, hHK r.property⟩).trans_le (hHd r.val r.property)
    | inr r => exact hOd r.val r.property
  have hP : ∀ i, P i ⊆ convexHull ℝ (m.vertices ''
      ((t i).val : Set (EuclideanSpace ℝ (Fin m.jointDimension)))) := by
    intro i
    cases i with
    | inl r => exact (m.face_image ⟨r.val, hHK r.property⟩).subset
    | inr r => exact inter_subset_right
  have hshared : ∀ i, convexHull ℝ (m.vertices ''
      (((m.face σ).val : Set (EuclideanSpace ℝ (Fin m.jointDimension))) ∩ (t i).val)) ∩ P i ⊆
        s.lowerRoof v := by
    intro i y hy
    cases i with
    | inl r =>
      obtain ⟨x, hx, rfl⟩ := m.shared σ ⟨r.val, hHK r.property⟩ hy.1
      exact hroof ⟨x, ⟨H.convexHull_subset_space r.property hx.2, hx.1⟩, rfl⟩
    | inr r => exact (disjoint_left.mp (hXshared r.val r.property) hy.1 hy.2.1).elim
  obtain ⟨T, hT, hTd, hTin, hcol, hinter⟩ :=
    exists_exceptional_column_complex_of_generalPosition_subsets hp hqp m.joint m.finite_faces
      m.vertices m.generalPosition (m.face σ) ((m.face_card σ).trans_le hσdim) t ht P hP
      s v hv (hshape.trans (m.face_image σ)) hshared
  refine ⟨T, hT, hTd, hTin, hcol, ?_⟩
  rintro y ⟨hy, hyσ⟩
  rcases hy with hyX | ⟨x, hxH, hxy⟩
  · obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.mp (hXcover ⟨hyX, hyσ⟩)
    exact hinter (Sum.inr ⟨t, ht⟩) ⟨hyσ, hyX, hyt⟩
  · obtain ⟨t, ht, hxt⟩ := SimplicialComplex.mem_space_iff.mp hxH
    have heq : raw x.val = y := by
      rw [← hHcoords x hxH ⟨y, hyσ, hxy.symm⟩, hxy, e.right_inv (hσtarget hyσ)]
    exact hinter (Sum.inl ⟨t, ht⟩) ⟨hyσ, x.val, hxt, heq⟩

end DifferentialGeometry.Topology.Engulfing
