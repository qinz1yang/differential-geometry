import DifferentialGeometry.Topology.Engulfing.Obstacle.Approximation.ObstacleGeneralPosition
import DifferentialGeometry.Topology.Engulfing.Obstacle.Augmentation.ObstacleExpansionPullback

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

noncomputable section

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n d p : ℕ} {ε : ℝ} {K L : SimplicialComplex ℝ E}
  {T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))}
  {f : C(K.space, EuclideanSpace ℝ (Fin n))}

def RelativeGeneralPositionApproximation.rawMap (a : RelativeGeneralPositionApproximation K L T f d p ε) :
    C(K.space, EuclideanSpace ℝ (Fin n)) :=
  ⟨fun x => a.correction.symm (a.approximation x),
    a.correction.symm.continuous.comp a.approximation.continuous⟩

omit [FiniteDimensional ℝ E] in
theorem RelativeGeneralPositionApproximation.rawMap_source
    (a : RelativeGeneralPositionApproximation K L T f d p ε) (x : K.space) :
    a.rawMap x = interpolateVertices a.augmentation.joint a.augmentation.joint_finite
      a.vertices (a.augmentation.sourceMap x) := by
  change a.correction.symm (a.approximation x) = _
  rw [a.source_exact, correctedInterpolant_apply, a.correction.symm_apply_apply]

structure ObstaclePullbackModel (a : RelativeGeneralPositionApproximation K L T f d p ε) where
  source : SimplicialComplex ℝ E
  finite_faces : source.faces.Finite
  space : source.space = K.space
  refines : simplicialRefines source K
  dimension : ∀ s ∈ source.faces, s.card ≤ d + 1
  inverse : EuclideanSpace ℝ (Fin a.augmentation.ambientDimension) → E
  inverse_exact : ∀ y : a.augmentation.sourceImage.space,
    inverse y.val = (a.augmentation.sourceHomeomorph.symm y).val
  faces : source.faces = {s | ∃ t ∈ a.augmentation.sourceImage.faces, t.image inverse = s}
  source_face_image : ∀ t ∈ a.augmentation.sourceImage.faces,
    (fun x : K.space => (a.augmentation.sourceMap x).val) ''
      {x | x.val ∈ convexHull ℝ (t.image inverse : Set E)} =
        convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension)))
  affine : ∀ s ∈ source.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
    (∀ x : K.space, x.val ∈ convexHull ℝ (s : Set E) → a.rawMap x = A x.val) ∧
      InjOn A (convexHull ℝ (s : Set E))
  face_image : ∀ s ∈ source.faces, ∃ t ∈ a.augmentation.sourceImage.faces,
    t.image inverse = s ∧ t.card = s.card ∧
      a.rawMap '' {x : K.space | x.val ∈ convexHull ℝ (s : Set E)} =
        convexHull ℝ (a.vertices ''
          (t : Set (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension))))
  expansions : ∀ A C, C ⊆ K.space → FiniteSimplexExpansionIn K A C →
    FiniteSimplexExpansionIn source A C

theorem RelativeGeneralPositionApproximation.exists_pullbackModel
    (a : RelativeGeneralPositionApproximation K L T f d p ε) (hdn : d ≤ n) :
    Nonempty (ObstaclePullbackModel a) := by
  obtain ⟨r, R, hR, hRs, href, hdim, hr, hra, hri, hRf, hfaces, hexp⟩ :=
    a.augmentation.exists_source_subdivision_preserving_expansions a.expansions
  have hrsource (x : K.space) : r (a.augmentation.sourceMap x).val = x.val := by
    have h := hr (a.augmentation.sourceHomeomorph x)
    simpa only [a.augmentation.sourceHomeomorph.symm_apply_apply,
      ObstacleAugmentation.sourceHomeomorph_apply] using h
  have hmap (t : Finset (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension)))
      (ht : t ∈ a.augmentation.sourceImage.faces) (x : K.space)
      (hx : x.val ∈ convexHull ℝ (t.image r : Set E)) :
      (a.augmentation.sourceMap x).val ∈ convexHull ℝ (t : Set _) :=
    (hfaces t ht).subset (mem_image_of_mem _ hx)
  have hface_subtype (t : Finset (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension)))
      (ht : t ∈ a.augmentation.sourceImage.faces) :
      a.augmentation.sourceMap '' {x : K.space | x.val ∈ convexHull ℝ (t.image r : Set E)} =
        {y : a.augmentation.joint.space | y.val ∈ convexHull ℝ (t : Set _)} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hmap t ht x hx
    · intro hy
      obtain ⟨x, hx, he⟩ := (hfaces t ht).symm.subset hy
      exact ⟨x, hx, Subtype.ext he⟩
  have hind (t : Finset (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension)))
      (ht : t ∈ a.augmentation.sourceImage.faces) :
      AffineIndependent ℝ (fun x : t => a.vertices x.val) :=
    a.generalPosition t
      (face_vertices_subset a.augmentation.joint ⟨t, a.augmentation.sourceImage_faces ht⟩)
      ((a.augmentation.sourceImage_dimension t ht).trans (Nat.add_le_add_right hdn 1))
  have hinj (t : Finset (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension)))
      (ht : t ∈ a.augmentation.sourceImage.faces) :
      InjOn a.rawMap {x : K.space | x.val ∈ convexHull ℝ (t.image r : Set E)} := by
    intro x hx y hy he
    apply a.augmentation.sourceMap_embedding.injective
    apply interpolateVertices_injOn_face a.augmentation.joint a.augmentation.joint_finite
      a.vertices ⟨t, a.augmentation.sourceImage_faces ht⟩ (hind t ht)
      (hmap t ht x hx) (hmap t ht y hy)
    simpa only [← a.rawMap_source] using he
  refine ⟨⟨R, hR, hRs, href, hdim, r, hr, hRf, hfaces, ?_, ?_, hexp⟩⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := hRf.subset hs
    obtain ⟨A, hA⟩ := hra t ht
    have hAi : InjOn A (convexHull ℝ (t : Set _)) := by
      intro x hx y hy he
      exact hri (a.augmentation.sourceImage.convexHull_subset_space ht hx)
        (a.augmentation.sourceImage.convexHull_subset_space ht hy)
        ((hA hx).trans (he.trans (hA hy).symm))
    obtain ⟨B, hBA, -⟩ := exists_affine_inverse_on_affineSpan
      (a.augmentation.sourceImage.nonempty_of_mem_faces ht) A
      (affineIndependent_of_injOn_convexHull (a.augmentation.sourceImage.indep ht) A hAi)
    obtain ⟨D, -, hD⟩ := interpolateVertices_affineOn a.augmentation.joint
      a.augmentation.joint_finite a.vertices ⟨t, a.augmentation.sourceImage_faces ht⟩
    have hB (x : K.space) (hx : x.val ∈ convexHull ℝ (t.image r : Set E)) :
        B x.val = (a.augmentation.sourceMap x).val := by
      have hm := hmap t ht x hx
      have he := hBA (a.augmentation.sourceMap x).val (convexHull_subset_affineSpan _ hm)
      rw [← hA hm, hrsource x] at he
      exact he
    have heq (x : K.space) (hx : x.val ∈ convexHull ℝ (t.image r : Set E)) :
        a.rawMap x = (D.comp B) x.val := by
      rw [a.rawMap_source, hD _ (hmap t ht x hx)]
      exact congrArg D (hB x hx).symm
    refine ⟨D.comp B, heq, ?_⟩
    intro x hx y hy he
    have hxK : x ∈ K.space := hRs.subset (R.convexHull_subset_space hs hx)
    have hyK : y ∈ K.space := hRs.subset (R.convexHull_subset_space hs hy)
    have he' : a.rawMap ⟨x, hxK⟩ = a.rawMap ⟨y, hyK⟩ :=
      (heq ⟨x, hxK⟩ hx).trans (he.trans (heq ⟨y, hyK⟩ hy).symm)
    exact congrArg Subtype.val (hinj t ht hx hy he')
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := hRf.subset hs
    refine ⟨t, ht, rfl, ?_, ?_⟩
    · exact (Finset.card_image_of_injOn (fun x hx y hy he =>
        hri (a.augmentation.sourceImage.subset_space ht hx)
          (a.augmentation.sourceImage.subset_space ht hy) he)).symm
    · calc
        a.rawMap '' {x : K.space | x.val ∈ convexHull ℝ (t.image r : Set E)} =
            (fun x => interpolateVertices a.augmentation.joint a.augmentation.joint_finite
              a.vertices (a.augmentation.sourceMap x)) ''
                {x : K.space | x.val ∈ convexHull ℝ (t.image r : Set E)} :=
          image_congr (fun x _ => a.rawMap_source x)
        _ = interpolateVertices a.augmentation.joint a.augmentation.joint_finite a.vertices ''
              {y : a.augmentation.joint.space | y.val ∈ convexHull ℝ (t : Set _)} := by
          rw [← image_image, hface_subtype t ht]
        _ = _ := interpolateVertices_image_face a.augmentation.joint a.augmentation.joint_finite
          a.vertices ⟨t, a.augmentation.sourceImage_faces ht⟩

namespace ObstaclePullbackModel

variable {a : RelativeGeneralPositionApproximation K L T f d p ε} (m : ObstaclePullbackModel a)

omit [FiniteDimensional ℝ E] in
theorem inverse_source (x : K.space) : m.inverse (a.augmentation.sourceMap x).val = x.val := by
  have h := m.inverse_exact (a.augmentation.sourceHomeomorph x)
  rw [a.augmentation.sourceHomeomorph.symm_apply_apply] at h
  exact h

omit [FiniteDimensional ℝ E] in
theorem inverse_mem_fixed_of_obstacle {y : EuclideanSpace ℝ (Fin a.augmentation.ambientDimension)}
    (hy : y ∈ a.augmentation.sourceImage.space) (hyT : y ∈ a.augmentation.obstacleImage.space) :
    m.inverse y ∈ L.space := by
  let y' : a.augmentation.sourceImage.space := ⟨y, hy⟩
  let x : K.space := a.augmentation.sourceHomeomorph.symm y'
  have hx : (a.augmentation.sourceMap x).val = y :=
    congrArg Subtype.val (a.augmentation.sourceHomeomorph.apply_symm_apply y')
  rw [m.inverse_exact y']
  exact a.augmentation.intersection_fixed x (hx.symm ▸ hyT)

omit [FiniteDimensional ℝ E] in
theorem shared_face_vertex_mem_fixed
    {s t : Finset (EuclideanSpace ℝ (Fin a.augmentation.ambientDimension))}
    (hs : s ∈ a.augmentation.sourceImage.faces) (ht : t ∈ a.augmentation.obstacleImage.faces)
    {y : EuclideanSpace ℝ (Fin a.augmentation.ambientDimension)} (hys : y ∈ s) (hyt : y ∈ t) :
    m.inverse y ∈ L.space :=
  m.inverse_mem_fixed_of_obstacle (a.augmentation.sourceImage.subset_space hs hys)
    (a.augmentation.obstacleImage.subset_space ht hyt)

omit [FiniteDimensional ℝ E] in
theorem rawMap_injOn_face {s : Finset E} (hs : s ∈ m.source.faces) :
    InjOn a.rawMap {x : K.space | x.val ∈ convexHull ℝ (s : Set E)} := by
  obtain ⟨A, hA, hinj⟩ := m.affine s hs
  intro x hx y hy he
  apply Subtype.ext
  apply hinj hx hy
  rw [← hA x hx, ← hA y hy]
  exact he

end ObstaclePullbackModel

end

end DifferentialGeometry.Topology.Engulfing
