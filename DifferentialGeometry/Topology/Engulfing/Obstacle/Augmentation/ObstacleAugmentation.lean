import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Quotient.LocalGeometricQuotient
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Geometry.DisjointGeometricUnion
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.RelativeBarycentricApproximation

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E : Type*} [DecidableEq E]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n d p : ℕ}

theorem geometricUnionLeft_mem_space_iff
    (L : SimplicialComplex ℝ E) (T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (x : E) :
    geometricUnionLeft x ∈ (geometricDisjointUnion L T).space ↔ x ∈ L.space := by
  rw [geometricDisjointUnion_space]
  constructor
  · rintro (⟨y, hy, he⟩ | ⟨y, hy, he⟩)
    · exact geometricUnionLeft_injective he ▸ hy
    · have he' : (1 : ℝ) = 0 := congrArg (fun z => z.2.2) he
      norm_num at he'
  · intro hx
    exact Or.inl (mem_image_of_mem _ hx)

structure ObstacleAugmentation
    (K L : SimplicialComplex ℝ E) (T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (f : C(K.space, EuclideanSpace ℝ (Fin n))) (d p : ℕ) where
  ambientDimension : ℕ
  joint : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin ambientDimension))
  joint_finite : joint.faces.Finite
  joint_dimension : ∀ s ∈ joint.faces, s.card ≤ d + 1
  sourceMap : C(K.space, joint.space)
  sourceMap_embedding : IsClosedEmbedding sourceMap
  obstacleMap : C(T.space, joint.space)
  obstacleMap_embedding : IsClosedEmbedding obstacleMap
  oldMap : C(joint.space, EuclideanSpace ℝ (Fin n))
  oldMap_source : ∀ x, oldMap (sourceMap x) = f x
  oldMap_obstacle : ∀ y, oldMap (obstacleMap y) = y.val
  sourceImage : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin ambientDimension))
  sourceImage_faces : sourceImage.faces ⊆ joint.faces
  sourceImage_space : sourceImage.space = range (fun x => (sourceMap x).val)
  sourceImage_dimension : ∀ s ∈ sourceImage.faces, s.card ≤ d + 1
  sourceImage_sections : hasFacewiseAffineSections K K joint sourceImage sourceMap
  obstacleImage : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin ambientDimension))
  obstacleImage_faces : obstacleImage.faces ⊆ joint.faces
  obstacleImage_space : obstacleImage.space = range (fun y => (obstacleMap y).val)
  obstacleImage_dimension : ∀ s ∈ obstacleImage.faces, s.card ≤ p + 1
  fixedImage : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin ambientDimension))
  fixedImage_faces : fixedImage.faces ⊆ joint.faces
  source_fixed : ∀ x : K.space, x.val ∈ L.space → (sourceMap x).val ∈ fixedImage.space
  obstacle_fixed : obstacleImage.space ⊆ fixedImage.space
  fixed_injective : InjOn oldMap (Subtype.val ⁻¹' fixedImage.space)
  fixed_affine : ∀ s ∈ fixedImage.faces,
    ∃ A : EuclideanSpace ℝ (Fin ambientDimension) →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : joint.space, x.val ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin ambientDimension))) →
        oldMap x = A x.val
  intersection_fixed : ∀ x : K.space, (sourceMap x).val ∈ obstacleImage.space → x.val ∈ L.space

omit [DecidableEq E] in
theorem exists_obstacleAugmentation
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hLK : L.faces ⊆ K.faces)
    (T : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))) (hT : T.faces.Finite)
    (hKd : ∀ s ∈ K.faces, s.card ≤ d + 1)
    (hTp : ∀ s ∈ T.faces, s.card ≤ p + 1) (hpd : p ≤ d)
    (f : C(K.space, EuclideanSpace ℝ (Fin n)))
    (hPL : ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ x : K.space, x.val ∈ convexHull ℝ (s : Set E) → f x = A x.val)
    (hinj : InjOn f (Subtype.val ⁻¹' L.space)) :
    Nonempty (ObstacleAugmentation K L T f d p) := by
  classical
  let F := EuclideanSpace ℝ (Fin n)
  let U := geometricDisjointUnion K T
  let D := geometricDisjointUnion L T
  have hU : U.faces.Finite := geometricDisjointUnion_finite_faces K T hK hT
  have hDU : D.faces ⊆ U.faces := by
    rintro s (hs | hs)
    · exact Or.inl (geometricUnionLeftComplex_mono hLK hs)
    · exact Or.inr hs
  have hUd : ∀ s ∈ U.faces, s.card ≤ d + 1 :=
    geometricDisjointUnion_face_card_le K T hKd (fun s hs => (hTp s hs).trans (by omega))
  obtain ⟨F₀, hFl, hFr⟩ := exists_continuousMap_geometricDisjointUnion K T hK hT f
    (⟨Subtype.val, continuous_subtype_val⟩ : C(T.space, F))
  let f₀ : (E × F × ℝ) → F := fun x => if hx : x ∈ U.space then F₀ ⟨x, hx⟩ else 0
  have hf₀ (x : U.space) : f₀ x.val = F₀ x := by simp [f₀, x.property]
  let πl : (E × F × ℝ) →ᵃ[ℝ] E := (LinearMap.fst ℝ E (F × ℝ)).toAffineMap
  let πr : (E × F × ℝ) →ᵃ[ℝ] F :=
    ((LinearMap.fst ℝ F ℝ).comp (LinearMap.snd ℝ E (F × ℝ))).toAffineMap
  have hleft (x : K.space) : f₀ (geometricUnionLeft x.val) = f x :=
    (hf₀ (geometricDisjointUnionInl K T x)).trans (hFl x)
  have hright (y : T.space) : f₀ (geometricUnionRight y.val) = y.val :=
    (hf₀ (geometricDisjointUnionInr K T y)).trans (hFr y)
  have hfa : ∀ s ∈ D.faces, ∃ A : (E × F × ℝ) →ᵃ[ℝ] F,
      EqOn f₀ A (convexHull ℝ (s : Set (E × F × ℝ))) := by
    rintro s (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · obtain ⟨A, hA⟩ := hPL t ht
      refine ⟨A.comp πl, ?_⟩
      rw [Finset.coe_image, ← AffineMap.image_convexHull]
      rintro _ ⟨x, hx, rfl⟩
      exact (hleft ⟨x, K.convexHull_subset_space (hLK ht) hx⟩).trans
        (hA ⟨x, K.convexHull_subset_space (hLK ht) hx⟩ hx)
    · refine ⟨πr, ?_⟩
      rw [Finset.coe_image, ← AffineMap.image_convexHull]
      rintro _ ⟨y, hy, rfl⟩
      exact hright ⟨y, T.convexHull_subset_space ht hy⟩
  have hfi : ∀ s ∈ D.faces, InjOn f₀ (convexHull ℝ (s : Set (E × F × ℝ))) := by
    rintro s (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · rw [Finset.coe_image, ← AffineMap.image_convexHull]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
      have hxK := K.convexHull_subset_space (hLK ht) hx
      have hyK := K.convexHull_subset_space (hLK ht) hy
      rw [hleft ⟨x, hxK⟩, hleft ⟨y, hyK⟩] at he
      exact congrArg (fun z : K.space => geometricUnionLeft z.val)
        (hinj (L.convexHull_subset_space ht hx) (L.convexHull_subset_space ht hy) he)
    · rw [Finset.coe_image, ← AffineMap.image_convexHull]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ he
      rw [hright ⟨x, T.convexHull_subset_space ht hx⟩,
        hright ⟨y, T.convexHull_subset_space ht hy⟩] at he
      exact congrArg geometricUnionRight he
  obtain ⟨m, Q, q, G, hQ, hQd, hq, hrel, hfactor, hemb, himages, hqPL⟩ :=
    exists_local_geometric_polyhedral_quotient U D hU hDU f₀ hfa hfi hUd F₀
      (fun x y _ _ => by rw [hf₀ x, hf₀ y])
  let qK := q.comp (geometricDisjointUnionInl K T)
  let qT := q.comp (geometricDisjointUnionInr K T)
  have hqK (x : K.space) : G (qK x) = f x := (hfactor _).trans (hFl x)
  have hqT (y : T.space) : G (qT y) = y.val := (hfactor _).trans (hFr y)
  have hqKi : Function.Injective qK := by
    intro x y he
    rcases (hrel _ _).mp he with hxy | ⟨hx, hy, hfxy⟩
    · exact geometricDisjointUnionInl_injective K T hxy
    · have hxL := (geometricUnionLeft_mem_space_iff L T x.val).mp hx
      have hyL := (geometricUnionLeft_mem_space_iff L T y.val).mp hy
      exact hinj hxL hyL ((hqK x).symm.trans ((congrArg G he).trans (hqK y)))
  have hqTi : Function.Injective qT := by
    intro x y he
    exact Subtype.ext ((hqT x).symm.trans ((congrArg G he).trans (hqT y)))
  letI : CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces K hK)
  letI : CompactSpace T.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces T hT)
  have hleftU : (geometricUnionLeftComplex (F := F) K).faces ⊆ U.faces := fun _ hs => Or.inl hs
  have hrightU : (geometricUnionRightComplex (E := E) T).faces ⊆ U.faces := fun _ hs => Or.inr hs
  obtain ⟨QK, hQK, hQKspace, hQKdim, hQKsections⟩ := himages (geometricUnionLeftComplex (F := F) K) hleftU
  obtain ⟨QT, hQT, hQTspace, hQTdim, hQTsections⟩ := himages (geometricUnionRightComplex (E := E) T) hrightU
  obtain ⟨QD, hQD, hQDspace, hQDdim, hQDsections⟩ := himages D hDU
  have hKspace : QK.space = range (fun x => (qK x).val) := by
    rw [hQKspace]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [geometricUnionLeftComplex_space] at hx
      obtain ⟨z, hz, he⟩ := hx
      exact ⟨⟨z, hz⟩, congrArg (fun u => (q u).val) (Subtype.ext he)⟩
    · rintro ⟨x, rfl⟩
      refine ⟨geometricDisjointUnionInl K T x, ?_, rfl⟩
      rw [geometricUnionLeftComplex_space]
      exact mem_image_of_mem _ x.property
  have hTspace : QT.space = range (fun y => (qT y).val) := by
    rw [hQTspace]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [geometricUnionRightComplex_space] at hx
      obtain ⟨z, hz, he⟩ := hx
      exact ⟨⟨z, hz⟩, congrArg (fun u => (q u).val) (Subtype.ext he)⟩
    · rintro ⟨x, rfl⟩
      refine ⟨geometricDisjointUnionInr K T x, ?_, rfl⟩
      rw [geometricUnionRightComplex_space]
      exact mem_image_of_mem _ x.property
  have hDmem (x : Q.space) : x.val ∈ QD.space ↔ x ∈ q '' {z | z.val ∈ D.space} := by
    rw [hQDspace]
    constructor
    · rintro ⟨y, hy, he⟩
      exact ⟨y, hy, Subtype.ext he⟩
    · rintro ⟨y, hy, rfl⟩
      exact mem_image_of_mem _ hy
  refine ⟨⟨m, Q, hQ, hQd, qK, qK.continuous.isClosedEmbedding hqKi,
    qT, qT.continuous.isClosedEmbedding hqTi, G, hqK, hqT,
    QK, hQK, hKspace, ?_, ?_, QT, hQT, hTspace, ?_,
    QD, hQD, ?_, ?_, ?_, ?_, ?_⟩⟩
  · apply hQKdim (d + 1)
    rintro s ⟨t, ht, rfl⟩
    exact Finset.card_image_le.trans (hKd t ht)
  · intro t ht
    obtain ⟨s, ⟨u, hu, rfl⟩, B, hB⟩ := hQKsections t ht
    refine ⟨u, hu, πl.comp B, ?_⟩
    intro y hy
    obtain ⟨x, hxB, hxs, hqx⟩ := hB y hy
    rw [Finset.coe_image, ← AffineMap.image_convexHull] at hxs
    obtain ⟨z, hz, he⟩ := hxs
    let z' : K.space := ⟨z, K.convexHull_subset_space hu hz⟩
    have hinl : geometricDisjointUnionInl K T z' = x := Subtype.ext he
    refine ⟨z', ?_, hz, ?_⟩
    · change z = πl (B y)
      rw [← hxB, ← he]
      rfl
    · change (q (geometricDisjointUnionInl K T z')).val = y
      rwa [hinl]
  · apply hQTdim (p + 1)
    rintro s ⟨t, ht, rfl⟩
    exact Finset.card_image_le.trans (hTp t ht)
  · intro x hx
    exact (hDmem (qK x)).mpr ⟨geometricDisjointUnionInl K T x,
      (geometricUnionLeft_mem_space_iff L T x.val).mpr hx, rfl⟩
  · intro y hy
    rw [hTspace] at hy
    obtain ⟨z, rfl⟩ := hy
    apply (hDmem (qT z)).mpr
    refine ⟨geometricDisjointUnionInr K T z, ?_, rfl⟩
    change geometricUnionRight z.val ∈ (geometricDisjointUnion L T).space
    rw [geometricDisjointUnion_space L T]
    exact Or.inr (mem_image_of_mem _ z.property)
  · intro x hx y hy he
    exact congrArg Subtype.val (hemb.injective
      (a₁ := ⟨x, (hDmem x).mp hx⟩) (a₂ := ⟨y, (hDmem y).mp hy⟩) he)
  · intro t ht
    obtain ⟨s, hs, B, hB⟩ := hQDsections t ht
    obtain ⟨A, hA⟩ := hfa s hs
    refine ⟨A.comp B, ?_⟩
    intro y hy
    obtain ⟨x, hxB, hxs, hqx⟩ := hB y.val hy
    have he : q x = y := Subtype.ext hqx
    calc
      G y = F₀ x := by rw [← he, hfactor]
      _ = f₀ x.val := (hf₀ x).symm
      _ = A x.val := hA hxs
      _ = (A.comp B) y.val := by rw [hxB]; rfl
  · intro x hx
    rw [hTspace] at hx
    obtain ⟨y, he⟩ := hx
    have he' : q (geometricDisjointUnionInr K T y) = q (geometricDisjointUnionInl K T x) :=
      Subtype.ext he
    rcases (hrel _ _).mp he' with hxy | ⟨hyD, hxD, hfxy⟩
    · have hheight : (1 : ℝ) = 0 := congrArg (fun z => z.val.2.2) hxy
      norm_num at hheight
    · exact (geometricUnionLeft_mem_space_iff L T x.val).mp hxD

end

end DifferentialGeometry.Topology.Engulfing
