import DifferentialGeometry.Topology.SimplicialComplex.Realization.SimplicialGluing
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.PiecewiseLinear

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry _root_.Topology

noncomputable section

set_option linter.unusedSectionVars false

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq E]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def vertexEvaluation (v : ι → E) : (ι → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ v

omit [DecidableEq E] in
@[simp] theorem vertexEvaluation_single (v : ι → E) (i : ι) :
    vertexEvaluation v (Pi.single i 1) = v i := by
  classical
  simp [vertexEvaluation, Fintype.linearCombination_apply]

theorem vertexEvaluation_image_face (v : ι → E) (s : Finset ι) :
    vertexEvaluation v '' convexHull ℝ
      ((s.image (fun i => Pi.single i (1 : ℝ))) : Set (ι → ℝ)) =
      convexHull ℝ ((s.image v : Finset E) : Set E) := by
  rw [LinearMap.image_convexHull]
  congr 1
  ext y
  simp only [mem_image, Finset.mem_coe, Finset.mem_image]
  constructor
  · rintro ⟨x, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, (vertexEvaluation_single v i).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Pi.single i 1, ⟨i, hi, rfl⟩, vertexEvaluation_single v i⟩

theorem vertexEvaluation_image_space (P : PreAbstractSimplicialComplex ι) (v : ι → E)
    (K : SimplicialComplex ℝ E) (hfaces : K.faces = (P.map v).faces) :
    vertexEvaluation v '' (standardRealization P).space = K.space := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hx⟩ := (standardRealization_mem_space P x).mp hx
    apply K.convexHull_subset_space (s := s.image v)
    · rw [hfaces]
      exact ⟨s, hs, rfl⟩
    · rw [← vertexEvaluation_image_face]
      exact mem_image_of_mem _ hx
  · intro hy
    obtain ⟨t, ht, hyt⟩ := SimplicialComplex.mem_space_iff.mp hy
    rw [hfaces] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    rw [← vertexEvaluation_image_face] at hyt
    obtain ⟨x, hx, hxy⟩ := hyt
    exact ⟨x, (standardRealization_mem_space P x).mpr ⟨s, hs, hx⟩, hxy⟩

theorem vertexEvaluation_injOn_space (P : PreAbstractSimplicialComplex ι) (v : ι → E)
    (hv : Function.Injective v) (K : SimplicialComplex ℝ E)
    (hfaces : K.faces = (P.map v).faces) :
    InjOn (vertexEvaluation v) (standardRealization P).space := by
  classical
  have hK : K.faces.Finite := hfaces ▸ P.faces.toFinite.image _
  let w : E → (ι → ℝ) := fun y => if h : ∃ i, v i = y then Pi.single h.choose 1 else 0
  have hw (i : ι) : w (v i) = Pi.single i 1 := by
    dsimp [w]
    rw [dite_eq_left ⟨i, rfl⟩]
    congr 1
    exact hv (Exists.choose_spec (⟨i, rfl⟩ : ∃ j, v j = v i))
  let g := interpolateVertices K hK w
  have hinverse (x : (standardRealization P).space) :
      g ⟨vertexEvaluation v x, (vertexEvaluation_image_space P v K hfaces).subset
        (mem_image_of_mem _ x.2)⟩ = x.1 := by
    obtain ⟨s, hs, hx⟩ := (standardRealization_mem_space P x).mp x.2
    have hsk : s.image v ∈ K.faces := by rw [hfaces]; exact ⟨s, hs, rfl⟩
    obtain ⟨A, hA, hg⟩ := interpolateVertices_affineOn K hK w ⟨s.image v, hsk⟩
    change interpolateVertices K hK w _ = _
    rw [hg _ ((vertexEvaluation_image_face v s).subset (mem_image_of_mem _ hx))]
    apply AffineMap.eqOn_affineSpan
      (f := A.comp (vertexEvaluation v).toAffineMap) (g := AffineMap.id ℝ (ι → ℝ))
      (s := ((s.image (fun i => Pi.single i (1 : ℝ))) : Set (ι → ℝ)))
    · intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      change A (vertexEvaluation v (Pi.single i 1)) = Pi.single i 1
      rw [vertexEvaluation_single, hA _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩), hw]
    · exact convexHull_subset_affineSpan _ hx
  intro x hx y hy hxy
  have hh := congrArg g (show
      (⟨vertexEvaluation v x, (vertexEvaluation_image_space P v K hfaces).subset
        (mem_image_of_mem _ hx)⟩ : K.space) =
      ⟨vertexEvaluation v y, (vertexEvaluation_image_space P v K hfaces).subset
        (mem_image_of_mem _ hy)⟩ from Subtype.ext hxy)
  rw [hinverse ⟨x, hx⟩, hinverse ⟨y, hy⟩] at hh
  exact hh

def geometricRealizationHomeomorph (P : PreAbstractSimplicialComplex ι) (v : ι → E)
    (hv : Function.Injective v) (K : SimplicialComplex ℝ E)
    (hfaces : K.faces = (P.map v).faces) :
    (standardRealization P).space ≃ₜ K.space := by
  let f : (standardRealization P).space → K.space := fun x =>
    ⟨vertexEvaluation v x, (vertexEvaluation_image_space P v K hfaces).subset
      (mem_image_of_mem _ x.2)⟩
  have hf : Continuous f := ((vertexEvaluation v).continuous_of_finiteDimensional.comp
    continuous_subtype_val).subtype_mk _
  have hi : Function.Injective f := fun x y h => Subtype.ext
    (vertexEvaluation_injOn_space P v hv K hfaces x.2 y.2 (congrArg Subtype.val h))
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := (vertexEvaluation_image_space P v K hfaces).symm.subset y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hi, hs⟩) hf

@[simp] theorem geometricRealizationHomeomorph_apply
    (P : PreAbstractSimplicialComplex ι) (v : ι → E)
    (hv : Function.Injective v) (K : SimplicialComplex ℝ E)
    (hfaces : K.faces = (P.map v).faces) (x : (standardRealization P).space) :
    (geometricRealizationHomeomorph P v hv K hfaces x).1 = vertexEvaluation v x := rfl

theorem geometricRealizationHomeomorph_subcomplex
    (P D : PreAbstractSimplicialComplex ι) (hDP : D ≤ P) (v : ι → E)
    (hv : Function.Injective v) (K : SimplicialComplex ℝ E)
    (hfaces : K.faces = (P.map v).faces) :
    (fun x : (standardRealization P).space =>
      (geometricRealizationHomeomorph P v hv K hfaces x).1) ''
      {x | x.1 ∈ (standardRealization D).space} =
      ⋃ s ∈ D.faces, convexHull ℝ ((s.image v : Finset E) : Set E) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := (standardRealization_mem_space D x).mp hx
    apply mem_iUnion₂.mpr ⟨s, hs, ?_⟩
    exact (vertexEvaluation_image_face v s).subset (mem_image_of_mem _ hxs)
  · intro hy
    obtain ⟨s, hs, hys⟩ := mem_iUnion₂.mp hy
    rw [← vertexEvaluation_image_face] at hys
    obtain ⟨x, hx, hxy⟩ := hys
    refine ⟨⟨x, (standardRealization_mem_space P x).mpr ⟨s, hDP hs, hx⟩⟩, ?_, hxy⟩
    exact (standardRealization_mem_space D x).mpr ⟨s, hs, hx⟩

theorem geometricRealizationHomeomorph_inverse_affine
    (P : PreAbstractSimplicialComplex ι) (v : ι → E)
    (hv : Function.Injective v) (K : SimplicialComplex ℝ E)
    (hfaces : K.faces = (P.map v).faces) (s : Finset ι) (hs : s ∈ P.faces) :
    ∃ A : E →ᵃ[ℝ] (ι → ℝ), ∀ y : K.space,
      y.1 ∈ convexHull ℝ ((s.image v : Finset E) : Set E) →
      ((geometricRealizationHomeomorph P v hv K hfaces).symm y).1 = A y.1 := by
  classical
  let w : E → (ι → ℝ) := fun y => if h : ∃ i, v i = y then Pi.single h.choose 1 else 0
  have hw (i : ι) : w (v i) = Pi.single i 1 := by
    dsimp [w]
    rw [dite_eq_left ⟨i, rfl⟩]
    congr 1
    exact hv (Exists.choose_spec (⟨i, rfl⟩ : ∃ j, v j = v i))
  have hsk : s.image v ∈ K.faces := by rw [hfaces]; exact ⟨s, hs, rfl⟩
  obtain ⟨A, hA⟩ := exists_affineMap_of_affineIndependent (K.indep hsk) w
  have hleft (x : ι → ℝ) (hx : x ∈ convexHull ℝ
      ((s.image (fun i => Pi.single i (1 : ℝ))) : Set (ι → ℝ))) :
      A (vertexEvaluation v x) = x := by
    apply AffineMap.eqOn_affineSpan
      (f := A.comp (vertexEvaluation v).toAffineMap) (g := AffineMap.id ℝ (ι → ℝ))
      (s := ((s.image (fun i => Pi.single i (1 : ℝ))) : Set (ι → ℝ)))
    · intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      change A (vertexEvaluation v (Pi.single i 1)) = Pi.single i 1
      rw [vertexEvaluation_single, hA _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩), hw]
    · exact convexHull_subset_affineSpan _ hx
  refine ⟨A, ?_⟩
  intro y hy
  rw [← vertexEvaluation_image_face] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  let x' : (standardRealization P).space :=
    ⟨x, (standardRealization_mem_space P x).mpr ⟨s, hs, hx⟩⟩
  let H := geometricRealizationHomeomorph P v hv K hfaces
  have hH : H x' = y := Subtype.ext hxy
  change (H.symm y).1 = A y.1
  rw [← hH, H.symm_apply_apply]
  exact (hleft x hx).symm

def abstractVertexComplex (K : SimplicialComplex ℝ E) :
    PreAbstractSimplicialComplex K.vertices where
  faces := {s | s.image Subtype.val ∈ K.faces}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨Finset.image_nonempty.mp (K.nonempty_of_mem_faces hs), ?_⟩
    intro t hts ht
    exact K.down_closed hs (Finset.image_subset_image hts) (Finset.image_nonempty.mpr ht)

theorem abstractVertexComplex_map (K : SimplicialComplex ℝ E) :
    ((abstractVertexComplex K).map Subtype.val).faces = K.faces := by
  classical
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hs
    let j : s → K.vertices := fun x => ⟨x.1, K.down_closed hs
      (Finset.singleton_subset_iff.mpr x.2) (Finset.singleton_nonempty _)⟩
    let t : Finset K.vertices := s.attach.image j
    have ht : t.image Subtype.val = s := by
      change (s.attach.image j).image Subtype.val = s
      rw [Finset.image_image]
      change s.attach.image Subtype.val = s
      exact Finset.attach_image_val
    refine ⟨t, ?_, ht⟩
    change t.image Subtype.val ∈ K.faces
    rwa [ht]

omit [DecidableEq E] in
theorem finite_vertices_of_finite_faces (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    K.vertices.Finite := by
  classical
  rw [K.vertices_eq]
  exact hK.biUnion (fun s _ => s.finite_toSet)

theorem abstractVertexComplex_face_card_le (K : SimplicialComplex ℝ E) {d : ℕ}
    (hd : ∀ s ∈ K.faces, s.card ≤ d) :
    ∀ s ∈ (abstractVertexComplex K).faces, s.card ≤ d := by
  intro s hs
  have h := hd (s.image Subtype.val) hs
  rwa [Finset.card_image_of_injective _ Subtype.val_injective] at h

def standardGeometricHomeomorph (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    letI : Fintype K.vertices := (finite_vertices_of_finite_faces K hK).fintype
    (standardRealization (abstractVertexComplex K)).space ≃ₜ K.space := by
  letI : Fintype K.vertices := (finite_vertices_of_finite_faces K hK).fintype
  exact geometricRealizationHomeomorph (abstractVertexComplex K) Subtype.val
    Subtype.val_injective K (abstractVertexComplex_map K).symm

end

end DifferentialGeometry.Topology.Engulfing
