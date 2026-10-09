import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedral.Maps.SimplicialPullback
import DifferentialGeometry.Topology.SimplicialComplex.Realization.GeometricRealization
import DifferentialGeometry.Topology.SimplicialComplex.Realization.BarycentricRealization

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [DecidableEq E] [DecidableEq F]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def geometricSimplicialVertexMap (L : SimplicialComplex ℝ E) (T : SimplicialComplex ℝ F)
    (f : E → F) (hmap : ∀ s ∈ L.faces, s.image f ∈ T.faces) : L.vertices → T.vertices :=
  fun x => ⟨f x.val, by
    change {f x.val} ∈ T.faces
    simpa using hmap {x.val} x.property⟩

theorem geometricSimplicialVertexMap_image_val
    (L : SimplicialComplex ℝ E) (T : SimplicialComplex ℝ F)
    (f : E → F) (hmap : ∀ s ∈ L.faces, s.image f ∈ T.faces) (s : Finset L.vertices) :
    (s.image (geometricSimplicialVertexMap L T f hmap)).image Subtype.val =
      (s.image Subtype.val).image f := by
  rw [Finset.image_image, Finset.image_image]
  rfl

theorem geometricSimplicialVertexMap_face
    (L : SimplicialComplex ℝ E) (T : SimplicialComplex ℝ F)
    (f : E → F) (hmap : ∀ s ∈ L.faces, s.image f ∈ T.faces)
    {s : Finset L.vertices} (hs : s ∈ (abstractVertexComplex L).faces) :
    s.image (geometricSimplicialVertexMap L T f hmap) ∈ (abstractVertexComplex T).faces := by
  change (s.image (geometricSimplicialVertexMap L T f hmap)).image Subtype.val ∈ T.faces
  rw [geometricSimplicialVertexMap_image_val]
  exact hmap (s.image Subtype.val) hs

theorem geometricSimplicialVertexMap_image_complex
    [FiniteDimensional ℝ E]
    (L : SimplicialComplex ℝ E) (T : SimplicialComplex ℝ F)
    (f : E → F) (hmap : ∀ s ∈ L.faces, s.image f ∈ T.faces)
    (honto : ∀ t ∈ T.faces, ∃ s ∈ L.faces, s.image f = t) :
    (abstractVertexComplex L).map (geometricSimplicialVertexMap L T f hmap) =
      abstractVertexComplex T := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact geometricSimplicialVertexMap_face L T f hmap hs
  · intro ht
    obtain ⟨u, hu, hut⟩ := honto (t.image Subtype.val) ht
    have hu' : u ∈ ((abstractVertexComplex L).map Subtype.val).faces :=
      (abstractVertexComplex_map L).symm ▸ hu
    obtain ⟨s, hs, hsu⟩ := hu'
    refine ⟨s, hs, ?_⟩
    change s.image (geometricSimplicialVertexMap L T f hmap) = t
    apply Finset.image_injective Subtype.val_injective
    rw [geometricSimplicialVertexMap_image_val]
    change s.image Subtype.val = u at hsu
    rw [hsu, hut]

theorem geometricSimplicialVertexMap_injOn_face
    (L : SimplicialComplex ℝ E) (T : SimplicialComplex ℝ F)
    (f : E → F) (hmap : ∀ s ∈ L.faces, s.image f ∈ T.faces)
    (hinj : ∀ s ∈ L.faces, InjOn f (convexHull ℝ (s : Set E))) :
    ∀ s ∈ (abstractVertexComplex L).faces,
      (s : Set L.vertices).InjOn (geometricSimplicialVertexMap L T f hmap) := by
  intro s hs x hx y hy hxy
  apply Subtype.ext
  apply hinj (s.image Subtype.val) hs
    (subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    (subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩))
  exact congrArg Subtype.val hxy

theorem geometricSimplicialVertexMap_evaluation
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : SimplicialComplex ℝ E) (T : SimplicialComplex ℝ F)
    [Fintype L.vertices] [Fintype T.vertices]
    (f : E → F) (hmap : ∀ s ∈ L.faces, s.image f ∈ T.faces)
    (hf : ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    {x : L.vertices → ℝ} (hx : x ∈ (standardRealization (abstractVertexComplex L)).space) :
    f (vertexEvaluation Subtype.val x) =
      vertexEvaluation Subtype.val (vertexPushforward (geometricSimplicialVertexMap L T f hmap) x) := by
  rw [vertexEvaluation_vertexPushforward]
  obtain ⟨s, hs, hxs⟩ := (standardRealization_mem_space _ _).mp hx
  obtain ⟨A, hA⟩ := hf (s.image Subtype.val) hs
  have hxgeom : vertexEvaluation Subtype.val x ∈ convexHull ℝ (s.image Subtype.val : Set E) :=
    (vertexEvaluation_image_face Subtype.val s).subset (mem_image_of_mem _ hxs)
  rw [hA hxgeom]
  apply AffineMap.eqOn_affineSpan
    (f := A.comp (vertexEvaluation (Subtype.val : L.vertices → E)).toAffineMap)
    (g := (vertexEvaluation (Subtype.val ∘ geometricSimplicialVertexMap L T f hmap)).toAffineMap)
    (s := (s.image (fun i => Pi.single i (1 : ℝ)) : Set (L.vertices → ℝ)))
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    change A (vertexEvaluation Subtype.val (Pi.single i 1)) =
      vertexEvaluation (Subtype.val ∘ geometricSimplicialVertexMap L T f hmap) (Pi.single i 1)
    rw [vertexEvaluation_single, vertexEvaluation_single]
    exact (hA (subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩))).symm
  · exact convexHull_subset_affineSpan _ hxs

theorem geometricSimplicialVertexMap_fiber_iff
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (L : SimplicialComplex ℝ E) (T : SimplicialComplex ℝ F)
    [Fintype L.vertices] [Finite T.vertices]
    (f : E → F) (hmap : ∀ s ∈ L.faces, s.image f ∈ T.faces)
    (hf : ∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    {x y : L.vertices → ℝ}
    (hx : x ∈ (standardRealization (abstractVertexComplex L)).space)
    (hy : y ∈ (standardRealization (abstractVertexComplex L)).space) :
    f (vertexEvaluation Subtype.val x) = f (vertexEvaluation Subtype.val y) ↔
      vertexPushforward (geometricSimplicialVertexMap L T f hmap) x =
        vertexPushforward (geometricSimplicialVertexMap L T f hmap) y := by
  classical
  let : Fintype ↑T.vertices := Fintype.ofFinite ↑T.vertices
  rw [geometricSimplicialVertexMap_evaluation L T f hmap hf hx,
    geometricSimplicialVertexMap_evaluation L T f hmap hf hy]
  have hm : (abstractVertexComplex L).map (geometricSimplicialVertexMap L T f hmap) ≤
      abstractVertexComplex T := by
    rintro s ⟨t, ht, rfl⟩
    exact geometricSimplicialVertexMap_face L T f hmap ht
  have hmem {z : L.vertices → ℝ} (hz : z ∈ (standardRealization (abstractVertexComplex L)).space) :
      vertexPushforward (geometricSimplicialVertexMap L T f hmap) z ∈
        (standardRealization (abstractVertexComplex T)).space :=
    standardRealization_mono hm ((vertexPushforward_image_space _ _).subset (mem_image_of_mem _ hz))
  exact ⟨fun h => vertexEvaluation_injOn_space (abstractVertexComplex T) Subtype.val
    Subtype.val_injective T (abstractVertexComplex_map T).symm (hmem hx) (hmem hy) h,
    congrArg (vertexEvaluation Subtype.val)⟩

theorem exists_compatible_abstract_simplicial_refinement [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E)))
    (hinj : ∀ s ∈ K.faces, InjOn f (convexHull ℝ (s : Set E)))
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∃ L : SimplicialComplex ℝ E, ∃ T : SimplicialComplex ℝ F, ∃ q : L.vertices → T.vertices,
      L.faces.Finite ∧ T.faces.Finite ∧ L.space = K.space ∧ T.space = f '' K.space ∧
      simplicialRefines L K ∧ (∀ s ∈ L.faces, s.card ≤ d + 1) ∧
      (∀ t ∈ T.faces, t.card ≤ d + 1) ∧
      (abstractVertexComplex L).map q = abstractVertexComplex T ∧
      (∀ s ∈ (abstractVertexComplex L).faces, (s : Set L.vertices).InjOn q) ∧
      (∀ x : L.vertices, (q x).val = f x.val) ∧
      (∀ s ∈ L.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E))) := by
  obtain ⟨L, T, hL, hT, hspaceL, hspaceT, href, hdimL, hdimT, hmap, honto, hAff, hinjL⟩ :=
    exists_compatible_simplicial_refinement K hK f hf hinj hd
  exact ⟨L, T, geometricSimplicialVertexMap L T f hmap,
    hL, hT, hspaceL, hspaceT, href, hdimL, hdimT,
    geometricSimplicialVertexMap_image_complex L T f hmap honto,
    geometricSimplicialVertexMap_injOn_face L T f hmap hinjL, fun _ => rfl, hAff⟩

end

end DifferentialGeometry.Topology.Engulfing
