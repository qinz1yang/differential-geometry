import DifferentialGeometry.Topology.PiecewiseLinear.HeightLocalization
import DifferentialGeometry.Topology.PiecewiseLinear.FiberInterior
import DifferentialGeometry.Topology.PiecewiseLinear.ParameterizedTriangleCap

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem mem_vertices_of_faces_subset_of_mem_space
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces)
    {q : E} (hqK : q ∈ K.vertices) (hqL : q ∈ L.space) : q ∈ L.vertices := by
  obtain ⟨s, hs, hqs⟩ := L.mem_space_iff.mp hqL
  have hsub : {q} ⊆ s := face_subset_of_mem_openSimplex_of_mem_convexHull K hqK
    (hLK hs) (mem_openSimplex_singleton q) hqs
  exact L.down_closed hs hsub (Finset.singleton_nonempty q)

theorem exists_triangle_cap_with_singular_comparison
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [dE : DecidableEq E] (hdimE : Module.finrank ℝ E = 3)
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere 2 K.space)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} {Q Q' D J C : Set E}
    {u v : (Fin 3 → ℝ) → E}
    (hu : IsPLHomeomorphOn u (stdSimplex ℝ (Fin 3)) Q)
    (hv : IsPLHomeomorphOn v (stdSimplex ℝ (Fin 3)) D)
    (huJ : u '' stdSimplexBoundary 2 = J) (hvJ : v '' stdSimplexBoundary 2 = J)
    (hQD : IsPLSphere 2 (Q ∪ D)) (hunion : Q ∪ Q' = K.space)
    (hQ' : IsClosed Q') (hinter : Q ∩ Q' ⊆ D) (hQDinter : Q ∩ D ⊆ J)
    (hDlevel : D ⊆ {x | ℓ x = ℓ p}) (hDC : D ⊆ C) (hC : IsCompact C)
    (hsep : ∀ q ∈ K.vertices \ {p}, Disjoint C {x | ℓ x = ℓ q})
    (H : E ≃ₜ E) (hH : IsPLHomeomorphOn H univ univ) (hfix : EqOn H id Cᶜ)
    (hfixV : EqOn H id (K.vertices \ {p})) (hheight : ∀ x, ℓ (H x) = ℓ x)
    (e : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] E)
    (T : Finset (EuclideanSpace ℝ (Fin 2)))
    (hT : AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 2)))
    (hcard : T.card = 3) (he : Function.Injective e)
    (htriangle : H '' D = e '' convexHull ℝ (T : Set _))
    (hhalf : ∀ q ∈ J \ {p}, ∀ᶠ x in 𝓝 q, x ∈ Q → ℓ x ≤ ℓ q)
    (hboundary : ∀ q ∈ J \ {p},
      ∀ᶠ x in 𝓝 q, x ∈ J ↔ x ∈ Q ∧ ℓ x = ℓ q) :
    ∃ R : Geometry.SimplicialComplex ℝ E, R.faces.Finite ∧
      R.space = H '' (Q ∪ D) ∧ IsPLSphere 2 R.space ∧
      ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, f ≠ 0 →
        InjOn f (R.vertices ∪ ((T.image e : Finset E) : Set E)) →
        (∀ x ∈ H '' D \ {H p}, f (H p) < f x) →
        heightSingularPoints R.space f \ {H p} ⊆
            heightSingularPoints K.space ℓ \ {p} ∧
        ∀ q ∈ K.vertices \ {p},
          (q ∈ heightSingularPoints R.space f ↔
            q ∈ heightSingularPoints K.space ℓ ∧ q ∈ Q) ∧
          (levelPolygons R.space f (f q)).encard ≤
            (levelPolygons K.space ℓ (ℓ q)).encard := by
  classical
  cases Subsingleton.elim dE (Classical.decEq E)
  obtain ⟨R, hRfin, hRspace, hR, hRQ, -, hRQboundary, -, -, hregular⟩ :=
    exists_triangulation_triangle_cap_with_nonsingular_boundary hdimE hu hv huJ hvJ
      hQD H hH ℓ hheight e T hT hcard he htriangle hhalf hboundary
  let _ : Finite R.faces := hRfin.to_subtype
  let M := restrict R (H '' Q)
  let _ : Finite M.faces := (restrict_faces_finite R (H '' Q)).to_subtype
  have hQ : IsPLBall 2 Q := ⟨u, hu⟩
  have hD : IsPLBall 2 D := ⟨v, hv⟩
  have hABimage : H '' Q ∩ H '' D ⊆ (H ∘ v) '' stdSimplexBoundary 2 := by
    rintro _ ⟨⟨x, hxQ, rfl⟩, y, hyD, heq⟩
    have hyx : y = x := H.injective heq
    have hxJ : x ∈ J := hQDinter ⟨hxQ, hyx ▸ hyD⟩
    rw [image_comp, hvJ]
    exact mem_image_of_mem H hxJ
  have hlevel : H '' D ⊆ {x | ℓ x = ℓ p} := by
    rintro _ ⟨x, hxD, rfl⟩
    exact (hheight x).trans (hDlevel hxD)
  have hvH : IsPLHomeomorphOn (H ∘ v) (stdSimplex ℝ (Fin 3)) (H '' D) :=
    hv.trans (hH.restrict hD.isPolyhedron (subset_univ D))
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) hz
  have hlocal :=
    eventually_heightSingularPoints_image_cap_sdiff_subset_and_encard_levelPolygons_le
      K R hK hR.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
      hdimE ℓ hℓ hinj p hunion hQ' hD.isPolyhedron.isClosed hinter hDC hC hsep
      H hH hfix hheight hRspace
  have hvertices := eventually_heightSingularPoints_image_cap_sdiff_subset_vertices
    K R hK.isCombinatorialManifold
      hR.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
      hdimE ℓ hinj hunion hQ' hD.isPolyhedron.isClosed hinter H hH hheight hRspace
  refine ⟨R, hRfin, hRspace, hR, ?_⟩
  filter_upwards [hregular, hlocal, hvertices] with f hfregular hflocal hfvertices
  intro hfne hfinj hnewsep
  have hfinjR : InjOn f R.vertices := hfinj.mono subset_union_left
  obtain ⟨houtside, hpoints⟩ := hflocal hfne hfinjR
  have hvertexImage := hfvertices hfne hfinjR
  have hflinear : f.toLinearMap ≠ 0 := by
    intro hz
    apply hfne
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) hz
  have hinner := heightSingularPoints_cap_inter_subset_image_boundary
    hdimE ℓ.toLinearMap hlinear (H.isClosedMap Q hQ.isPolyhedron.isClosed)
      hvH hlevel hABimage (hheight p) f.toLinearMap
      (fun x hx heq => (ne_of_lt (hnewsep x hx)) heq.symm)
  rw [← image_union, ← hRspace, image_comp] at hinner
  refine ⟨?_, hpoints⟩
  rintro q ⟨hqsing, hqHp⟩
  by_cases hqD : q ∈ H '' D
  · rcases hinner ⟨hqsing, hqD⟩ with hqJ | hqHp'
    · have hqR : q ∈ R.vertices := heightSingularPoints_subset_vertices R
        hR.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
        hdimE f.toLinearMap hflinear hfinjR hqsing
      have hqJ' : q ∈ H '' J := by
        rw [← hvJ]
        exact hqJ
      have hqBoundarySpace : q ∈ (boundaryComplex 2 M).space := by
        simpa only [M, hRQboundary] using hqJ'
      have hqBoundary : q ∈ (boundaryComplex 2 M).vertices :=
        mem_vertices_of_faces_subset_of_mem_space R (boundaryComplex 2 M)
          (fun s hs => restrict_faces_subset R (H '' Q)
            (boundaryComplex_faces_subset 2 M hs)) hqR hqBoundarySpace
      exact (hfregular hfinj q ⟨hqBoundary, hqHp⟩ hqsing).elim
    · exact (hqHp hqHp').elim
  · have hqoutside : q ∈ heightSingularPoints R.space f \ (H '' D ∪ {H p}) :=
      ⟨hqsing, fun h => h.elim hqD hqHp⟩
    have hqold : q ∈ heightSingularPoints K.space ℓ := houtside hqoutside
    obtain ⟨v, hv, hvq⟩ := hvertexImage ⟨hqsing, hqD⟩
    have hvp : v ≠ p := by
      intro hvp
      apply hqHp
      rw [mem_singleton_iff, ← hvq, hvp]
    have hvfixed : H v = v := hfixV ⟨hv, by simpa only [mem_singleton_iff] using hvp⟩
    have hvq' : v = q := hvfixed.symm.trans hvq
    have hqp : q ≠ p := fun hqp => hvp (hvq'.trans hqp)
    exact ⟨hqold, by simpa only [mem_singleton_iff] using hqp⟩

end DifferentialGeometry.Topology.PiecewiseLinear
