/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexHeightCut
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleConvexification

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLSphere_pair_of_singular_height_with_triangle_cap
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere 2 K.space)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hinj : InjOn ℓ K.vertices) {p : E} (hp : p ∈ heightSingularPoints K.space ℓ)
    {W : Set E} (hW : IsOpen W) (hWconv : Convex ℝ W) (hKW : K.space ⊆ W) :
    ∃ (A B D : Set E) (g : (Fin 3 → ℝ) → E) (H : E ≃ₜ E) (m : E →ₗ[ℝ] ℝ)
      (e : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] E)
      (T : Finset (EuclideanSpace ℝ (Fin 2))),
      A ∪ B = K.space ∧ A ∩ B = g '' stdSimplexBoundary 2 ∧
      K.space ∩ D = g '' stdSimplexBoundary 2 ∧
      IsPLBall 2 A ∧ IsPLBall 2 B ∧ IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      D ⊆ W ∩ {x | ℓ x = ℓ p} ∧ D ∉ 𝓝[{x | ℓ x = ℓ p}] p ∧
      IsPLSphere 2 (A ∪ D) ∧ IsPLSphere 2 (B ∪ D) ∧ (A ∪ D) ∩ (B ∪ D) = D ∧
      ((A ∪ D) ∪ (B ∪ D)) \ (D \ (g '' stdSimplexBoundary 2)) = K.space ∧
      (levelPolygons A ℓ (ℓ p)).encard + (levelPolygons B ℓ (ℓ p)).encard =
        (levelPolygons K.space ℓ (ℓ p)).encard + 1 ∧
      IsPLHomeomorphOn H univ univ ∧ EqOn H id Wᶜ ∧ EqOn H id (K.vertices \ {p}) ∧
      (∀ x, ℓ (H x) = ℓ x) ∧ Convex ℝ (H '' D) ∧
      T.card = 3 ∧ AffineIndependent ℝ ((↑) : T → EuclideanSpace ℝ (Fin 2)) ∧
      Function.Injective e ∧ H '' D = e '' convexHull ℝ (T : Set _) ∧
      m ≠ 0 ∧ (∀ x ∈ H '' D \ {H p}, m (H p) < m x) ∧
      (∀ S : Set E, heightIndex (H '' S) ℓ = heightIndex S ℓ) ∧
      ∀ Q ∈ ({A, B} : Set (Set E)), ∃ R : Geometry.SimplicialComplex ℝ E,
        R.faces.Finite ∧ R.space = H '' (Q ∪ D) ∧ IsPLSphere 2 R.space ∧
        ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, f ≠ 0 → InjOn f R.vertices →
          heightSingularPoints R.space f \ (H '' D ∪ {H p}) ⊆
              heightSingularPoints K.space ℓ ∧
          (∀ q ∈ K.vertices \ {p},
            (q ∈ heightSingularPoints R.space f ↔
              q ∈ heightSingularPoints K.space ℓ ∧ q ∈ Q) ∧
            (levelPolygons R.space f (f q)).encard ≤
              (levelPolygons K.space ℓ (ℓ q)).encard) ∧
          ((∀ x ∈ H '' D \ {H p}, f x ≠ f (H p)) →
            heightSingularPoints R.space f \
                (H '' (g '' stdSimplexBoundary 2) ∪ {H p}) ⊆
              heightSingularPoints K.space ℓ) := by
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) hz
  have hpv := heightSingularPoints_subset_vertices K
    hK.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
    hdimE ℓ.toLinearMap hlinear hinj hp
  obtain ⟨A, B, D, g, hunion, hinter, hA, hB, hg, hDW, hpD, hAD, hBD,
    hcap, hrecover, hcount, -, -, -, hSD⟩ :=
    exists_isPLSphere_pair_of_mem_heightSingularPoints_with_inter_eq_boundary
      K hK hdimE ℓ.toLinearMap hlinear hinj hp hW hWconv hKW
  have hD : IsPLBall 2 D := ⟨g, hg⟩
  have hAB : A ∩ B ⊆ D :=
    fun x hx => hcap.subset ⟨Or.inl hx.1, Or.inl hx.2⟩
  have hV : (K.vertices \ {p}).Finite :=
    (Set.Finite.preimage Finset.singleton_injective.injOn
      (Set.toFinite K.faces)).subset sdiff_subset
  have havoid : ℓ p ∉ ℓ '' (K.vertices \ {p}) := by
    rintro ⟨q, hq, heq⟩
    exact hq.2 (hinj hq.1 hpv heq)
  obtain ⟨U, C, hU, hUconv, hDU, hUW, hUC, hC, hsep⟩ :=
    exists_convex_open_neighborhood_disjoint_fibers hD.isPolyhedron.isCompact ℓ
      (hDW.trans inter_subset_right) hV havoid hW hWconv
      (hDW.trans inter_subset_left)
  obtain ⟨H, m, e, T, hH, hfixU, hheight, hTcard, hT, heinj, htriangle,
    hm, hmsep, hindex⟩ :=
    exists_isPLHomeomorphOn_triangle_image_strict_separation_of_subset_fiber
      hdimE ℓ.toLinearMap hlinear hD (hDW.trans inter_subset_right) rfl hpD
      hUconv hU hDU
  have hconvex : Convex ℝ (H '' D) := by
    rw [htriangle]
    exact (convex_convexHull ℝ (T : Set _)).affine_image e
  have hfixC : EqOn H id Cᶜ :=
    hfixU.mono (compl_subset_compl.mpr hUC)
  have hfixV : EqOn H id (K.vertices \ {p}) := by
    intro q hq
    exact hfixC (fun hqC => Set.disjoint_left.mp (hsep q hq) hqC rfl)
  have hpiece (Q Q' : Set E) (hQQ' : Q ∪ Q' = K.space)
      (hQ : IsClosed Q) (hQ' : IsClosed Q') (hinter' : Q ∩ Q' ⊆ D)
      (hcap' : IsPLSphere 2 (Q ∪ D)) :
      ∃ R : Geometry.SimplicialComplex ℝ E,
        R.faces.Finite ∧ R.space = H '' (Q ∪ D) ∧ IsPLSphere 2 R.space ∧
        ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, f ≠ 0 → InjOn f R.vertices →
          heightSingularPoints R.space f \ (H '' D ∪ {H p}) ⊆
              heightSingularPoints K.space ℓ ∧
          (∀ q ∈ K.vertices \ {p},
            (q ∈ heightSingularPoints R.space f ↔
              q ∈ heightSingularPoints K.space ℓ ∧ q ∈ Q) ∧
            (levelPolygons R.space f (f q)).encard ≤
              (levelPolygons K.space ℓ (ℓ q)).encard) ∧
          ((∀ x ∈ H '' D \ {H p}, f x ≠ f (H p)) →
            heightSingularPoints R.space f \
                (H '' (g '' stdSimplexBoundary 2) ∪ {H p}) ⊆
              heightSingularPoints K.space ℓ) := by
    have himage : IsPLSphere 2 (H '' (Q ∪ D)) :=
      hcap'.of_isPLHomeomorphOn
        (hH.restrict hcap'.isPolyhedron (subset_univ _))
    obtain ⟨R, hRfin, hRspace⟩ := himage.isPolyhedron.exists_simplicialComplex
    let _ : Finite R.faces := hRfin.to_subtype
    have hR : IsPLSphere 2 R.space := hRspace.symm ▸ himage
    refine ⟨R, hRfin, hRspace, hR, ?_⟩
    filter_upwards
        [eventually_heightSingularPoints_image_cap_sdiff_subset_and_encard_levelPolygons_le
      K R hK hR.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
      hdimE ℓ hℓ hinj p hQQ' hQ' hD.isPolyhedron.isClosed hinter'
      (hDU.trans hUC) hC hsep H hH hfixC hheight hRspace] with f hf hfne hfinj
    obtain ⟨houtside, hpoints⟩ := hf hfne hfinj
    refine ⟨houtside, hpoints, fun hside => ?_⟩
    have hgimage : IsPLHomeomorphOn (H ∘ g) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
        (H '' D) := hg.trans (hH.restrict hD.isPolyhedron (subset_univ D))
    have hlevel : H '' D ⊆ {x | ℓ x = ℓ p} := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hheight x).trans (hDW hx).2
    have hQD : H '' Q ∩ H '' D ⊆ (H ∘ g) '' stdSimplexBoundary 2 := by
      rintro _ ⟨⟨x, hx, rfl⟩, y, hy, heq⟩
      have hyx : y = x := H.injective heq
      have hxJ : x ∈ g '' stdSimplexBoundary 2 :=
        hSD.subset ⟨hQQ' ▸ Or.inl hx, hyx ▸ hy⟩
      rw [image_comp]
      exact mem_image_of_mem H hxJ
    have hinner := heightSingularPoints_cap_inter_subset_image_boundary
      hdimE ℓ.toLinearMap hlinear (H.isClosedMap Q hQ) hgimage hlevel hQD
      (hheight p) f.toLinearMap hside
    rw [← image_union, ← hRspace, image_comp] at hinner
    rintro q ⟨hq, hqexc⟩
    by_cases hqD : q ∈ H '' D
    · exact (hqexc (hinner ⟨hq, hqD⟩)).elim
    · exact houtside
        ⟨hq, fun h => h.elim hqD (fun heq => hqexc (Or.inr heq))⟩
  refine ⟨A, B, D, g, H, m, e, T, hunion, hinter, hSD, hA, hB, hg, hDW,
    hpD, hAD, hBD, hcap, hrecover, hcount, hH,
    hfixU.mono (compl_subset_compl.mpr hUW), hfixV, hheight, hconvex,
    hTcard, hT, heinj, htriangle, hm, hmsep, hindex, ?_⟩
  intro Q hQ
  rcases hQ with hQA | hQB
  · rw [hQA]
    exact hpiece A B hunion hA.isPolyhedron.isClosed hB.isPolyhedron.isClosed
      hAB hAD
  · change Q = B at hQB
    rw [hQB]
    exact hpiece B A ((union_comm B A).trans hunion)
      hB.isPolyhedron.isClosed hA.isPolyhedron.isClosed
      ((inter_comm B A).trans_le hAB) hBD

end DifferentialGeometry.Topology.PiecewiseLinear
