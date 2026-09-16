import DifferentialGeometry.Topology.PiecewiseLinear.FiberInterior
import DifferentialGeometry.Topology.PiecewiseLinear.HeightLocalization
import DifferentialGeometry.Topology.PiecewiseLinear.LevelConvexification
import DifferentialGeometry.Topology.PiecewiseLinear.SingularHeightCut

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLSphere_pair_of_singular_height_with_convex_cap
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLSphere 2 K.space)
    (hdimE : Module.finrank ℝ E = 3) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    {p : E} (hp : p ∈ heightSingularPoints K.space ℓ)
    {W : Set E} (hW : IsOpen W) (hWconv : Convex ℝ W) (hKW : K.space ⊆ W) :
    ∃ (A B D : Set E) (g : (Fin 3 → ℝ) → E) (H : E ≃ₜ E) (m : E →ₗ[ℝ] ℝ),
      A ∪ B = K.space ∧ A ∩ B = g '' stdSimplexBoundary 2 ∧
      K.space ∩ D = g '' stdSimplexBoundary 2 ∧
      IsPLBall 2 A ∧ IsPLBall 2 B ∧ IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3)) D ∧
      D ⊆ W ∩ {x | ℓ x = ℓ p} ∧ D ∉ 𝓝[{x | ℓ x = ℓ p}] p ∧
      IsPLSphere 2 (A ∪ D) ∧ IsPLSphere 2 (B ∪ D) ∧ (A ∪ D) ∩ (B ∪ D) = D ∧
      ((A ∪ D) ∪ (B ∪ D)) \ (D \ (g '' stdSimplexBoundary 2)) = K.space ∧
      (levelPolygons A ℓ (ℓ p)).encard + (levelPolygons B ℓ (ℓ p)).encard =
        (levelPolygons K.space ℓ (ℓ p)).encard + 1 ∧
      IsPLHomeomorphOn H univ univ ∧ EqOn H id Wᶜ ∧ EqOn H id (K.vertices \ {p}) ∧
      (∀ x, ℓ (H x) = ℓ x) ∧ Convex ℝ (H '' D) ∧ m ≠ 0 ∧
      (∀ x ∈ H '' D \ {H p}, m (H p) < m x) ∧
      (∀ S : Set E, heightIndex (H '' S) ℓ = heightIndex S ℓ) ∧
      ∀ T ∈ ({A, B} : Set (Set E)), ∃ R : Geometry.SimplicialComplex ℝ E,
        R.faces.Finite ∧ R.space = H '' (T ∪ D) ∧ IsPLSphere 2 R.space ∧
        ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, f ≠ 0 → InjOn f R.vertices →
          heightSingularPoints R.space f \ (H '' D ∪ {H p}) ⊆ heightSingularPoints K.space ℓ ∧
          (∀ q ∈ K.vertices \ {p},
            (q ∈ heightSingularPoints R.space f ↔ q ∈ heightSingularPoints K.space ℓ ∧ q ∈ T) ∧
            (levelPolygons R.space f (f q)).encard ≤ (levelPolygons K.space ℓ (ℓ q)).encard) ∧
          ((∀ x ∈ H '' D \ {H p}, f x ≠ f (H p)) →
            heightSingularPoints R.space f \ (H '' (g '' stdSimplexBoundary 2) ∪ {H p}) ⊆
              heightSingularPoints K.space ℓ) := by
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) hz
  have hpv := heightSingularPoints_subset_vertices K hK.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
    hdimE ℓ.toLinearMap hlinear hinj hp
  obtain ⟨A, B, D, g, hunion, hinter, hA, hB, hg, hDW, hpD, hAD, hBD, hcap, hrecover, hcount, -, -, -, hSD⟩ :=
    exists_isPLSphere_pair_of_mem_heightSingularPoints_with_inter_eq_boundary K hK hdimE ℓ.toLinearMap hlinear hinj hp hW hWconv hKW
  have hD : IsPLBall 2 D := ⟨g, hg⟩
  have hAB : A ∩ B ⊆ D := fun x hx => hcap.subset ⟨Or.inl hx.1, Or.inl hx.2⟩
  have hV : (K.vertices \ {p}).Finite :=
    (Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)).subset sdiff_subset
  have havoid : ℓ p ∉ ℓ '' (K.vertices \ {p}) := by
    rintro ⟨q, hq, heq⟩
    exact hq.2 (hinj hq.1 hpv heq)
  obtain ⟨U, C, hU, hUconv, hDU, hUW, hUC, hC, hsep⟩ :=
    exists_convex_open_neighborhood_disjoint_fibers hD.isPolyhedron.isCompact ℓ
      (hDW.trans inter_subset_right) hV havoid hW hWconv (hDW.trans inter_subset_left)
  obtain ⟨H, m, hH, hfixU, hheight, hconvex, hm, hmsep, hindex⟩ :=
    exists_isPLHomeomorphOn_convex_image_strict_separation_of_subset_fiber hdimE ℓ.toLinearMap hlinear hD
      (hDW.trans inter_subset_right) rfl hpD hUconv hU hDU
  have hfixC : EqOn H id Cᶜ := hfixU.mono (compl_subset_compl.mpr hUC)
  have hfixV : EqOn H id (K.vertices \ {p}) := by
    intro q hq
    exact hfixC (fun hqC => Set.disjoint_left.mp (hsep q hq) hqC rfl)
  have hpiece (T T' : Set E) (hTT' : T ∪ T' = K.space) (hT : IsClosed T) (hT' : IsClosed T')
      (hinter' : T ∩ T' ⊆ D) (hcap' : IsPLSphere 2 (T ∪ D)) :
      ∃ R : Geometry.SimplicialComplex ℝ E,
        R.faces.Finite ∧ R.space = H '' (T ∪ D) ∧ IsPLSphere 2 R.space ∧
        ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, f ≠ 0 → InjOn f R.vertices →
          heightSingularPoints R.space f \ (H '' D ∪ {H p}) ⊆ heightSingularPoints K.space ℓ ∧
          (∀ q ∈ K.vertices \ {p},
            (q ∈ heightSingularPoints R.space f ↔ q ∈ heightSingularPoints K.space ℓ ∧ q ∈ T) ∧
            (levelPolygons R.space f (f q)).encard ≤ (levelPolygons K.space ℓ (ℓ q)).encard) ∧
          ((∀ x ∈ H '' D \ {H p}, f x ≠ f (H p)) →
            heightSingularPoints R.space f \ (H '' (g '' stdSimplexBoundary 2) ∪ {H p}) ⊆
              heightSingularPoints K.space ℓ) := by
    have himage : IsPLSphere 2 (H '' (T ∪ D)) :=
      hcap'.of_isPLHomeomorphOn (hH.restrict hcap'.isPolyhedron (subset_univ _))
    obtain ⟨R, hRfin, hRspace⟩ := himage.isPolyhedron.exists_simplicialComplex
    let _ : Finite R.faces := hRfin.to_subtype
    have hR : IsPLSphere 2 R.space := hRspace.symm ▸ himage
    refine ⟨R, hRfin, hRspace, hR, ?_⟩
    filter_upwards [eventually_heightSingularPoints_image_cap_sdiff_subset_and_encard_levelPolygons_le K R hK
      hR.isCombinatorialManifold.isCombinatorialManifoldWithBoundary hdimE ℓ hℓ hinj p hTT' hT'
      hD.isPolyhedron.isClosed hinter' (hDU.trans hUC) hC hsep H hH hfixC hheight hRspace]
      with f hf hfne hfinj
    obtain ⟨houtside, hpoints⟩ := hf hfne hfinj
    refine ⟨houtside, hpoints, fun hside => ?_⟩
    have hgimage : IsPLHomeomorphOn (H ∘ g) (stdSimplex ℝ (Fin 3)) (H '' D) :=
      hg.trans (hH.restrict hD.isPolyhedron (subset_univ D))
    have hlevel : H '' D ⊆ {x | ℓ x = ℓ p} := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hheight x).trans (hDW hx).2
    have hTD : H '' T ∩ H '' D ⊆ (H ∘ g) '' stdSimplexBoundary 2 := by
      rintro _ ⟨⟨x, hx, rfl⟩, y, hy, heq⟩
      have hyx : y = x := H.injective heq
      have hxJ : x ∈ g '' stdSimplexBoundary 2 := hSD.subset ⟨hTT' ▸ Or.inl hx, hyx ▸ hy⟩
      rw [image_comp]
      exact mem_image_of_mem H hxJ
    have hinner := heightSingularPoints_cap_inter_subset_image_boundary hdimE ℓ.toLinearMap hlinear
      (H.isClosedMap T hT) hgimage hlevel hTD (hheight p) f.toLinearMap hside
    rw [← image_union, ← hRspace, image_comp] at hinner
    rintro q ⟨hq, hqexc⟩
    by_cases hqD : q ∈ H '' D
    · exact (hqexc (hinner ⟨hq, hqD⟩)).elim
    · exact houtside ⟨hq, fun h => h.elim hqD (fun heq => hqexc (Or.inr heq))⟩
  refine ⟨A, B, D, g, H, m, hunion, hinter, hSD, hA, hB, hg, hDW, hpD, hAD, hBD, hcap, hrecover, hcount,
    hH, hfixU.mono (compl_subset_compl.mpr hUW), hfixV, hheight, hconvex, hm, hmsep, hindex, ?_⟩
  intro T hT
  rcases hT with hTA | hTB
  · rw [hTA]
    exact hpiece A B hunion hA.isPolyhedron.isClosed hB.isPolyhedron.isClosed hAB hAD
  · change T = B at hTB
    rw [hTB]
    exact hpiece B A ((union_comm B A).trans hunion) hB.isPolyhedron.isClosed hA.isPolyhedron.isClosed
      ((inter_comm B A).trans_le hAB) hBD

end DifferentialGeometry.Topology.PiecewiseLinear
