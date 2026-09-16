import DifferentialGeometry.Topology.PiecewiseLinear.HeightTriangleStability
import DifferentialGeometry.Topology.PiecewiseLinear.TriangleCoordinates
import Mathlib.Data.Finset.Sort

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem exists_height_ordered_triangle_vertices {s : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) (hcard : s.card = 3)
    (ℓ : E →L[ℝ] ℝ) (hinj : InjOn ℓ (s : Set E)) :
    ∃ v : Fin 3 → E, range v = (s : Set E) ∧ AffineIndependent ℝ v ∧
      StrictMono (ℓ ∘ v) := by
  classical
  let : LinearOrder s := LinearOrder.lift' (fun x : s => ℓ x)
    (fun x y h => Subtype.ext (hinj x.property y.property h))
  let e : Fin 3 ≃o s := Fintype.orderIsoFinOfCardEq s (by simpa using hcard)
  refine ⟨fun i => e i, ?_, hs.comp_embedding e.toEquiv.toEmbedding, ?_⟩
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩
  · exact e.strictMono

theorem eventually_exists_isPLHomeomorphOn_face_fiber_preserving_subfaces
    {s : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E)) (hcard : s.card = 3)
    (H : E ≃ₜ E) (hH : IsPLHomeomorphOn H univ univ) (ℓ : E →L[ℝ] ℝ)
    (hheight : ∀ x, ℓ (H x) = ℓ x) (hinj : InjOn ℓ (s : Set E)) {p : E}
    (hunique : ∀ v ∈ s, ℓ v = ℓ p → v = p) :
    ∀ᶠ f : E →L[ℝ] ℝ in 𝓝 ℓ, ∃ g : E → E,
      IsPLHomeomorphOn g (convexHull ℝ (s : Set E) ∩ {x | f (H x) = f (H p)})
        (convexHull ℝ (s : Set E) ∩ {x | ℓ x = ℓ p}) ∧
      ∀ t ⊆ s, ∀ x ∈ convexHull ℝ (s : Set E) ∩ {x | f (H x) = f (H p)},
        g x ∈ convexHull ℝ (t : Set E) ↔ x ∈ convexHull ℝ (t : Set E) := by
  classical
  obtain ⟨v, hv, hvind, hvmono⟩ := exists_height_ordered_triangle_vertices hs hcard ℓ hinj
  let T : Set (ℝ × ℝ) := {z | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 + z.2 ≤ 1}
  let A := triangleAffineMap v
  have hT : IsHPolytope T := isHPolytope_coordinate_triangle
  have hAimage : A '' T = convexHull ℝ (s : Set E) := by
    rw [← hv]
    exact triangleAffineMap_image v
  have hApl := isPiecewiseAffineOn_of_affine_of_isHPolytope A hT
  have hA : IsPLHomeomorphOn A T (convexHull ℝ (s : Set E)) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hT.isPolyhedron hApl
      ⟨fun _ hz => hAimage.subset ⟨_, hz, rfl⟩,
        (triangleAffineMap_injective hvind).injOn, fun _ hx => hAimage.symm.subset hx⟩
  have hG : IsPiecewiseAffineOn (H ∘ A) T := by
    simpa only [preimage_univ, inter_univ] using hH.isPiecewiseAffineOn.comp hApl
  have hlin : ∀ z : ℝ × ℝ, ℓ (H (A z)) =
      (ℓ (v 2) - ℓ (v 0)) * z.1 + (ℓ (v 1) - ℓ (v 0)) * z.2 + ℓ (v 0) := by
    intro z
    rw [hheight]
    dsimp only [A]
    rw [triangleAffineMap_apply, map_add, map_add, map_smul, map_smul, map_sub, map_sub]
    simp only [smul_eq_mul]
    ring
  have hv0 : ℓ (v 0) < ℓ (v 1) := hvmono (by decide : (0 : Fin 3) < 1)
  have hv1 : ℓ (v 1) < ℓ (v 2) := hvmono (by decide : (1 : Fin 3) < 2)
  have hverts : ∀ z ∈ ({(0, 0), (0, 1), (1, 0)} : Set (ℝ × ℝ)), A z ∈ s := by
    intro z hz
    rcases hz with rfl | rfl | rfl
    · simpa [A, triangleAffineMap_apply] using hv.subset (mem_range_self (0 : Fin 3))
    · simpa [A, triangleAffineMap_apply] using hv.subset (mem_range_self (1 : Fin 3))
    · simpa [A, triangleAffineMap_apply] using hv.subset (mem_range_self (2 : Fin 3))
  have hlocal := eventually_exists_isPLHomeomorphOn_triangle_fiber_preserving_edges hG ℓ
    (by linarith : 0 < ℓ (v 1) - ℓ (v 0))
    (by linarith : ℓ (v 1) - ℓ (v 0) < ℓ (v 2) - ℓ (v 0))
    (fun z _ _ _ => hlin z) (p := H p) (by
      intro z hz heq
      apply congrArg H
      apply hunique _ (hverts z hz)
      simpa only [Function.comp_apply, hheight] using heq)
  filter_upwards [hlocal] with f hf
  obtain ⟨g, hg, hedges⟩ := hf
  let P : (E →L[ℝ] ℝ) → Set (ℝ × ℝ) := fun k =>
    {z | z ∈ T ∧ k (H (A z)) = k (H p)}
  let Q : (E →L[ℝ] ℝ) → Set E := fun k =>
    convexHull ℝ (s : Set E) ∩ {x | k (H x) = k (H p)}
  have hg' : IsPLHomeomorphOn g (P f) (P ℓ) := hg
  have hPold : IsPolyhedron (P ℓ) := by
    have hpoly := hT.inter_preimage (isHPolytope_singleton (ℓ p))
      (ℓ.toLinearMap.toAffineMap.comp A)
    convert hpoly.isPolyhedron using 1
    ext z
    simp [P, hheight]
  have hPnew : IsPolyhedron (P f) := by
    have hpoly := hg'.isPolyhedron_preimage hPold (Subset.refl _)
    have heq : P f ∩ g ⁻¹' P ℓ = P f := inter_eq_left.mpr hg'.bijOn.mapsTo
    rwa [heq] at hpoly
  have hPQ : ∀ k, A '' P k = Q k := by
    intro k
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hA.bijOn.mapsTo hz.1, hz.2⟩
    · rintro ⟨hx, hlevel⟩
      obtain ⟨z, hz, rfl⟩ := hA.bijOn.surjOn hx
      exact ⟨z, ⟨hz, hlevel⟩, rfl⟩
  have hAnew : IsPLHomeomorphOn A (P f) (Q f) := by
    simpa only [hPQ] using hA.restrict hPnew (fun _ hx => hx.1)
  have hAold : IsPLHomeomorphOn A (P ℓ) (Q ℓ) := by
    simpa only [hPQ] using hA.restrict hPold (fun _ hx => hx.1)
  let g' : E → E := A ∘ g ∘ Function.invFunOn A (P f)
  refine ⟨g', ?_, ?_⟩
  · have h := (hAnew.symm.trans hg').trans hAold
    simpa only [g', Q, hheight, Function.comp_assoc] using h
  · intro t ht x hx
    let z := Function.invFunOn A (P f) x
    have hz : z ∈ P f := hAnew.symm.bijOn.mapsTo hx
    have hAz : A z = x := hAnew.bijOn.invOn_invFunOn.2 hx
    have hgz := hg'.bijOn.mapsTo hz
    obtain ⟨hl, hb, hr⟩ := hedges z hz.1 hz.2
    have himage : v '' {i | v i ∈ t} = (t : Set E) := by
      apply Subset.antisymm
      · rintro _ ⟨i, hi, rfl⟩
        exact hi
      · intro y hy
        obtain ⟨i, rfl⟩ := hv.symm.subset (ht hy)
        exact ⟨i, hy, rfl⟩
    have hsub := triangleAffineMap_mem_convexHull_image_iff_of_preserving_edges hvind
      {i | v i ∈ t} hgz.1 hz.1 hl hb hr
    rw [himage] at hsub
    change A (g z) ∈ convexHull ℝ (t : Set E) ↔ x ∈ convexHull ℝ (t : Set E)
    rwa [← hAz]

end DifferentialGeometry.Topology.PiecewiseLinear
