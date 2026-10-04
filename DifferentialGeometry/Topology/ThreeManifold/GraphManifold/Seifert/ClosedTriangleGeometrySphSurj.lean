import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometrySphFold
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatSurj

/-!
# The fold of a spherical closed triangle block is onto

Lane B3d3, for B3d (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`,
§2, with DB3 §4). On the spherical triangle minus the outer vertex the fold is `P ∘ liftP` and on
its mirror `P ∘ liftM` (`sphFoldMap_of_triangle`, `sphFoldMap_of_conjTriangle`): points of a
vertex disc lie in its closed sector (`SphLayout.triangle_sector_*`), inside the good window.
Every point of the block is `P (u, ζ)` with `|u| < 7/2`, `u ≠ ± 3/2`, or on a core circle: for
`Im u ≥ 0` take the preimage of `u` in the triangle and the fibre coordinate solving
`e(t/ℓ) Ψ = ζ`, for `Im u < 0` the mirror point, and a core circle is the image of the fibre over
its vertex (`surjective_sphFoldMap`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace ClosedTriangle

namespace Sph

open TwoConeFold

section Surj

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (hχ : 0 < d.orbChi)
  (D : (C.closedSphShape hc h3 hχ).FoldData) (L : SphLayout (sphDatum C hc h3 hχ D))

set_option hygiene false in
local notation "𝒦" => sphDatum C hc h3 hχ D

theorem window_of_sector {w : ℂ} {θ : ℝ} (hθ : 0 < θ) (h : 0 ≤ arg w ∧ arg w ≤ θ) :
    -(θ / 2) < arg w ∧ arg w < 3 * θ / 2 :=
  ⟨by linarith [h.1], by linarith [h.2]⟩

theorem sphFoldMap_of_triangle {x : ModelCoordinates} (hz : planeOf x ∈ (𝒦).σ.triangle)
    (hz0 : planeOf x ≠ 0) (hz1 : planeOf x ≠ (𝒦).σ.vertexOne)
    (hz2 : planeOf x ≠ (𝒦).σ.vertexTwo) :
    sphFoldMap L C hc h3 x = C.closedChart hc h3 ((𝒦).liftP x) ∧ planeOf x ∈ sphBase L := by
  have hcov := L.cover ⟨hz, hz0⟩
  simp only [mem_union] at hcov
  have hdom : ∀ _ : planeOf x ∈ L.mainSet ∨ planeOf x ∈ L.discOne ∨
      planeOf x ∈ L.discTwo ∨ planeOf x ∈ L.discThree, planeOf x ∈ sphBase L := by
    intro h
    simp only [sphBase, mem_union, mem_ofPred_eq]
    tauto
  rcases hcov with ((hm | hd) | hd) | hd
  · exact ⟨sphFoldMap_of_main C hc h3 hχ D L hm, hdom (Or.inl hm)⟩
  · refine ⟨?_, hdom (Or.inr (Or.inl hd))⟩
    rw [sphFoldMap_of_discOne L C hc h3 hd]
    exact tubeOne_eq_liftP C hc h3 hχ D L hd ⟨rotOne_ne_zero L hd hz1,
      window_of_sector (𝒦).σ.θ₁_pos (L.triangle_sector_one _ hz hd hz1)⟩
  · refine ⟨?_, hdom (Or.inr (Or.inr (Or.inl hd)))⟩
    rw [sphFoldMap_of_discTwo L C hc h3 hd]
    exact tubeTwo_eq_liftP C hc h3 hχ D L hd ⟨rotTwo_ne_zero L hd hz2,
      window_of_sector (𝒦).σ.θ₂_pos (L.triangle_sector_two _ hz hd hz2)⟩
  · refine ⟨?_, hdom (Or.inr (Or.inr (Or.inr hd)))⟩
    rw [sphFoldMap_of_discThree L C hc h3 hd]
    exact tubeThree_eq_liftP C hc h3 hχ D L hd ⟨hz0,
      window_of_sector (𝒦).σ.θ₃_pos (L.triangle_sector_three _ hz hd hz0)⟩

theorem sphFoldMap_of_conjTriangle {x : ModelCoordinates}
    (hz : conj (planeOf x) ∈ (𝒦).σ.triangle) (hz0 : conj (planeOf x) ≠ 0)
    (hz1 : conj (planeOf x) ≠ (𝒦).σ.vertexOne) (hz2 : conj (planeOf x) ≠ (𝒦).σ.vertexTwo) :
    sphFoldMap L C hc h3 x = C.closedChart hc h3 ((𝒦).liftM x) ∧ planeOf x ∈ sphBase L := by
  have hcov := L.cover ⟨hz, hz0⟩
  simp only [mem_union] at hcov
  have hdom : ∀ _ : conj (planeOf x) ∈ L.mainSet ∨ planeOf x ∈ L.discOneMirror ∨
      planeOf x ∈ L.discTwo ∨ planeOf x ∈ L.discThree, planeOf x ∈ sphBase L := by
    intro h
    simp only [sphBase, mem_union, mem_ofPred_eq]
    tauto
  rcases hcov with ((hm | hd) | hd) | hd
  · exact ⟨sphFoldMap_of_conjMain C hc h3 hχ D L hm, hdom (Or.inl hm)⟩
  · have hd' : planeOf x ∈ L.discOneMirror := hd
    refine ⟨?_, hdom (Or.inr (Or.inl hd'))⟩
    rw [sphFoldMap_of_discOneMirror L C hc h3 hd']
    exact tubeOne_eq_liftM C hc h3 hχ D L hd ⟨rotOne_ne_zero L hd hz1,
      window_of_sector (𝒦).σ.θ₁_pos (L.triangle_sector_one _ hz hd hz1)⟩
  · have hd' : planeOf x ∈ L.discTwo := by
      have := L.conj_mem_discTwo hd
      rwa [conj_conj] at this
    refine ⟨?_, hdom (Or.inr (Or.inr (Or.inl hd')))⟩
    rw [sphFoldMap_of_discTwo L C hc h3 hd']
    exact tubeTwo_eq_liftM C hc h3 hχ D L hd' ⟨rotTwo_ne_zero L hd hz2,
      window_of_sector (𝒦).σ.θ₂_pos (L.triangle_sector_two _ hz hd hz2)⟩
  · have hd' : planeOf x ∈ L.discThree := by
      have := L.conj_mem_discThree hd
      rwa [conj_conj] at this
    refine ⟨?_, hdom (Or.inr (Or.inr (Or.inr hd')))⟩
    rw [sphFoldMap_of_discThree L C hc h3 hd']
    exact tubeThree_eq_liftM C hc h3 hχ D L hd' ⟨hz0,
      window_of_sector (𝒦).σ.θ₃_pos (L.triangle_sector_three _ hz hd hz0)⟩

theorem vertexOne_mem_discOne : (𝒦).σ.vertexOne ∈ L.discOne := by
  refine ⟨?_, ?_⟩
  · rw [mul_comm, mul_conj]
    have : (0 : ℝ) < 1 + normSq (𝒦).σ.vertexOne := by
      have := normSq_nonneg (𝒦).σ.vertexOne; linarith
    exact_mod_cast this.ne'
  · rw [rotOne_eq_of_sph (𝒦).hσ]
    simp [discV, L.radOne_pos]

theorem vertexTwo_mem_discTwo : (𝒦).σ.vertexTwo ∈ L.discTwo := by
  refine ⟨?_, ?_⟩
  · rw [mul_comm, mul_conj]
    have : (0 : ℝ) < 1 + normSq (𝒦).σ.vertexTwo := by
      have := normSq_nonneg (𝒦).σ.vertexTwo; linarith
    exact_mod_cast this.ne'
  · rw [rotTwo_eq_of_sph (𝒦).hσ]
    simp [discV, L.radTwo_pos]

theorem zero_mem_discThree : (0 : ℂ) ∈ L.discThree := by
  change ‖(0 : ℂ)‖ < L.radThree
  rw [norm_zero]
  exact L.radThree_pos

theorem rotOne_vertexOne : (𝒦).σ.rotOne (𝒦).σ.vertexOne = 0 := by
  rw [rotOne_eq_of_sph (𝒦).hσ]
  simp [discV]

theorem rotTwo_vertexTwo : (𝒦).σ.rotTwo (𝒦).σ.vertexTwo = 0 := by
  rw [rotTwo_eq_of_sph (𝒦).hσ]
  simp [discV]

theorem surjective_sphFoldMap (q : W.pieceInterior ⊤) :
    ∃ x : ModelCoordinates, planeOf x ∈ sphBase L ∧ sphFoldMap L C hc h3 x = q := by
  have hℓ := (𝒦).ℓ_ne
  rcases C.exists_closedChart_eq hc h3 q with ⟨y, hy, rfl⟩ | ⟨m, w, rfl⟩
  · obtain ⟨hy7, hy1, hy2⟩ := hy
    by_cases him : 0 ≤ y.1.im
    · obtain ⟨z, ⟨hzT, hz0⟩, hfz⟩ := (𝒦).D.bijOn_f.surjOn (⟨hy7, him⟩ : y.1 ∈ basePlusSeven)
      have hz1 : z ≠ (𝒦).σ.vertexOne := by
        rintro rfl; exact hy1 (hfz.symm.trans ((𝒦).D.f_vertexOne))
      have hz2 : z ≠ (𝒦).σ.vertexTwo := by
        rintro rfl; exact hy2 (hfz.symm.trans ((𝒦).D.f_vertexTwo))
      obtain ⟨s, hs⟩ := exists_eC_eq (y.2 * ((𝒦).psiC z)⁻¹)
      set x := ofPlane z ((𝒦).ℓ * s) with hx
      have hpx : planeOf x = z := planeOf_ofPlane _ _
      obtain ⟨hF, hdom⟩ := sphFoldMap_of_triangle C hc h3 hχ D L (x := x) (hpx ▸ hzT)
        (hpx ▸ hz0) (hpx ▸ hz1) (hpx ▸ hz2)
      refine ⟨x, hdom, ?_⟩
      rw [hF]
      congr 1
      unfold SphDatum.liftP
      rw [hpx, hfz, hx, ofPlane_apply_two, mul_div_cancel_left₀ _ hℓ, hs, inv_mul_cancel_right]
    · push Not at him
      have hc7 : conj y.1 ∈ basePlusSeven := ⟨by rw [Complex.norm_conj]; exact hy7,
        by rw [conj_im]; linarith⟩
      obtain ⟨z, ⟨hzT, hz0⟩, hfz⟩ := (𝒦).D.bijOn_f.surjOn hc7
      have hz1 : z ≠ (𝒦).σ.vertexOne := by
        rintro rfl
        apply hy1
        have := congrArg conj (hfz.symm.trans ((𝒦).D.f_vertexOne))
        rwa [Complex.conj_conj, map_div₀, map_ofNat, map_ofNat] at this
      have hz2 : z ≠ (𝒦).σ.vertexTwo := by
        rintro rfl
        apply hy2
        have := congrArg conj (hfz.symm.trans ((𝒦).D.f_vertexTwo))
        rwa [Complex.conj_conj, map_neg, map_div₀, map_ofNat, map_ofNat] at this
      obtain ⟨s, hs⟩ := exists_eC_eq (y.2⁻¹ * ((𝒦).psiC z)⁻¹)
      set x := ofPlane (conj z) ((𝒦).c₀ - (𝒦).ℓ * s) with hx
      have hpx : conj (planeOf x) = z := by rw [hx, planeOf_ofPlane, Complex.conj_conj]
      obtain ⟨hF, hdom⟩ := sphFoldMap_of_conjTriangle C hc h3 hχ D L (x := x) (hpx ▸ hzT)
        (hpx ▸ hz0) (hpx ▸ hz1) (hpx ▸ hz2)
      refine ⟨x, hdom, ?_⟩
      rw [hF]
      congr 1
      unfold SphDatum.liftM SphDatum.liftP conjPair
      rw [planeOf_reflectMap, hpx, hfz, Complex.conj_conj, reflectMap_two, hx, ofPlane_apply_two,
        sub_sub_cancel, mul_div_cancel_left₀ _ hℓ, hs, inv_mul_cancel_right, inv_inv]
  · obtain ⟨j, rfl⟩ := (C.closedHoleEquiv hc h3).surjective m
    fin_cases j
    · obtain ⟨s, hs⟩ := exists_eC_eq w
      set x := ofPlane 0 ((𝒦).ℓ * (s / (𝒦).σ.p₃ - (𝒦).betaThree)) with hx
      have hpx : planeOf x = 0 := planeOf_ofPlane _ _
      have hd : planeOf x ∈ L.discThree := by rw [hpx]; exact zero_mem_discThree C hc h3 hχ D L
      refine ⟨x, ?_, ?_⟩
      · simp only [sphBase, mem_union]
        exact Or.inr hd
      · rw [sphFoldMap_of_discThree L C hc h3 hd]
        congr 1
        unfold SphDatum.tubeThree SphDatum.sThree
        rw [hpx, mul_zero, zero_mul, hx, ofPlane_apply_two, mul_div_cancel_left₀ _ hℓ,
          sub_add_cancel, mul_div_cancel₀ _ (by exact_mod_cast (𝒦).p₃_pos.ne'), hs]
    · obtain ⟨s, hs⟩ := exists_eC_eq w
      set x := ofPlane (𝒦).σ.vertexOne
        ((𝒦).ℓ * (s / (𝒦).σ.p₁ - (𝒦).betaOne (𝒦).σ.vertexOne)) with hx
      have hpx : planeOf x = (𝒦).σ.vertexOne := planeOf_ofPlane _ _
      have hd : planeOf x ∈ L.discOne := by
        rw [hpx]; exact vertexOne_mem_discOne C hc h3 hχ D L
      refine ⟨x, ?_, ?_⟩
      · simp only [sphBase, mem_union]
        exact Or.inl (Or.inl (Or.inl (Or.inr hd)))
      · rw [sphFoldMap_of_discOne L C hc h3 hd]
        congr 1
        unfold SphDatum.tubeOne SphDatum.sOne
        rw [hpx, rotOne_vertexOne C hc h3 hχ D, zero_mul, hx, ofPlane_apply_two,
          mul_div_cancel_left₀ _ hℓ, sub_add_cancel,
          mul_div_cancel₀ _ (by exact_mod_cast (𝒦).p₁_pos.ne'), hs]
    · obtain ⟨s, hs⟩ := exists_eC_eq w
      set x := ofPlane (𝒦).σ.vertexTwo
        ((𝒦).ℓ * (s / (𝒦).σ.p₂ - (𝒦).betaTwo (𝒦).σ.vertexTwo)) with hx
      have hpx : planeOf x = (𝒦).σ.vertexTwo := planeOf_ofPlane _ _
      have hd : planeOf x ∈ L.discTwo := by
        rw [hpx]; exact vertexTwo_mem_discTwo C hc h3 hχ D L
      refine ⟨x, ?_, ?_⟩
      · simp only [sphBase, mem_union]
        exact Or.inl (Or.inr hd)
      · rw [sphFoldMap_of_discTwo L C hc h3 hd]
        congr 1
        unfold SphDatum.tubeTwo SphDatum.sTwo
        rw [hpx, rotTwo_vertexTwo C hc h3 hχ D, zero_mul, hx, ofPlane_apply_two,
          mul_div_cancel_left₀ _ hℓ, sub_add_cancel,
          mul_div_cancel₀ _ (by exact_mod_cast (𝒦).p₂_pos.ne'), hs]

end Surj

end Sph

end ClosedTriangle

end GC.Seifert
