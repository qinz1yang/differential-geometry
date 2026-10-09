import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypFold
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatSurj

/-!
# The fold of a hyperbolic closed triangle block is onto

Lane B3c (design `docs/geometrization/handoffs/20261004-design-b3c-hyperbolic-rows.md`, §3; the
hyperbolic analogue of B3's `ClosedTriangleGeometryFlatSurj`). In the closed hyperbolic triangle
every point other than a vertex lies in the good sector of the vertex discs (`triangle_sector_one`,
`triangle_sector_two`, `triangle_sector_three`, from CF-H2's `HypFold.sector_one/two/three`), so on
the triangle minus the outer vertex the fold is `P ∘ liftP` and on its mirror `P ∘ liftM`
(`hypMap_of_triangle`, `hypMap_of_conjTriangle`). Every point of the block is `P (u, ζ)` with
`|u| < 7/2` or on a core circle: for `Im u ≥ 0` take the preimage of `u` in the triangle, the
model point over it (`hypVertex`-type point `ofPlane (hypDiscInv z) t`, `hb = z`) and the fibre
coordinate solving `e(t/ℓ) Ψ = ζ`; for `Im u < 0` the mirror point; a core circle is the image of
the fibre over its vertex (`surjective_hypMap`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace ClosedTriangle

namespace Hyp

open TwoConeFold

section Sectors

variable {σ : CompactShape} (hσ : σ.curv = .hyperbolic)
include hσ

theorem rotOne_ne_zero {z : ℂ} (hz : ‖z‖ < 1) (h1 : z ≠ σ.vertexOne) : σ.rotOne z ≠ 0 := by
  intro h
  apply h1
  rw [HypFold.rotOne_eq_mul_mob hσ, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd h (neg_ne_zero.2 (Complex.exp_ne_zero _))
  · exact eq_of_mob_eq_zero (HypFold.one_sub_conj_vertexOne_mul_ne_zero hσ hz) h

theorem rotTwo_ne_zero {z : ℂ} (hz : ‖z‖ < 1) (h2 : z ≠ σ.vertexTwo) : σ.rotTwo z ≠ 0 := by
  intro h
  apply h2
  rw [HypFold.rotTwo_eq_mul_mob hσ, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd h (neg_ne_zero.2 (Complex.exp_ne_zero _))
  · refine eq_of_mob_eq_zero ?_ h
    rw [HypFold.conj_vertexTwo (σ := σ)]
    exact HypFold.one_sub_vertexTwo_mul_ne_zero hσ hz

theorem rotOne_vertexOne : σ.rotOne σ.vertexOne = 0 := by
  rw [HypFold.rotOne_eq_mul_mob hσ, HypFold.mob_self, mul_zero]

theorem rotTwo_vertexTwo : σ.rotTwo σ.vertexTwo = 0 := by
  rw [HypFold.rotTwo_eq_mul_mob hσ, HypFold.mob_self, mul_zero]

theorem triangle_sector_one {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne) :
    σ.rotOne z ≠ 0 ∧ -(σ.θ₁ / 2) < arg (σ.rotOne z) ∧ arg (σ.rotOne z) < 3 * σ.θ₁ / 2 := by
  have hne := rotOne_ne_zero hσ (HypFold.norm_lt_one_of_mem hσ hz) h1
  obtain ⟨a, b⟩ := HypFold.sector_one hσ hz
  obtain ⟨c1, c2⟩ := arg_mem_Icc_of_sides σ.θ₁_pos σ.θ₁_le hne a b
  have := σ.θ₁_pos
  exact ⟨hne, by linarith, by linarith⟩

theorem triangle_sector_two {z : ℂ} (hz : z ∈ σ.triangle) (h2 : z ≠ σ.vertexTwo) :
    σ.rotTwo z ≠ 0 ∧ -(σ.θ₂ / 2) < arg (σ.rotTwo z) ∧ arg (σ.rotTwo z) < 3 * σ.θ₂ / 2 := by
  have hne := rotTwo_ne_zero hσ (HypFold.norm_lt_one_of_mem hσ hz) h2
  obtain ⟨a, b⟩ := HypFold.sector_two hσ hz
  obtain ⟨c1, c2⟩ := arg_mem_Icc_of_sides σ.θ₂_pos σ.θ₂_le hne a b
  have := σ.θ₂_pos
  exact ⟨hne, by linarith, by linarith⟩

omit hσ in
theorem triangle_sector_three {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) :
    z ≠ 0 ∧ -(σ.θ₃ / 2) < arg z ∧ arg z < 3 * σ.θ₃ / 2 := by
  have a : 0 ≤ z.im := hz.2 0
  have b := hz.2 1
  have hb : (exp (-((σ.θ₃ : ℂ) * I)) * z).im ≤ 0 := by
    have := HypFold.wallSide_one_eq_neg_im (σ := σ) z
    linarith
  obtain ⟨c1, c2⟩ := arg_mem_Icc_of_sides σ.θ₃_pos σ.θ₃_le h0 a hb
  have := σ.θ₃_pos
  exact ⟨h0, by linarith, by linarith⟩

end Sectors

theorem hb_ofPlane_hypDiscInv {z : ℂ} (hz : ‖z‖ < 1) (t : ℝ) :
    hb (ofPlane (hypDiscInv z) t) = z := by
  rw [hb, planeOf_ofPlane, hypDisc_hypDiscInv hz]

section Surj

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (hχ : d.orbChi < 0)
  (D : (C.closedHypShape hc h3 hχ).FoldData)

set_option hygiene false in
local notation "𝒦" => hypDatum C hc h3 hχ D

theorem hypMap_of_triangle {x : ModelCoordinates} (hz : hb x ∈ (𝒦).σ.triangle)
    (hz0 : hb x ≠ 0) (hz1 : hb x ≠ (𝒦).σ.vertexOne) (hz2 : hb x ≠ (𝒦).σ.vertexTwo) :
    hypMap C hc h3 (𝒦) x = C.closedChart hc h3 ((𝒦).liftP x) ∧ x ∈ hypDomain (𝒦) := by
  have hcov := triangle_diff_subset_cover (𝒦).hσ (D := (𝒦).D) ⟨hz, hz0⟩
  simp only [mem_union] at hcov
  have hdom : ∀ h : hb x ∈ mainSet (𝒦).D ∨ hb x ∈ discOne (𝒦).D ∨
      hb x ∈ discTwo (𝒦).D ∨ hb x ∈ discThree (𝒦).D, x ∈ hypDomain (𝒦) := by
    intro h
    change hb x ∈ hypBase (𝒦)
    simp only [hypBase, mem_union, mem_ofPred_eq]
    tauto
  rcases hcov with ((hm | hd) | hd) | hd
  · exact ⟨hypMap_of_main C hc h3 hχ D hm, hdom (Or.inl hm)⟩
  · refine ⟨?_, hdom (Or.inr (Or.inl hd))⟩
    rw [hypMap_of_discOne C hc h3 _ hd]
    exact tubeOne_eq_liftP C hc h3 hχ D hd (triangle_sector_one (𝒦).hσ hz hz1)
  · refine ⟨?_, hdom (Or.inr (Or.inr (Or.inl hd)))⟩
    rw [hypMap_of_discTwo C hc h3 _ hd]
    exact tubeTwo_eq_liftP C hc h3 hχ D hd (triangle_sector_two (𝒦).hσ hz hz2)
  · refine ⟨?_, hdom (Or.inr (Or.inr (Or.inr hd)))⟩
    rw [hypMap_of_discThree C hc h3 _ hd]
    exact tubeThree_eq_liftP C hc h3 hχ D hd (triangle_sector_three hz hz0)

theorem hypMap_of_conjTriangle {x : ModelCoordinates}
    (hz : conj (hb x) ∈ (𝒦).σ.triangle) (hz0 : conj (hb x) ≠ 0)
    (hz1 : conj (hb x) ≠ (𝒦).σ.vertexOne) (hz2 : conj (hb x) ≠ (𝒦).σ.vertexTwo) :
    hypMap C hc h3 (𝒦) x = C.closedChart hc h3 ((𝒦).liftM x) ∧ x ∈ hypDomain (𝒦) := by
  have hcov := triangle_diff_subset_cover (𝒦).hσ (D := (𝒦).D) ⟨hz, hz0⟩
  simp only [mem_union] at hcov
  have hdom : ∀ h : conj (hb x) ∈ mainSet (𝒦).D ∨ hb x ∈ discOneMirror (𝒦).D ∨
      hb x ∈ discTwo (𝒦).D ∨ hb x ∈ discThree (𝒦).D, x ∈ hypDomain (𝒦) := by
    intro h
    change hb x ∈ hypBase (𝒦)
    simp only [hypBase, mem_union, mem_ofPred_eq]
    tauto
  have hconj : ∀ {S : Set ℂ}, (∀ w ∈ S, conj w ∈ S) → conj (hb x) ∈ S → hb x ∈ S :=
    fun hS h => by simpa using hS _ h
  rcases hcov with ((hm | hd) | hd) | hd
  · exact ⟨hypMap_of_conjMain C hc h3 hχ D hm, hdom (Or.inl hm)⟩
  · have hd' : hb x ∈ discOneMirror (𝒦).D := (mem_discOneMirror_iff _).2 hd
    refine ⟨?_, hdom (Or.inr (Or.inl hd'))⟩
    rw [hypMap_of_discOneMirror C hc h3 _ hd']
    exact tubeOne_eq_liftM C hc h3 hχ D hd (triangle_sector_one (𝒦).hσ hz hz1)
  · have hd' : hb x ∈ discTwo (𝒦).D := hconj (fun w hw => conj_mem_discTwo (𝒦).hσ hw) hd
    refine ⟨?_, hdom (Or.inr (Or.inr (Or.inl hd')))⟩
    rw [hypMap_of_discTwo C hc h3 _ hd']
    exact tubeTwo_eq_liftM C hc h3 hχ D hd' (triangle_sector_two (𝒦).hσ hz hz2)
  · have hd' : hb x ∈ discThree (𝒦).D := hconj (fun w hw => conj_mem_discThree hw) hd
    refine ⟨?_, hdom (Or.inr (Or.inr (Or.inr hd')))⟩
    rw [hypMap_of_discThree C hc h3 _ hd']
    exact tubeThree_eq_liftM C hc h3 hχ D hd' (triangle_sector_three hz hz0)

theorem surjective_hypMap (q : W.pieceInterior ⊤) :
    ∃ x ∈ hypDomain (𝒦), hypMap C hc h3 (𝒦) x = q := by
  have hℓ := (𝒦).ℓ_ne
  have hσ := (𝒦).hσ
  rcases C.exists_closedChart_eq hc h3 q with ⟨y, hy, rfl⟩ | ⟨m, w, rfl⟩
  · obtain ⟨hy7, hy1, hy2⟩ := hy
    by_cases him : 0 ≤ y.1.im
    · obtain ⟨z, ⟨hzT, hz0⟩, hfz⟩ := (𝒦).D.bijOn_f.surjOn (⟨hy7, him⟩ : y.1 ∈ basePlusSeven)
      have hz1 : z ≠ (𝒦).σ.vertexOne := by
        rintro rfl; exact hy1 (hfz.symm.trans (𝒦).D.f_vertexOne)
      have hz2 : z ≠ (𝒦).σ.vertexTwo := by
        rintro rfl; exact hy2 (hfz.symm.trans (𝒦).D.f_vertexTwo)
      have hzn : ‖z‖ < 1 := HypFold.norm_lt_one_of_mem hσ hzT
      obtain ⟨s, hs⟩ := exists_eC_eq (y.2 * ((𝒦).psiC z)⁻¹)
      set x := ofPlane (hypDiscInv z) ((𝒦).ℓ * s) with hx
      have hpx : hb x = z := hb_ofPlane_hypDiscInv hzn _
      obtain ⟨hF, hdom⟩ := hypMap_of_triangle C hc h3 hχ D (x := x) (hpx ▸ hzT) (hpx ▸ hz0)
        (hpx ▸ hz1) (hpx ▸ hz2)
      refine ⟨x, hdom, ?_⟩
      rw [hF]
      congr 1
      unfold HypDatum.liftP
      rw [hpx, hfz, hx, ofPlane_apply_two, mul_div_cancel_left₀ _ hℓ, hs, inv_mul_cancel_right]
    · push Not at him
      have hc7 : conj y.1 ∈ basePlusSeven := ⟨by rw [Complex.norm_conj]; exact hy7,
        by rw [conj_im]; linarith⟩
      obtain ⟨z, ⟨hzT, hz0⟩, hfz⟩ := (𝒦).D.bijOn_f.surjOn hc7
      have hz1 : z ≠ (𝒦).σ.vertexOne := by
        rintro rfl
        apply hy1
        have := congrArg conj (hfz.symm.trans (𝒦).D.f_vertexOne)
        rwa [Complex.conj_conj, map_div₀, map_ofNat, map_ofNat] at this
      have hz2 : z ≠ (𝒦).σ.vertexTwo := by
        rintro rfl
        apply hy2
        have := congrArg conj (hfz.symm.trans (𝒦).D.f_vertexTwo)
        rwa [Complex.conj_conj, map_neg, map_div₀, map_ofNat, map_ofNat] at this
      have hzn : ‖conj z‖ < 1 := by rw [Complex.norm_conj]; exact HypFold.norm_lt_one_of_mem hσ hzT
      obtain ⟨s, hs⟩ := exists_eC_eq (y.2⁻¹ * ((𝒦).psiC z)⁻¹)
      set x := ofPlane (hypDiscInv (conj z)) ((𝒦).c₀ - (𝒦).ℓ * s) with hx
      have hpx : conj (hb x) = z := by rw [hx, hb_ofPlane_hypDiscInv hzn, Complex.conj_conj]
      obtain ⟨hF, hdom⟩ := hypMap_of_conjTriangle C hc h3 hχ D (x := x) (hpx ▸ hzT)
        (hpx ▸ hz0) (hpx ▸ hz1) (hpx ▸ hz2)
      refine ⟨x, hdom, ?_⟩
      rw [hF]
      congr 1
      unfold HypDatum.liftM HypDatum.liftP conjPair
      rw [HypDatum.hb_reflectMap, hpx, hfz, Complex.conj_conj, reflectMap_two, hx,
        ofPlane_apply_two, sub_sub_cancel, mul_div_cancel_left₀ _ hℓ, hs, inv_mul_cancel_right,
        inv_inv]
  · obtain ⟨j, rfl⟩ := (C.closedHoleEquiv hc h3).surjective m
    fin_cases j
    · obtain ⟨s, hs⟩ := exists_eC_eq w
      set x := ofPlane (hypDiscInv 0) ((𝒦).ℓ * (s / (𝒦).σ.p₃ - (𝒦).betaThree)) with hx
      have hpx : hb x = 0 := hb_ofPlane_hypDiscInv (by simp) _
      have hd : hb x ∈ discThree (𝒦).D := by
        change ‖hb x‖ < _; rw [hpx, norm_zero]; exact radThree_pos _
      refine ⟨x, ?_, ?_⟩
      · change hb x ∈ hypBase (𝒦)
        simp only [hypBase, mem_union]
        exact Or.inr hd
      · rw [hypMap_of_discThree C hc h3 _ hd]
        congr 1
        unfold HypDatum.tubeThree HypDatum.sThree
        rw [hpx, mul_zero, zero_mul, hx, ofPlane_apply_two, mul_div_cancel_left₀ _ hℓ,
          sub_add_cancel, mul_div_cancel₀ _ (by exact_mod_cast (𝒦).p₃_pos.ne'), hs]
    · obtain ⟨s, hs⟩ := exists_eC_eq w
      set x := ofPlane (hypDiscInv (𝒦).σ.vertexOne)
        ((𝒦).ℓ * (s / (𝒦).σ.p₁ - (𝒦).betaOne (𝒦).σ.vertexOne)) with hx
      have hpx : hb x = (𝒦).σ.vertexOne :=
        hb_ofPlane_hypDiscInv (HypFold.norm_vertexOne_lt_one hσ) _
      have hd : hb x ∈ discOne (𝒦).D := by rw [hpx]; exact mem_discOne_vertexOne hσ
      refine ⟨x, ?_, ?_⟩
      · change hb x ∈ hypBase (𝒦)
        simp only [hypBase, mem_union]
        exact Or.inl (Or.inl (Or.inl (Or.inr hd)))
      · rw [hypMap_of_discOne C hc h3 _ hd]
        congr 1
        unfold HypDatum.tubeOne HypDatum.sOne
        rw [hpx, rotOne_vertexOne hσ, zero_mul, hx, ofPlane_apply_two,
          mul_div_cancel_left₀ _ hℓ, sub_add_cancel,
          mul_div_cancel₀ _ (by exact_mod_cast (𝒦).p₁_pos.ne'), hs]
    · obtain ⟨s, hs⟩ := exists_eC_eq w
      set x := ofPlane (hypDiscInv (𝒦).σ.vertexTwo)
        ((𝒦).ℓ * (s / (𝒦).σ.p₂ - (𝒦).betaTwo (𝒦).σ.vertexTwo)) with hx
      have hpx : hb x = (𝒦).σ.vertexTwo :=
        hb_ofPlane_hypDiscInv (HypFold.norm_vertexTwo_lt_one hσ) _
      have hd : hb x ∈ discTwo (𝒦).D := by rw [hpx]; exact mem_discTwo_vertexTwo hσ
      refine ⟨x, ?_, ?_⟩
      · change hb x ∈ hypBase (𝒦)
        simp only [hypBase, mem_union]
        exact Or.inl (Or.inr hd)
      · rw [hypMap_of_discTwo C hc h3 _ hd]
        congr 1
        unfold HypDatum.tubeTwo HypDatum.sTwo
        rw [hpx, rotTwo_vertexTwo hσ, zero_mul, hx, ofPlane_apply_two,
          mul_div_cancel_left₀ _ hℓ, sub_add_cancel,
          mul_div_cancel₀ _ (by exact_mod_cast (𝒦).p₂_pos.ne'), hs]

end Surj

end Hyp

end ClosedTriangle

end GC.Seifert
