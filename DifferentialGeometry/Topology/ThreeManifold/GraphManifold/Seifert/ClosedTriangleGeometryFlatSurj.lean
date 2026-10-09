import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatFold

/-!
# The fold of a flat closed triangle block is onto

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§4). In the closed triangle every point other than a vertex lies in the good sector of the vertex
discs (`triangle_sector_one`, `triangle_sector_two`, `triangle_sector_three`), so on the triangle
minus the outer vertex the fold is `P ∘ liftP` and on its mirror `P ∘ liftM`
(`flatMap_of_triangle`, `flatMap_of_conjTriangle`). Every point of the block is `P (u, ζ)` with
`|u| < 7/2` or on a core circle: for `Im u ≥ 0` take the preimage of `u` in the triangle and the
fibre coordinate solving `e(t/ℓ) Ψ = ζ`, for `Im u < 0` the mirror point, and a core circle is the
image of the fibre over its vertex (`surjective_flatMap`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace ClosedTriangle

open TwoConeFold

section Sectors

theorem arg_mem_Icc_of_sides {w : ℂ} {θ : ℝ} (hθ0 : 0 < θ) (hθ : θ ≤ Real.pi / 2) (hw : w ≠ 0)
    (h1 : 0 ≤ w.im) (h2 : (exp (-((θ : ℂ) * I)) * w).im ≤ 0) : 0 ≤ arg w ∧ arg w ≤ θ := by
  refine ⟨arg_nonneg_iff.mpr h1, ?_⟩
  by_contra hlt
  push Not at hlt
  have hπ := arg_le_pi w
  have heq : arg (exp ((-θ : ℝ) * I) * w) = -θ + arg w :=
    arg_exp_mul_of_mem hw (by linarith [Real.pi_pos]) (by linarith)
  have hexp : exp (((-θ : ℝ) : ℂ) * I) = exp (-((θ : ℂ) * I)) := by
    congr 1; push_cast; ring
  rw [hexp] at heq
  have hne : exp (-((θ : ℂ) * I)) * w ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hw
  have hsin := Complex.sin_arg (exp (-((θ : ℂ) * I)) * w)
  rw [heq] at hsin
  have hpos : 0 < Real.sin (-θ + arg w) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [hsin] at hpos
  have hn : 0 < ‖exp (-((θ : ℂ) * I)) * w‖ := norm_pos_iff.mpr hne
  have := (div_pos_iff_of_pos_right hn).mp hpos
  linarith

variable {σ : EuclidShape}

theorem triangle_sector_one {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne) :
    σ.rotOne z ≠ 0 ∧ -(σ.θ₁ / 2) < arg (σ.rotOne z) ∧ arg (σ.rotOne z) < 3 * σ.θ₁ / 2 := by
  have hne : σ.rotOne z ≠ 0 := by
    intro h
    apply h1
    rw [EuclidShape.rotOne, neg_eq_zero, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd h (Complex.exp_ne_zero _)
    · exact sub_eq_zero.mp h
  have a := hz 1
  have b := hz 2
  rw [σ.wallSide_one_eq_im_rotOne] at a
  rw [σ.wallSide_two_eq_rotOne] at b
  obtain ⟨c1, c2⟩ := arg_mem_Icc_of_sides σ.θ₁_pos σ.θ₁_le hne a (by linarith)
  have := σ.θ₁_pos
  exact ⟨hne, by linarith, by linarith⟩

theorem triangle_sector_two {z : ℂ} (hz : z ∈ σ.triangle) (h2 : z ≠ σ.vertexTwo) :
    σ.rotTwo z ≠ 0 ∧ -(σ.θ₂ / 2) < arg (σ.rotTwo z) ∧ arg (σ.rotTwo z) < 3 * σ.θ₂ / 2 := by
  have hne : σ.rotTwo z ≠ 0 := by
    intro h
    apply h2
    rw [EuclidShape.rotTwo, neg_eq_zero, mul_eq_zero] at h
    rcases h with h | h
    · exact absurd h (Complex.exp_ne_zero _)
    · exact sub_eq_zero.mp h
  have a : 0 ≤ (σ.rotTwo z).im := hz 2
  have b := hz 0
  rw [σ.wallSide_zero_eq_rotTwo] at b
  obtain ⟨c1, c2⟩ := arg_mem_Icc_of_sides σ.θ₂_pos σ.θ₂_le hne a (by linarith)
  have := σ.θ₂_pos
  exact ⟨hne, by linarith, by linarith⟩

theorem triangle_sector_three {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) :
    z ≠ 0 ∧ -(σ.θ₃ / 2) < arg z ∧ arg z < 3 * σ.θ₃ / 2 := by
  have a : 0 ≤ z.im := hz 0
  have b := hz 1
  rw [σ.wallSide_one_eq_rotThree] at b
  obtain ⟨c1, c2⟩ := arg_mem_Icc_of_sides σ.θ₃_pos σ.θ₃_le h0 a (by linarith)
  have := σ.θ₃_pos
  exact ⟨h0, by linarith, by linarith⟩

end Sectors

section Surj

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (h0 : d.orbChi = 0)
  (D : (C.closedEuclidShape hc h3 h0).toCompactShape.FoldData)

set_option hygiene false in
local notation "𝒦" => flatDatum C hc h3 h0 D

theorem flatMap_of_triangle {x : ModelCoordinates} (hz : planeOf x ∈ (𝒦).σ.triangle)
    (hz0 : planeOf x ≠ 0) (hz1 : planeOf x ≠ (𝒦).σ.vertexOne)
    (hz2 : planeOf x ≠ (𝒦).σ.vertexTwo) :
    flatMap C hc h3 (𝒦) x = C.closedChart hc h3 ((𝒦).liftP x) ∧ x ∈ flatDomain (𝒦) := by
  have hcov := triangle_diff_subset_cover (𝒦).D ⟨hz, hz0⟩
  simp only [mem_union] at hcov
  have hdom : ∀ h : planeOf x ∈ mainSet (𝒦).D ∨ planeOf x ∈ discOne (𝒦).D ∨
      planeOf x ∈ discTwo (𝒦).D ∨ planeOf x ∈ discThree (𝒦).D, x ∈ flatDomain (𝒦) := by
    intro h
    change planeOf x ∈ flatBase (𝒦)
    simp only [flatBase, mem_union, mem_ofPred_eq]
    tauto
  rcases hcov with ((hm | hd) | hd) | hd
  · exact ⟨flatMap_of_main C hc h3 h0 D hm, hdom (Or.inl hm)⟩
  · refine ⟨?_, hdom (Or.inr (Or.inl hd))⟩
    rw [flatMap_of_discOne C hc h3 _ hd]
    exact tubeOne_eq_liftP C hc h3 h0 D hd (triangle_sector_one hz hz1)
  · refine ⟨?_, hdom (Or.inr (Or.inr (Or.inl hd)))⟩
    rw [flatMap_of_discTwo C hc h3 _ hd]
    exact tubeTwo_eq_liftP C hc h3 h0 D hd (triangle_sector_two hz hz2)
  · refine ⟨?_, hdom (Or.inr (Or.inr (Or.inr hd)))⟩
    rw [flatMap_of_discThree C hc h3 _ hd]
    exact tubeThree_eq_liftP C hc h3 h0 D hd (triangle_sector_three hz hz0)

theorem flatMap_of_conjTriangle {x : ModelCoordinates}
    (hz : conj (planeOf x) ∈ (𝒦).σ.triangle) (hz0 : conj (planeOf x) ≠ 0)
    (hz1 : conj (planeOf x) ≠ (𝒦).σ.vertexOne) (hz2 : conj (planeOf x) ≠ (𝒦).σ.vertexTwo) :
    flatMap C hc h3 (𝒦) x = C.closedChart hc h3 ((𝒦).liftM x) ∧ x ∈ flatDomain (𝒦) := by
  have hcov := triangle_diff_subset_cover (𝒦).D ⟨hz, hz0⟩
  simp only [mem_union] at hcov
  have hdom : ∀ h : conj (planeOf x) ∈ mainSet (𝒦).D ∨ planeOf x ∈ discOneMirror (𝒦).D ∨
      planeOf x ∈ discTwo (𝒦).D ∨ planeOf x ∈ discThree (𝒦).D, x ∈ flatDomain (𝒦) := by
    intro h
    change planeOf x ∈ flatBase (𝒦)
    simp only [flatBase, mem_union, mem_ofPred_eq]
    tauto
  have hconj : ∀ {S : Set ℂ}, (∀ w ∈ S, conj w ∈ S) → conj (planeOf x) ∈ S → planeOf x ∈ S :=
    fun hS h => by simpa using hS _ h
  rcases hcov with ((hm | hd) | hd) | hd
  · exact ⟨flatMap_of_conjMain C hc h3 h0 D hm, hdom (Or.inl hm)⟩
  · have hd' : planeOf x ∈ discOneMirror (𝒦).D := (mem_discOneMirror_iff _).2 hd
    refine ⟨?_, hdom (Or.inr (Or.inl hd'))⟩
    rw [flatMap_of_discOneMirror C hc h3 _ hd']
    exact tubeOne_eq_liftM C hc h3 h0 D hd (triangle_sector_one hz hz1)
  · have hd' : planeOf x ∈ discTwo (𝒦).D := hconj (fun w hw => conj_mem_discTwo _ hw) hd
    refine ⟨?_, hdom (Or.inr (Or.inr (Or.inl hd')))⟩
    rw [flatMap_of_discTwo C hc h3 _ hd']
    exact tubeTwo_eq_liftM C hc h3 h0 D hd' (triangle_sector_two hz hz2)
  · have hd' : planeOf x ∈ discThree (𝒦).D := hconj (fun w hw => conj_mem_discThree _ hw) hd
    refine ⟨?_, hdom (Or.inr (Or.inr (Or.inr hd')))⟩
    rw [flatMap_of_discThree C hc h3 _ hd']
    exact tubeThree_eq_liftM C hc h3 h0 D hd' (triangle_sector_three hz hz0)

theorem exists_eC_eq (w : Circle) : ∃ s : ℝ, eC s = w := by
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective w
  refine ⟨θ / (2 * Real.pi), ?_⟩
  rw [eC, mul_div_cancel₀ _ (by positivity)]
  exact hθ

theorem surjective_flatMap (q : W.pieceInterior ⊤) :
    ∃ x ∈ flatDomain (𝒦), flatMap C hc h3 (𝒦) x = q := by
  have hℓ := (𝒦).ℓ_ne
  rcases C.exists_closedChart_eq hc h3 q with ⟨y, hy, rfl⟩ | ⟨m, w, rfl⟩
  · obtain ⟨hy7, hy1, hy2⟩ := hy
    by_cases him : 0 ≤ y.1.im
    · obtain ⟨z, ⟨hzT, hz0⟩, hfz⟩ := (bijOn_f' (𝒦).D).surjOn (⟨hy7, him⟩ : y.1 ∈ basePlusSeven)
      have hz1 : z ≠ (𝒦).σ.vertexOne := by
        rintro rfl; exact hy1 (hfz.symm.trans (f_vertexOne _))
      have hz2 : z ≠ (𝒦).σ.vertexTwo := by
        rintro rfl; exact hy2 (hfz.symm.trans (f_vertexTwo _))
      obtain ⟨s, hs⟩ := exists_eC_eq (y.2 * ((𝒦).psiC z)⁻¹)
      set x := ofPlane z ((𝒦).ℓ * s) with hx
      have hpx : planeOf x = z := planeOf_ofPlane _ _
      obtain ⟨hF, hdom⟩ := flatMap_of_triangle C hc h3 h0 D (x := x) (hpx ▸ hzT) (hpx ▸ hz0)
        (hpx ▸ hz1) (hpx ▸ hz2)
      refine ⟨x, hdom, ?_⟩
      rw [hF]
      congr 1
      unfold FlatDatum.liftP
      rw [hpx, hfz, hx, ofPlane_apply_two, mul_div_cancel_left₀ _ hℓ, hs, inv_mul_cancel_right]
    · push Not at him
      have hc7 : conj y.1 ∈ basePlusSeven := ⟨by rw [Complex.norm_conj]; exact hy7,
        by rw [conj_im]; linarith⟩
      obtain ⟨z, ⟨hzT, hz0⟩, hfz⟩ := (bijOn_f' (𝒦).D).surjOn hc7
      have hz1 : z ≠ (𝒦).σ.vertexOne := by
        rintro rfl
        apply hy1
        have := congrArg conj (hfz.symm.trans (f_vertexOne _))
        rwa [Complex.conj_conj, map_div₀, map_ofNat, map_ofNat] at this
      have hz2 : z ≠ (𝒦).σ.vertexTwo := by
        rintro rfl
        apply hy2
        have := congrArg conj (hfz.symm.trans (f_vertexTwo _))
        rwa [Complex.conj_conj, map_neg, map_div₀, map_ofNat, map_ofNat] at this
      obtain ⟨s, hs⟩ := exists_eC_eq (y.2⁻¹ * ((𝒦).psiC z)⁻¹)
      set x := ofPlane (conj z) ((𝒦).c₀ - (𝒦).ℓ * s) with hx
      have hpx : conj (planeOf x) = z := by rw [hx, planeOf_ofPlane, Complex.conj_conj]
      obtain ⟨hF, hdom⟩ := flatMap_of_conjTriangle C hc h3 h0 D (x := x) (hpx ▸ hzT)
        (hpx ▸ hz0) (hpx ▸ hz1) (hpx ▸ hz2)
      refine ⟨x, hdom, ?_⟩
      rw [hF]
      congr 1
      unfold FlatDatum.liftM FlatDatum.liftP conjPair
      rw [planeOf_reflectMap, hpx, hfz, Complex.conj_conj, reflectMap_two, hx, ofPlane_apply_two,
        sub_sub_cancel, mul_div_cancel_left₀ _ hℓ, hs, inv_mul_cancel_right, inv_inv]
  · obtain ⟨j, rfl⟩ := (C.closedHoleEquiv hc h3).surjective m
    fin_cases j
    · obtain ⟨s, hs⟩ := exists_eC_eq w
      set x := ofPlane 0 ((𝒦).ℓ * (s / (𝒦).σ.p₃ - (𝒦).betaThree)) with hx
      have hpx : planeOf x = 0 := planeOf_ofPlane _ _
      have hd : planeOf x ∈ discThree (𝒦).D := by
        change ‖planeOf x‖ < _; rw [hpx, norm_zero]; exact radThree_pos _
      refine ⟨x, ?_, ?_⟩
      · change planeOf x ∈ flatBase (𝒦)
        simp only [flatBase, mem_union]
        exact Or.inr hd
      · rw [flatMap_of_discThree C hc h3 _ hd]
        congr 1
        unfold FlatDatum.tubeThree FlatDatum.sThree
        rw [hpx, mul_zero, zero_mul, hx, ofPlane_apply_two, mul_div_cancel_left₀ _ hℓ,
          sub_add_cancel, mul_div_cancel₀ _ (by exact_mod_cast (𝒦).p₃_pos.ne'), hs]
    · obtain ⟨s, hs⟩ := exists_eC_eq w
      set x := ofPlane (𝒦).σ.vertexOne
        ((𝒦).ℓ * (s / (𝒦).σ.p₁ - (𝒦).betaOne (𝒦).σ.vertexOne)) with hx
      have hpx : planeOf x = (𝒦).σ.vertexOne := planeOf_ofPlane _ _
      have hd : planeOf x ∈ discOne (𝒦).D := by
        change ‖planeOf x - _‖ < _; rw [hpx, sub_self, norm_zero]; exact radOne_pos _
      refine ⟨x, ?_, ?_⟩
      · change planeOf x ∈ flatBase (𝒦)
        simp only [flatBase, mem_union]
        exact Or.inl (Or.inl (Or.inl (Or.inr hd)))
      · rw [flatMap_of_discOne C hc h3 _ hd]
        congr 1
        unfold FlatDatum.tubeOne FlatDatum.sOne
        rw [hpx, (𝒦).σ.rotOne_vertexOne, zero_mul, hx, ofPlane_apply_two,
          mul_div_cancel_left₀ _ hℓ, sub_add_cancel,
          mul_div_cancel₀ _ (by exact_mod_cast (𝒦).p₁_pos.ne'), hs]
    · obtain ⟨s, hs⟩ := exists_eC_eq w
      set x := ofPlane (𝒦).σ.vertexTwo
        ((𝒦).ℓ * (s / (𝒦).σ.p₂ - (𝒦).betaTwo (𝒦).σ.vertexTwo)) with hx
      have hpx : planeOf x = (𝒦).σ.vertexTwo := planeOf_ofPlane _ _
      have hd : planeOf x ∈ discTwo (𝒦).D := by
        change ‖planeOf x - _‖ < _; rw [hpx, sub_self, norm_zero]; exact radTwo_pos _
      refine ⟨x, ?_, ?_⟩
      · change planeOf x ∈ flatBase (𝒦)
        simp only [flatBase, mem_union]
        exact Or.inl (Or.inr hd)
      · rw [flatMap_of_discTwo C hc h3 _ hd]
        congr 1
        unfold FlatDatum.tubeTwo FlatDatum.sTwo
        rw [hpx, (𝒦).σ.rotTwo_vertexTwo, zero_mul, hx, ofPlane_apply_two,
          mul_div_cancel_left₀ _ hℓ, sub_add_cancel,
          mul_div_cancel₀ _ (by exact_mod_cast (𝒦).p₂_pos.ne'), hs]

end Surj

end ClosedTriangle

end GC.Seifert
