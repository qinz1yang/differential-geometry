/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.WallSystemCellTopology
import DifferentialGeometry.Topology.PiecewiseLinear.WallChartTransition
import DifferentialGeometry.Topology.PiecewiseLinear.ConeComplex

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

theorem IsCommonWallSystem.injOn_chartAffine {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {Cf Bf : Set (Finset Ea)} {BdM C : Set M} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb Eb' : ι → Set M}
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ec ℓ Eb Eb') (i : ι) {s : Finset Ea}
    (hs : s ∈ Q.faces) (hsE : wallSystemCell ρ s ⊆ Eb' i)
    {A : Ea →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)} (hA : ∀ x ∈ wallSystemCell ρ s, ec i x = A (ρ x)) :
    InjOn A (convexHull ℝ (s : Set Ea)) := by
  intro q hq q' hq' hqq
  have hqr : q ∈ range ρ := hsys.rangeEq ▸ Q.convexHull_subset_space hs hq
  have hqr' : q' ∈ range ρ := hsys.rangeEq ▸ Q.convexHull_subset_space hs hq'
  obtain ⟨x, rfl⟩ := hqr
  obtain ⟨x', rfl⟩ := hqr'
  have hx : x ∈ wallSystemCell ρ s := hq
  have hx' : x' ∈ wallSystemCell ρ s := hq'
  have hxx : x = x' := (ec i).injOn (hsys.layerSource i (hsE hx))
    (hsys.layerSource i (hsE hx')) (by rw [hA x hx, hA x' hx', hqq])
  rw [hxx]

theorem IsCommonWallSystem.exists_wallChart_sides {Q : Geometry.SimplicialComplex ℝ Ea}
    {ρ : M → Ea} {Cf Bf : Set (Finset Ea)} {BdM C : Set M} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb Eb' : ι → Set M}
    (hsys : IsCommonWallSystem Q ρ Cf Bf BdM C ec ℓ Eb Eb') (i : ι) {w : Finset Ea}
    (hw : w ∈ wallSystemWalls Q) {y : M} (hyw : y ∈ wallSystemCell ρ w)
    (hyskel : y ∉ wallSystemSkeleton Q ρ) (hyE : y ∈ Eb i) :
    ∃ cm ∈ wallSystemCells Q, ∃ cp ∈ wallSystemCells Q, cm ≠ cp ∧ w ⊆ cm ∧ w ⊆ cp ∧
      ∃ (ν : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] ℝ) (U : Set M), IsOpen U ∧ y ∈ U ∧
        U ⊆ (ec i).source ∧ U ⊆ wallSystemCell ρ cm ∪ wallSystemCell ρ cp ∧
        (∀ c ∈ wallSystemCells Q, (U ∩ wallSystemCell ρ c).Nonempty → c = cm ∨ c = cp) ∧
        (∀ w' ∈ wallSystemWalls Q, U ∩ wallSystemCell ρ w' ⊆ wallSystemCell ρ w) ∧
        Disjoint U (wallSystemSkeleton Q ρ) ∧
        (∀ x ∈ U, x ∈ wallSystemCell ρ w ↔ ν (ec i x) = 0) ∧
        (∀ x ∈ U ∩ wallSystemCell ρ cm, ν (ec i x) ≤ 0) ∧
        (∀ x ∈ U ∩ wallSystemCell ρ cp, 0 ≤ ν (ec i x)) ∧
        (∀ x ∈ U, ν (ec i x) < 0 → x ∈ wallSystemCellInt ρ cm) ∧
        ∀ x ∈ U, 0 < ν (ec i x) → x ∈ wallSystemCellInt ρ cp := by
  classical
  obtain ⟨cm, hcm, cp, hcp, hne, hwm, hwp, huniq⟩ := hsys.wallSides w hw
  have hywInt : y ∈ wallSystemCellInt ρ w := by
    by_contra h
    exact hyskel (wallSystemCell_sdiff_subset_wallSystemSkeleton hw ⟨hyw, h⟩)
  have hwcm : wallSystemCell ρ w ⊆ wallSystemCell ρ cm :=
    fun x hx => convexHull_mono (Finset.coe_subset.mpr hwm) hx
  have hwcp : wallSystemCell ρ w ⊆ wallSystemCell ρ cp :=
    fun x hx => convexHull_mono (Finset.coe_subset.mpr hwp) hx
  have hmE : wallSystemCell ρ cm ⊆ Eb' i := hsys.starLayer i cm hcm ⟨y, hwcm hyw, hyE⟩
  have hpE : wallSystemCell ρ cp ⊆ Eb' i := hsys.starLayer i cp hcp ⟨y, hwcp hyw, hyE⟩
  obtain ⟨Am, hAm⟩ := hsys.chartAffine i cm hcm.1 hmE
  obtain ⟨Ap, hAp⟩ := hsys.chartAffine i cp hcp.1 hpE
  have hinjm := hsys.injOn_chartAffine i hcm.1 hmE hAm
  have hinjp := hsys.injOn_chartAffine i hcp.1 hpE hAp
  have hw3 : w.card = 3 := hw.2
  have hwne : w.Nonempty := Finset.card_pos.mp (by rw [hw3]; norm_num)
  obtain ⟨qm, hqmw, hcmeq⟩ := Finset.exists_eq_insert_iff.mpr ⟨hwm, by rw [hcm.2, hw3]⟩
  obtain ⟨qp, hqpw, hcpeq⟩ := Finset.exists_eq_insert_iff.mpr ⟨hwp, by rw [hcp.2, hw3]⟩
  replace hcmeq := hcmeq.symm
  replace hcpeq := hcpeq.symm
  have hqm : qm ∈ cm := by rw [hcmeq]; exact Finset.mem_insert_self qm w
  have hqp : qp ∈ cp := by rw [hcpeq]; exact Finset.mem_insert_self qp w
  have hindm : AffineIndependent ℝ (Am ∘ ((↑) : cm → Ea)) :=
    AffineIndependent.comp_affineMap_of_injOn (Q.indep hcm.1) Am (by rwa [Subtype.range_coe])
  have hindp : AffineIndependent ℝ (Ap ∘ ((↑) : cp → Ea)) :=
    AffineIndependent.comp_affineMap_of_injOn (Q.indep hcp.1) Ap (by rwa [Subtype.range_coe])
  have htopm : affineSpan ℝ (range (Am ∘ ((↑) : cm → Ea))) = ⊤ := by
    rw [hindm.affineSpan_eq_top_iff_card_eq_finrank_add_one, Fintype.card_coe, hcm.2,
      finrank_euclideanSpace_fin]
  have htopp : affineSpan ℝ (range (Ap ∘ ((↑) : cp → Ea))) = ⊤ := by
    rw [hindp.affineSpan_eq_top_iff_card_eq_finrank_add_one, Fintype.card_coe, hcp.2,
      finrank_euclideanSpace_fin]
  let bm : AffineBasis cm ℝ (EuclideanSpace ℝ (Fin 3)) := ⟨Am ∘ ((↑) : cm → Ea), hindm, htopm⟩
  let ν : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] ℝ := -bm.coord ⟨qm, hqm⟩
  have hνqm : ν (Am qm) = -1 := by
    have h := bm.coord_apply_eq ⟨qm, hqm⟩
    change -(bm.coord ⟨qm, hqm⟩ (Am qm)) = -1
    rw [show Am qm = bm ⟨qm, hqm⟩ from rfl, h]
  have hνv : ∀ v ∈ w, ν (Am v) = 0 := by
    intro v hv
    have hvm : v ∈ cm := hwm hv
    have hvne : (⟨qm, hqm⟩ : cm) ≠ ⟨v, hvm⟩ := by
      intro h
      apply hqmw
      have : qm = v := congrArg Subtype.val h
      rw [this]
      exact hv
    have h := bm.coord_apply_ne hvne
    change -(bm.coord ⟨qm, hqm⟩ (Am v)) = 0
    rw [show Am v = bm ⟨v, hvm⟩ from rfl, h, neg_zero]
  have hνw : ∀ z ∈ convexHull ℝ (w : Set Ea), ν (Am z) = 0 := by
    have hconv : Convex ℝ ((ν.comp Am) ⁻¹' {0}) :=
      (convex_singleton (0 : ℝ)).affine_preimage (ν.comp Am)
    exact fun z hz => convexHull_min (fun v hv => hνv v (Finset.mem_coe.mp hv)) hconv hz
  have hApm : ∀ z ∈ convexHull ℝ (w : Set Ea), Ap z = Am z := by
    intro z hz
    have hzr : z ∈ range ρ := hsys.rangeEq ▸ Q.convexHull_subset_space hw.1 hz
    obtain ⟨x, rfl⟩ := hzr
    rw [← hAp x (hwcp hz), ← hAm x (hwcm hz)]
  have hνcell : ∀ (A : Ea →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (q : Ea), q ∉ w →
      (∀ z ∈ convexHull ℝ (w : Set Ea), ν (A z) = 0) →
      ∀ z ∈ convexHull ℝ ((insert q w : Finset Ea) : Set Ea), ∃ θ : ℝ, 0 ≤ θ ∧
        ν (A z) = θ * ν (A q) ∧ (θ = 0 → z ∈ convexHull ℝ (w : Set Ea)) := by
    intro A q hqw hA0 z hz
    rcases exists_combo_of_mem_convexHull_insert hqw hz with rfl | ⟨z', hz', t, ht0, ht1, rfl⟩
    · exact ⟨1, zero_le_one, (one_mul _).symm, fun h => absurd h one_ne_zero⟩
    · refine ⟨1 - t, by linarith, ?_, fun hθ => ?_⟩
      · have h : ν (A (q + t • (z' - q))) = ν (A q) + t * (ν (A z') - ν (A q)) := by
          have hlm : q + t • (z' - q) = AffineMap.lineMap q z' t := by
            rw [AffineMap.lineMap_apply_module']
            abel
          have h2 := AffineMap.apply_lineMap (ν.comp A) q z' t
          rw [AffineMap.lineMap_apply_ring'] at h2
          simp only [AffineMap.comp_apply] at h2
          rw [hlm, h2]
          ring
        rw [h, hA0 z' hz']
        ring
      · have ht : t = 1 := by linarith
        rw [ht, one_smul, add_sub_cancel]
        exact hz'
  have hνAp0 : ∀ z ∈ convexHull ℝ (w : Set Ea), ν (Ap z) = 0 := fun z hz => by
    rw [hApm z hz]
    exact hνw z hz
  have hκne : ν (Ap qp) ≠ 0 := by
    intro hκ
    have hzero : EqOn ν (AffineMap.const ℝ (EuclideanSpace ℝ (Fin 3)) (0 : ℝ))
        (range (Ap ∘ ((↑) : cp → Ea))) := by
      rintro _ ⟨v, rfl⟩
      simp only [Function.comp_apply, AffineMap.const_apply]
      have hv : (v : Ea) ∈ insert qp w := hcpeq ▸ v.2
      rcases Finset.mem_insert.mp hv with h | h
      · rw [h]
        exact hκ
      · exact hνAp0 v (subset_convexHull ℝ _ (Finset.mem_coe.mpr h))
    have hν0 := AffineMap.ext_on htopp hzero
    have h := hνqm
    rw [hν0, AffineMap.const_apply] at h
    norm_num at h
  have hstar : IsOpen ((ec i).source ∩ wallSystemStar Q ρ w) :=
    (ec i).open_source.inter (isOpen_wallSystemStar hsys.finiteFaces hsys.continuous w)
  have hystar : y ∈ (ec i).source ∩ wallSystemStar Q ρ w :=
    ⟨hsys.layerSource i (hmE (hwcm hyw)), wallSystemCellInt_subset_wallSystemStar hw.1 hywInt⟩
  have hstarsub : wallSystemStar Q ρ w ⊆ wallSystemCell ρ cm ∪ wallSystemCell ρ cp :=
    wallSystemStar_subset_union_wallSystemCell hsys.rangeEq hsys.memCell huniq
  have hνy : ν (ec i y) = 0 := by
    rw [hAm y (hwcm hyw)]
    exact hνw (ρ y) hyw
  have hκpos : 0 < ν (Ap qp) := by
    rcases lt_or_gt_of_ne hκne with hneg | hpos
    · exfalso
      have hopen := (ec i).isOpen_image_of_subset_source hstar inter_subset_left
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen (ec i y) ⟨y, hystar, rfl⟩
      obtain ⟨q₀, hq₀⟩ := hwne
      set d : EuclideanSpace ℝ (Fin 3) := Am qm - Am q₀ with hd
      have hνd : ν.linear d = -1 := by
        rw [hd, ← vsub_eq_sub, AffineMap.linearMap_vsub, vsub_eq_sub, hνqm, hνv q₀ hq₀]
        norm_num
      set t : ℝ := ε / (2 * (‖d‖ + 1)) with ht
      have hden : 0 < 2 * (‖d‖ + 1) := by positivity
      have htpos : 0 < t := div_pos hε hden
      have hmem : ec i y - t • d ∈ Metric.ball (ec i y) ε := by
        rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
          Real.norm_eq_abs, abs_of_pos htpos]
        have h1 : t * ‖d‖ ≤ t * (‖d‖ + 1) := by nlinarith [norm_nonneg d]
        have h2 : t * (‖d‖ + 1) = ε / 2 := by
          rw [ht]
          field_simp
        linarith
      obtain ⟨x, ⟨hxs, hxst⟩, hxeq⟩ := hball hmem
      have hνx : ν (ec i x) = t := by
        rw [hxeq, sub_eq_neg_add, ← vadd_eq_add, AffineMap.map_vadd, vadd_eq_add, hνy,
          map_neg, map_smul, hνd, smul_eq_mul]
        ring
      rcases hstarsub hxst with hxm | hxp
      · obtain ⟨θ, hθ, heq, -⟩ := hνcell Am qm hqmw hνw (ρ x) (hcmeq ▸ hxm)
        rw [← hAm x hxm, hνqm] at heq
        linarith
      · obtain ⟨θ, hθ, heq, -⟩ := hνcell Ap qp hqpw hνAp0 (ρ x) (hcpeq ▸ hxp)
        rw [← hAp x hxp] at heq
        nlinarith
    · exact hpos
  have hsidem : ∀ x ∈ wallSystemCell ρ cm, ν (ec i x) ≤ 0 ∧
      (ν (ec i x) = 0 → x ∈ wallSystemCell ρ w) := by
    intro x hx
    obtain ⟨θ, hθ, heq, hθw⟩ := hνcell Am qm hqmw hνw (ρ x) (hcmeq ▸ hx)
    rw [← hAm x hx, hνqm] at heq
    refine ⟨by linarith, fun h0 => hθw (by linarith)⟩
  have hsidep : ∀ x ∈ wallSystemCell ρ cp, 0 ≤ ν (ec i x) ∧
      (ν (ec i x) = 0 → x ∈ wallSystemCell ρ w) := by
    intro x hx
    obtain ⟨θ, hθ, heq, hθw⟩ := hνcell Ap qp hqpw hνAp0 (ρ x) (hcpeq ▸ hx)
    rw [← hAp x hx] at heq
    refine ⟨by rw [heq]; positivity, fun h0 => hθw ?_⟩
    rw [heq] at h0
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hκne
  let Bad : Set M :=
    (⋃ c ∈ {c | c ∈ wallSystemCells Q ∧ y ∉ wallSystemCell ρ c}, wallSystemCell ρ c) ∪
      (⋃ w' ∈ {w' | w' ∈ wallSystemWalls Q ∧ y ∉ wallSystemCell ρ w'}, wallSystemCell ρ w') ∪
      wallSystemSkeleton Q ρ
  have hBad : IsClosed Bad := by
    refine ((Set.Finite.isClosed_biUnion (hsys.finiteFaces.subset fun c hc => hc.1.1)
      fun c _ => isClosed_wallSystemCell hsys.continuous c).union
      (Set.Finite.isClosed_biUnion (hsys.finiteFaces.subset fun c hc => hc.1.1)
      fun c _ => isClosed_wallSystemCell hsys.continuous c)).union ?_
    exact isClosed_wallSystemSkeleton hsys.finiteFaces hsys.continuous
  let U : Set M := (ec i).source ∩ Badᶜ
  have hyU : y ∈ U := by
    refine ⟨hystar.1, ?_⟩
    rintro ((h | h) | h)
    · obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.mp h
      exact hc.2 hyc
    · obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.mp h
      exact hc.2 hyc
    · exact hyskel h
  have hcellU : ∀ c ∈ wallSystemCells Q, (U ∩ wallSystemCell ρ c).Nonempty → c = cm ∨ c = cp := by
    rintro c hc ⟨x, hxU, hxc⟩
    have hyc : y ∈ wallSystemCell ρ c := by
      by_contra hyc
      exact hxU.2 (Or.inl (Or.inl (mem_iUnion₂.mpr ⟨c, ⟨hc, hyc⟩, hxc⟩)))
    exact huniq c hc (face_subset_of_mem_openSimplex_of_mem_convexHull Q hw.1 hc.1 hywInt hyc)
  have hUsub : U ⊆ wallSystemCell ρ cm ∪ wallSystemCell ρ cp := by
    intro x hxU
    have hcov := iUnion_wallSystemCell_eq_univ hsys.rangeEq hsys.memCell
    have hx : x ∈ ⋃ c ∈ wallSystemCells Q, wallSystemCell ρ c := by rw [hcov]; exact mem_univ x
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hx
    rcases hcellU c hc ⟨x, hxU, hxc⟩ with rfl | rfl
    · exact Or.inl hxc
    · exact Or.inr hxc
  have hwallU : ∀ w' ∈ wallSystemWalls Q, U ∩ wallSystemCell ρ w' ⊆ wallSystemCell ρ w := by
    rintro w' hw' x ⟨hxU, hxw'⟩
    have hyw' : y ∈ wallSystemCell ρ w' := by
      by_contra hyw'
      exact hxU.2 (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨w', ⟨hw', hyw'⟩, hxw'⟩)))
    have hsub := face_subset_of_mem_openSimplex_of_mem_convexHull Q hw.1 hw'.1 hywInt hyw'
    have hw3' : w'.card = 3 := hw'.2
    rw [Finset.eq_of_subset_of_card_le hsub (by omega)]
    exact hxw'
  have hzero : ∀ x ∈ U, x ∈ wallSystemCell ρ w ↔ ν (ec i x) = 0 := by
    intro x hxU
    constructor
    · intro hxw
      rw [hAm x (hwcm hxw)]
      exact hνw (ρ x) hxw
    · intro h0
      rcases hUsub hxU with hxm | hxp
      · exact (hsidem x hxm).2 h0
      · exact (hsidep x hxp).2 h0
  have hint : ∀ c ∈ wallSystemCells Q, ∀ x ∈ U, x ∈ wallSystemCell ρ c → ν (ec i x) ≠ 0 →
      x ∈ wallSystemCellInt ρ c := by
    intro c hc x hxU hxc h0
    by_contra hxi
    obtain ⟨w', hw', hxw'⟩ := mem_iUnion₂.mp (wallSystemCell_sdiff_subset_iUnion_wall hc ⟨hxc, hxi⟩)
    exact h0 ((hzero x hxU).mp (hwallU w' hw' ⟨hxU, hxw'⟩))
  refine ⟨cm, hcm, cp, hcp, hne, hwm, hwp, ν, U, (ec i).open_source.inter hBad.isOpen_compl, hyU,
    inter_subset_left, hUsub, hcellU, hwallU, ?_, hzero, fun x hx => (hsidem x hx.2).1,
    fun x hx => (hsidep x hx.2).1, ?_, ?_⟩
  · exact Set.disjoint_left.mpr fun x hxU hxs => hxU.2 (Or.inr hxs)
  · intro x hxU hneg
    rcases hUsub hxU with hxm | hxp
    · exact hint cm hcm x hxU hxm hneg.ne
    · exact absurd (hsidep x hxp).1 (not_le.mpr hneg)
  · intro x hxU hpos
    rcases hUsub hxU with hxm | hxp
    · exact absurd (hsidem x hxm).1 (not_le.mpr hpos)
    · exact hint cp hcp x hxU hxp hpos.ne'

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear
