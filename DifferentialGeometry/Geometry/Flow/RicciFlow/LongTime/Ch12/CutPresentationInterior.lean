import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutPresentationRecon

set_option autoImplicit false
noncomputable section
open Set Function Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

variable {M : ConnectedClosedOrientedManifold.{u} 3} (F : CollaredTorusFamily_C2a M.Carrier)

/-- The cut tori `σ_i(T² × {0})` in `M`. -/
def zeroSet_S12 : Set M.Carrier := ⋃ i, F.collar i '' (univ ×ˢ {0})

theorem isClosed_zeroSet_S12 : IsClosed (zeroSet_S12 F) := by
  refine isClosed_iUnion_of_finite fun i => ?_
  have hc : IsCompact (univ ×ˢ ({0} : Set ℝ) : Set (Torus × ℝ)) :=
    isCompact_univ.prod isCompact_singleton
  refine (hc.image_of_continuousOn ?_).isClosed
  refine (F.collar i).toOpenPartialHomeomorph.continuousOn.mono ?_
  change _ ⊆ (F.collar i).source
  rw [F.source_eq]
  rintro ⟨t, s⟩ ⟨-, hs⟩
  have : s = 0 := hs
  subst this
  exact ⟨by norm_num, by norm_num⟩

/-- The image of the interior of the cut carrier in `M`: the complement of the cut tori. -/
def interiorImage_S12 : TopologicalSpace.Opens M.Carrier :=
  ⟨(zeroSet_S12 F)ᶜ, (isClosed_zeroSet_S12 F).isOpen_compl⟩

theorem mem_interior_iff_S12 (x : (cutCarrier_C2a F).Carrier) :
    x ∈ (cutCarrier_C2a F).interior ↔
      ∀ i, (∀ t, x.1 ≠ F.collar i (t, 1/2)) ∧ (∀ t, x.1 ≠ F.collar i (t, -1/2)) := by
  have h1 : x ∈ (cutCarrier_C2a F).interior ↔ x ∉ (cutCarrier_C2a F).model.boundary
      (cutCarrier_C2a F).Carrier := by
    have h2 : x ∈ (cutCarrier_C2a F).interior ↔
        x ∈ (cutCarrier_C2a F).model.interior (cutCarrier_C2a F).Carrier := Iff.rfl
    rw [h2]
    constructor
    · intro h hb
      exact (cutCarrier_C2a F).model.disjoint_interior_boundary.le_bot ⟨h, hb⟩
    · intro h
      rcases (cutCarrier_C2a F).model.isInteriorPoint_or_isBoundaryPoint x with h' | h'
      · exact h'
      · exact absurd h' h
  rw [h1, cutIncl_boundary_iff_C2a]
  push Not
  exact Iff.rfl

theorem sideTorus_not_interior_left_S12 (i : Fin F.count) (t : Torus) :
    sideTorus_C2a F i hL_C2a t ∉ (cutCarrier_C2a F).interior := by
  intro h
  exact (((mem_interior_iff_S12 F (sideTorus_C2a F i hL_C2a t)).mp h) i).2 t
    (sideTorus_val_left_S12 F i t)

theorem sideTorus_not_interior_right_S12 (i : Fin F.count) (t : Torus) :
    sideTorus_C2a F i hR_C2a t ∉ (cutCarrier_C2a F).interior := by
  intro h
  exact (((mem_interior_iff_S12 F (sideTorus_C2a F i hR_C2a t)).mp h) i).1 t
    (sideTorus_val_right_S12 F i t)

theorem rmapK_interior_mem_S12 {x : (cutCarrier_C2a F).Carrier}
    (hx : x ∈ (cutCarrier_C2a F).interior) : rmapK_S12 F x ∈ interiorImage_S12 F := by
  have hxi := (mem_interior_iff_S12 F x).mp hx
  intro hz
  obtain ⟨i, ⟨t, s⟩, ⟨-, hs⟩, hit⟩ := mem_iUnion.mp hz
  have hs0 : s = 0 := hs
  subst hs0
  replace hit : F.collar i (t, 0) = rmapK_S12 F x := hit
  replace hit := hit.symm
  by_cases hxt : ∃ j, x.1 ∈ (F.collar j).target
  · obtain ⟨j, hj⟩ := hxt
    have hq : (F.collar j).symm x.1 ∈ signedCollarSource := by
      have := (F.collar j).map_target hj; rwa [F.source_eq] at this
    have hxq : x.1 = F.collar j ((F.collar j).symm x.1) := ((F.collar j).right_inv hj).symm
    have hge := half_le_abs_of_mem_cut_S12 F j hq hxq
    have hR := rmap_collar_S12 (x := x) j hq hxq
    have hmemj : F.collar j (((F.collar j).symm x.1).1, rhoHat_S12 ((F.collar j).symm x.1).2)
        ∈ (F.collar j).target := by
      have := rhoHat_mem_Ioo_S12 hge (abs_lt.mpr ⟨hq.1, hq.2⟩)
      exact collar_mem_target_S12 j (q := (((F.collar j).symm x.1).1, rhoHat_S12 ((F.collar j).symm x.1).2))
        ⟨this.1, this.2⟩
    have hmemi : F.collar i (t, 0) ∈ (F.collar i).target :=
      collar_mem_target_S12 i (q := (t, 0)) ⟨by norm_num, by norm_num⟩
    have hij : j = i := by
      by_contra hne
      have h1 : rmapK_S12 F x ∈ (F.collar j).target := by
        change rmap_S12 x ∈ _; rw [hR]; exact hmemj
      have h2 : rmapK_S12 F x ∈ (F.collar i).target := by rw [hit]; exact hmemi
      exact (Set.disjoint_left.mp (F.disjoint hne)) h1 h2
    subst hij
    have hs1 := rhoHat_mem_Ioo_S12 hge (abs_lt.mpr ⟨hq.1, hq.2⟩)
    have hinj := (F.collar j).toOpenPartialHomeomorph.injOn
      (by change _ ∈ (F.collar j).source; rw [F.source_eq]; exact ⟨hs1.1, hs1.2⟩)
      (by change _ ∈ (F.collar j).source; rw [F.source_eq]; exact ⟨by norm_num, by norm_num⟩)
      (show F.collar j (((F.collar j).symm x.1).1, rhoHat_S12 ((F.collar j).symm x.1).2) =
        F.collar j (t, 0) from by rw [← hR]; exact hit)
    have e2 : rhoHat_S12 ((F.collar j).symm x.1).2 = 0 := (Prod.ext_iff.mp hinj).2
    have e3 : rhoHat_S12 (1/2) = 0 := by rw [rhoHat_of_nonneg_S12 (by norm_num), rho_half_S12]
    have key : ∀ s : ℝ, ((F.collar j).symm x.1).2 = s →
        x.1 = F.collar j (((F.collar j).symm x.1).1, s) := fun s hs =>
      hxq.trans (congrArg (⇑(F.collar j)) (Prod.ext rfl hs))
    rcases rhoHat_inj_S12 hge (s' := 1/2) (by rw [abs_of_pos (by norm_num)]) (e2.trans e3.symm)
      with h3 | ⟨h3, -⟩ | ⟨h3, -⟩
    · exact (hxi j).1 _ (key _ h3)
    · exact (hxi j).1 _ (key _ h3)
    · exact (hxi j).2 _ (key _ h3)
  · push Not at hxt
    have hR : rmapK_S12 F x = x.1 := rmap_of_not_mem_S12 hxt
    have : x.1 ∈ tubeOpen_C2a F i := by
      rw [← hR, hit]
      exact ⟨(t, 0), ⟨trivial, by norm_num, by norm_num⟩, rfl⟩
    exact (mem_compl_iff _ _).mp x.2 (mem_iUnion.mpr ⟨i, this⟩)

/-- `R` restricted to the interior of `K`, as a map onto the complement of the cut tori. -/
def interiorFun_S12 (x : (cutCarrier_C2a F).interior) : interiorImage_S12 F :=
  ⟨rmapK_S12 F x.1, rmapK_interior_mem_S12 F x.2⟩

theorem interiorFun_injective_S12 : Injective (interiorFun_S12 F) := by
  intro a b h
  have h' : rmapK_S12 F a.1 = rmapK_S12 F b.1 := congrArg Subtype.val h
  rcases rmapK_cases_S12 F h' with h1 | ⟨i, t, h1, -⟩ | ⟨i, t, -, h1⟩
  · exact Subtype.ext h1
  · exact absurd (h1 ▸ a.2) (sideTorus_not_interior_left_S12 F i t)
  · exact absurd (h1 ▸ b.2) (sideTorus_not_interior_left_S12 F i t)

theorem interiorFun_surjective_S12 : Surjective (interiorFun_S12 F) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := rmapK_surjective_S12 F y
  have hxi : x ∈ (cutCarrier_C2a F).interior := by
    by_contra hni
    have hb : x ∈ (cutCarrier_C2a F).model.boundary (cutCarrier_C2a F).Carrier := by
      by_contra hnb
      apply hni
      exact (mem_interior_iff_S12 F x).mpr (fun i => ⟨fun t ht => hnb ((cutIncl_boundary_iff_C2a F x).mpr
          ⟨i, Or.inl ⟨t, ht⟩⟩), fun t ht => hnb ((cutIncl_boundary_iff_C2a F x).mpr
          ⟨i, Or.inr ⟨t, ht⟩⟩)⟩)
    obtain ⟨i, ⟨t, ht⟩ | ⟨t, ht⟩⟩ := (cutIncl_boundary_iff_C2a F x).mp hb
    · have hxe : x = sideTorus_C2a F i hR_C2a t := Subtype.ext (by rw [ht, sideTorus_val_right_S12])
      apply hy
      refine mem_iUnion.mpr ⟨i, (t, 0), ⟨trivial, rfl⟩, ?_⟩
      rw [← hx, hxe]
      exact (rmapK_sideTorus_right_S12 F i t).symm
    · have hxe : x = sideTorus_C2a F i hL_C2a t := Subtype.ext (by rw [ht, sideTorus_val_left_S12])
      apply hy
      refine mem_iUnion.mpr ⟨i, (t, 0), ⟨trivial, rfl⟩, ?_⟩
      rw [← hx, hxe]
      exact (rmapK_sideTorus_left_S12 F i t).symm
  exact ⟨⟨x, hxi⟩, Subtype.ext hx⟩

/-- The bijection between the interior of the cut carrier and the complement of the cut tori. -/
def interiorEquiv_S12 : (cutCarrier_C2a F).interior ≃ interiorImage_S12 F :=
  Equiv.ofBijective (interiorFun_S12 F) ⟨interiorFun_injective_S12 F, interiorFun_surjective_S12 F⟩

theorem interiorEquiv_symm_val_S12 (z : interiorImage_S12 F) (w : (cutCarrier_C2a F).Carrier)
    (hw : w ∈ (cutCarrier_C2a F).interior) (h : rmapK_S12 F w = z.1) :
    ((interiorEquiv_S12 F).symm z).1 = w := by
  have : interiorEquiv_S12 F ⟨w, hw⟩ = z := Subtype.ext h
  have h2 : (interiorEquiv_S12 F).symm z = ⟨w, hw⟩ := (Equiv.symm_apply_eq _).mpr this.symm
  rw [h2]

theorem tubeOpen_subset_slab_S12 (i : Fin F.count) : tubeOpen_C2a F i ⊆ slab_S12 F i :=
  image_mono (prod_mono subset_rfl (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩))

/-- A point of `K ⊂ M` as a point of the cut carrier. -/
def kpt_S12 {y : M.Carrier} (hy : y ∈ cutSet_C2a F) : (cutCarrier_C2a F).Carrier := ⟨y, hy⟩

theorem interior_of_not_boundary_param_S12 (i : Fin F.count) {q : Torus × ℝ}
    (hq : q ∈ signedCollarSource) (hne : q.2 ≠ 1/2 ∧ q.2 ≠ -1/2)
    (hK : F.collar i q ∈ cutSet_C2a F) :
    kpt_S12 F hK ∈ (cutCarrier_C2a F).interior := by
  rw [mem_interior_iff_S12]
  intro j
  have hj : ∀ (t : Torus) (s : ℝ), (s = 1/2 ∨ s = -1/2) → F.collar i q = F.collar j (t, s) → False := by
    intro t s hs he
    have hts : (t, s) ∈ signedCollarSource := by
      rcases hs with rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩
    have hij : i = j := by
      by_contra hne'
      exact (Set.disjoint_left.mp (F.disjoint hne')) (collar_mem_target_S12 i hq)
        (he ▸ collar_mem_target_S12 j hts)
    subst hij
    have := (F.collar i).toOpenPartialHomeomorph.injOn
      (by change _ ∈ (F.collar i).source; rw [F.source_eq]; exact hq)
      (by change _ ∈ (F.collar i).source; rw [F.source_eq]; exact hts) he
    have h2 : q.2 = s := (Prod.ext_iff.mp this).2
    rcases hs with rfl | rfl
    · exact hne.1 h2
    · exact hne.2 h2
  exact ⟨fun t ht => hj t (1/2) (Or.inl rfl) ht, fun t ht => hj t (-1/2) (Or.inr rfl) ht⟩

theorem gPlus_symm_apply_S12 (i : Fin F.count) {q : Torus × ℝ} (hq : q ∈ signedCollarSource) :
    (gPlus_S12 F i).symm (F.collar i q) = F.collar i (q.1, psi_S12 q.2) := by
  change F.collar i (phiPlus_S12.symm ((F.collar i).symm (F.collar i q))) = _
  rw [collar_symm_apply_S12 i hq]; rfl

theorem gMinus_symm_apply_S12 (i : Fin F.count) {q : Torus × ℝ} (hq : q ∈ signedCollarSource) :
    (gMinus_S12 F i).symm (F.collar i q) = F.collar i (q.1, -psi_S12 (-q.2)) := by
  change F.collar i (phiMinus_S12.symm ((F.collar i).symm (F.collar i q))) = _
  rw [collar_symm_apply_S12 i hq]; rfl

theorem contMDiff_interiorSymm_val_S12 :
    ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun z : interiorImage_S12 F => (((interiorEquiv_S12 F).symm z).1).1) := by
  refine contMDiff_of_locally_contMDiffOn fun z => ?_
  by_cases hs : ∃ i, z.1 ∈ slab_S12 F i
  · obtain ⟨i, q, ⟨-, hq1, hq2⟩, hzq⟩ := hs
    have hqs : q ∈ signedCollarSource := ⟨by linarith [hq1], by linarith [hq2]⟩
    have hq0 : q.2 ≠ 0 := by
      intro h0
      apply z.2
      exact mem_iUnion.mpr ⟨i, q, ⟨trivial, h0⟩, hzq⟩
    rcases lt_or_gt_of_ne hq0 with hneg | hpos
    · refine ⟨Subtype.val ⁻¹' (F.collar i '' (univ ×ˢ Ioo (-1 : ℝ) 0)),
        (isOpen_collarImage_S12 i le_rfl (by norm_num)).preimage continuous_subtype_val,
        ⟨q, ⟨trivial, hqs.1, hneg⟩, hzq⟩, ?_⟩
      have hG := (gMinus_S12 F i).symm.contMDiffOn
      refine (hG.comp contMDiff_subtype_val.contMDiffOn ?_).congr ?_
      · rintro y ⟨q', ⟨-, h1, h2⟩, hyq⟩
        change y.1 ∈ (gMinus_S12 F i).target
        rw [gMinus_target_S12]
        exact ⟨q', ⟨trivial, h1, by linarith⟩, hyq⟩
      · rintro y ⟨q', ⟨-, h1, h2⟩, hyq⟩
        have hq' : q' ∈ signedCollarSource := ⟨h1, by linarith⟩
        have hp : (q'.1, -psi_S12 (-q'.2)) ∈ signedCollarSource :=
          ⟨by change -1 < -psi_S12 (-q'.2); linarith [psi_lt_one_S12 (show -q'.2 < 1 by linarith)],
           by change -psi_S12 (-q'.2) < 1; linarith [half_le_psi_S12 (show 0 ≤ -q'.2 by linarith)]⟩
        have hq3 := half_le_psi_S12 (show 0 ≤ -q'.2 by linarith)
        have hq4 := strictMono_psi_S12 (show 0 < -q'.2 by linarith)
        rw [psi_zero_S12] at hq4
        have hK : F.collar i (q'.1, -psi_S12 (-q'.2)) ∈ cutSet_C2a F :=
          collar_mem_cutSet_C2a i hp (by
            change 1/2 ≤ |-psi_S12 (-q'.2)|
            rw [abs_neg, abs_of_nonneg (by linarith)]; exact hq3)
        have hint := interior_of_not_boundary_param_S12 F i hp
          ⟨by change -psi_S12 (-q'.2) ≠ 1/2; intro h; linarith,
           by change -psi_S12 (-q'.2) ≠ -1/2; intro h; linarith⟩ hK
        have hR : rmapK_S12 F (kpt_S12 F hK) = y.1 := by
          refine (rmap_collar_S12 (x := (⟨_, hK⟩ : ↥(cutSet_C2a F))) i hp rfl).trans ?_
          change F.collar i (q'.1, rhoHat_S12 (-psi_S12 (-q'.2))) = _
          rw [rhoHat_of_neg_S12 (by linarith), neg_neg, rho_psi_S12, neg_neg, ← hyq]
        have := interiorEquiv_symm_val_S12 F y (kpt_S12 F hK) hint hR
        change (((interiorEquiv_S12 F).symm y).1).1 = _
        rw [this]
        change F.collar i (q'.1, -psi_S12 (-q'.2)) = (gMinus_S12 F i).symm y.1
        rw [← hyq, gMinus_symm_apply_S12 F i hq']
    · refine ⟨Subtype.val ⁻¹' (F.collar i '' (univ ×ˢ Ioo (0 : ℝ) 1)),
        (isOpen_collarImage_S12 i (by norm_num) le_rfl).preimage continuous_subtype_val,
        ⟨q, ⟨trivial, hpos, hqs.2⟩, hzq⟩, ?_⟩
      have hG := (gPlus_S12 F i).symm.contMDiffOn
      refine (hG.comp contMDiff_subtype_val.contMDiffOn ?_).congr ?_
      · rintro y ⟨q', ⟨-, h1, h2⟩, hyq⟩
        change y.1 ∈ (gPlus_S12 F i).target
        rw [gPlus_target_S12]
        exact ⟨q', ⟨trivial, by linarith, h2⟩, hyq⟩
      · rintro y ⟨q', ⟨-, h1, h2⟩, hyq⟩
        have hq' : q' ∈ signedCollarSource := ⟨by linarith, h2⟩
        have hp : (q'.1, psi_S12 q'.2) ∈ signedCollarSource :=
          ⟨by change -1 < psi_S12 q'.2; linarith [half_le_psi_S12 h1.le],
           by change psi_S12 q'.2 < 1; exact psi_lt_one_S12 h2⟩
        have hq3 := half_le_psi_S12 h1.le
        have hq4 := strictMono_psi_S12 h1
        rw [psi_zero_S12] at hq4
        have hK : F.collar i (q'.1, psi_S12 q'.2) ∈ cutSet_C2a F :=
          collar_mem_cutSet_C2a i hp (by
            change 1/2 ≤ |psi_S12 q'.2|
            rw [abs_of_nonneg (by linarith)]; exact hq3)
        have hint := interior_of_not_boundary_param_S12 F i hp
          ⟨by change psi_S12 q'.2 ≠ 1/2; intro h; linarith,
           by change psi_S12 q'.2 ≠ -1/2; intro h; linarith⟩ hK
        have hR : rmapK_S12 F (kpt_S12 F hK) = y.1 := by
          refine (rmap_collar_S12 (x := (⟨_, hK⟩ : ↥(cutSet_C2a F))) i hp rfl).trans ?_
          change F.collar i (q'.1, rhoHat_S12 (psi_S12 q'.2)) = _
          rw [rhoHat_of_nonneg_S12 (by linarith), rho_psi_S12, ← hyq]
        have := interiorEquiv_symm_val_S12 F y (kpt_S12 F hK) hint hR
        change (((interiorEquiv_S12 F).symm y).1).1 = _
        rw [this]
        change F.collar i (q'.1, psi_S12 q'.2) = (gPlus_S12 F i).symm y.1
        rw [← hyq, gPlus_symm_apply_S12 F i hq']
  · refine ⟨Subtype.val ⁻¹' (⋃ i, slab_S12 F i)ᶜ,
      (isClosed_iUnion_of_finite isClosed_slab_S12).isOpen_compl.preimage continuous_subtype_val,
      fun h => hs (mem_iUnion.mp h), ?_⟩
    refine contMDiff_subtype_val.contMDiffOn.congr ?_
    intro y hy
    have hyK : y.1 ∈ cutSet_C2a F := by
      intro h
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      exact hy (mem_iUnion.mpr ⟨i, tubeOpen_subset_slab_S12 F i hi⟩)
    have hint : kpt_S12 F hyK ∈ (cutCarrier_C2a F).interior := by
      rw [mem_interior_iff_S12]
      intro i
      refine ⟨fun t ht => hy (mem_iUnion.mpr ⟨i, ⟨(t, 1/2), ⟨trivial, by norm_num, by norm_num⟩, ht.symm⟩⟩),
        fun t ht => hy (mem_iUnion.mpr ⟨i, ⟨(t, -1/2), ⟨trivial, by norm_num, by norm_num⟩, ht.symm⟩⟩)⟩
    have hR : rmapK_S12 F (kpt_S12 F hyK) = y.1 :=
      rmap_eq_val_S12 (x := kpt_S12 F hyK) (fun i h => hy (mem_iUnion.mpr ⟨i, h⟩))
    exact congrArg Subtype.val (interiorEquiv_symm_val_S12 F y (kpt_S12 F hyK) hint hR)

theorem contMDiff_interiorSymm_S12 :
    ContMDiff (𝓡 3) (cutCarrier_C2a F).model ∞ (interiorEquiv_S12 F).symm := by
  refine (ContMDiff.subtypeVal_comp_iff (I := 𝓡 3) (I' := (cutCarrier_C2a F).model)
    (cutCarrier_C2a F).interior (interiorEquiv_S12 F).symm).mp ?_
  let _ : ChartedSpace (EuclideanHalfSpace 3) ↥(cutSet_C2a F) := (cutAtlas_C2a F).toChartedSpace
  have h := (cutAtlas_C2a F).contMDiff_iff_subtype_val (J := 𝓡 3)
    (f := fun z : interiorImage_S12 F => (((interiorEquiv_S12 F).symm z).1 : ↥(cutSet_C2a F)))
  exact h.mpr (contMDiff_interiorSymm_val_S12 F)

/-- **The interior diffeomorphism**: `R` is a diffeomorphism from the interior of the cut
carrier onto the complement of the cut tori. -/
def interiorDiffeomorph_S12 : (cutCarrier_C2a F).interior ≃ₘ⟮(cutCarrier_C2a F).model, 𝓡 3⟯
    interiorImage_S12 F where
  toEquiv := interiorEquiv_S12 F
  contMDiff_toFun :=
    (ContMDiff.subtypeVal_comp_iff (I := (cutCarrier_C2a F).model) (I' := 𝓡 3)
      (interiorImage_S12 F) (interiorEquiv_S12 F)).mp
      ((contMDiff_rmapK_S12 F).comp contMDiff_subtype_val)
  contMDiff_invFun := contMDiff_interiorSymm_S12 F

end GC.LongTime.Ch12
