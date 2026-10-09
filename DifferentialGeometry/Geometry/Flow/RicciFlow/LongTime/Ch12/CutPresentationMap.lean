import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutPresentationCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutPresentationOrient

set_option autoImplicit false
noncomputable section
open Set Function Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

/-- `ρ` as a diffeomorphism of the line. -/
def rhoDiffeo_S12 : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toEquiv := ⟨rho_S12, psi_S12, psi_rho_S12, rho_psi_S12⟩
  contMDiff_toFun := contDiff_rho_S12.contMDiff
  contMDiff_invFun := contDiff_psi_S12.contMDiff

/-- `s ↦ -ρ(-s)` as a diffeomorphism of the line. -/
def rhoNegDiffeo_S12 : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toEquiv := ⟨fun s => -rho_S12 (-s), fun s => -psi_S12 (-s),
    fun s => by simp [psi_rho_S12], fun s => by simp [rho_psi_S12]⟩
  contMDiff_toFun := (contDiff_id.neg.comp (contDiff_rho_S12.comp contDiff_id.neg)).contMDiff
  contMDiff_invFun := (contDiff_id.neg.comp (contDiff_psi_S12.comp contDiff_id.neg)).contMDiff

variable {M : ConnectedClosedOrientedManifold.{u} 3} (F : CollaredTorusFamily_C2a M.Carrier)

/-- `(t, s) ↦ (t, ρ s)`. -/
def phiPlus_S12 : Diffeomorph signedCollarModel signedCollarModel (Torus × ℝ) (Torus × ℝ) ∞ :=
  (Diffeomorph.refl torusModel Torus ∞).prodCongr rhoDiffeo_S12

/-- `(t, s) ↦ (t, -ρ(-s))`. -/
def phiMinus_S12 : Diffeomorph signedCollarModel signedCollarModel (Torus × ℝ) (Torus × ℝ) ∞ :=
  (Diffeomorph.refl torusModel Torus ∞).prodCongr rhoNegDiffeo_S12

/-- The local stretch of `M` along the `i`-th collar on the positive side:
`σ_i (t, s) ↦ σ_i (t, ρ s)`. -/
def gPlus_S12 (i : Fin F.count) : PartialDiffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞ :=
  ((F.collar i).symm.trans phiPlus_S12.toPartialDiffeomorph).trans (F.collar i)

/-- The local stretch on the negative side: `σ_i (t, s) ↦ σ_i (t, -ρ(-s))`. -/
def gMinus_S12 (i : Fin F.count) : PartialDiffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞ :=
  ((F.collar i).symm.trans phiMinus_S12.toPartialDiffeomorph).trans (F.collar i)

variable {F}

theorem collar_symm_apply_S12 (i : Fin F.count) {q : Torus × ℝ} (hq : q ∈ signedCollarSource) :
    (F.collar i).symm (F.collar i q) = q :=
  (F.collar i).left_inv (by rw [F.source_eq]; exact hq)

theorem collar_mem_target_S12 (i : Fin F.count) {q : Torus × ℝ} (hq : q ∈ signedCollarSource) :
    F.collar i q ∈ (F.collar i).target :=
  (F.collar i).map_source (by rw [F.source_eq]; exact hq)

theorem mem_source_gPlus_S12 (i : Fin F.count) {q : Torus × ℝ} (hq : q ∈ signedCollarSource)
    (h : -1 < rho_S12 q.2) (h' : rho_S12 q.2 < 1) :
    F.collar i q ∈ (gPlus_S12 F i).source := by
  refine ⟨⟨collar_mem_target_S12 i hq, trivial⟩, ?_⟩
  change phiPlus_S12 ((F.collar i).symm (F.collar i q)) ∈ (F.collar i).source
  rw [collar_symm_apply_S12 i hq, F.source_eq]
  exact ⟨h, h'⟩

theorem gPlus_apply_S12 (i : Fin F.count) {q : Torus × ℝ} (hq : q ∈ signedCollarSource) :
    gPlus_S12 F i (F.collar i q) = F.collar i (q.1, rho_S12 q.2) := by
  change F.collar i (phiPlus_S12 ((F.collar i).symm (F.collar i q))) = _
  rw [collar_symm_apply_S12 i hq]; rfl

theorem mem_source_gMinus_S12 (i : Fin F.count) {q : Torus × ℝ} (hq : q ∈ signedCollarSource)
    (h : -1 < -rho_S12 (-q.2)) (h' : -rho_S12 (-q.2) < 1) :
    F.collar i q ∈ (gMinus_S12 F i).source := by
  refine ⟨⟨collar_mem_target_S12 i hq, trivial⟩, ?_⟩
  change phiMinus_S12 ((F.collar i).symm (F.collar i q)) ∈ (F.collar i).source
  rw [collar_symm_apply_S12 i hq, F.source_eq]
  exact ⟨h, h'⟩

theorem gMinus_apply_S12 (i : Fin F.count) {q : Torus × ℝ} (hq : q ∈ signedCollarSource) :
    gMinus_S12 F i (F.collar i q) = F.collar i (q.1, -rho_S12 (-q.2)) := by
  change F.collar i (phiMinus_S12 ((F.collar i).symm (F.collar i q))) = _
  rw [collar_symm_apply_S12 i hq]; rfl

/-- Odd extension of `ρ`. -/
def rhoHat_S12 (s : ℝ) : ℝ := if 0 ≤ s then rho_S12 s else -rho_S12 (-s)

theorem rhoHat_of_nonneg_S12 {s : ℝ} (hs : 0 ≤ s) : rhoHat_S12 s = rho_S12 s := by
  unfold rhoHat_S12; simp only [hs, ↓reduceIte]

theorem rhoHat_of_neg_S12 {s : ℝ} (hs : s < 0) : rhoHat_S12 s = -rho_S12 (-s) := by
  unfold rhoHat_S12; simp only [not_le.mpr hs, ↓reduceIte]

theorem rhoHat_of_abs_ge_S12 {s : ℝ} (hs : 7/8 ≤ |s|) : rhoHat_S12 s = s := by
  rcases le_or_gt 0 s with h | h
  · rw [rhoHat_of_nonneg_S12 h, rho_of_ge_S12 (by rwa [abs_of_nonneg h] at hs)]
  · rw [rhoHat_of_neg_S12 h, rho_of_ge_S12 (by rw [abs_of_neg h] at hs; exact hs)]; ring

open Classical in
/-- **The stretch map** `R : K → M`: `σ_i(t, s) ↦ σ_i(t, ±ρ|s|)` on the collars, the inclusion
elsewhere. -/
def rmap_S12 (x : ↥(cutSet_C2a F)) : M.Carrier :=
  if h : ∃ i, x.1 ∈ (F.collar i).target then
    F.collar h.choose (((F.collar h.choose).symm x.1).1,
      rhoHat_S12 ((F.collar h.choose).symm x.1).2)
  else x.1

theorem rmap_of_mem_S12 {x : ↥(cutSet_C2a F)} (i : Fin F.count)
    (hx : x.1 ∈ (F.collar i).target) :
    rmap_S12 x = F.collar i (((F.collar i).symm x.1).1, rhoHat_S12 ((F.collar i).symm x.1).2) := by
  have h : ∃ i, x.1 ∈ (F.collar i).target := ⟨i, hx⟩
  unfold rmap_S12
  simp only [h, ↓reduceDIte]
  have : h.choose = i := by
    by_contra hne
    exact (Set.disjoint_left.mp (F.disjoint hne)) h.choose_spec hx
  rw [this]

theorem rmap_of_not_mem_S12 {x : ↥(cutSet_C2a F)} (hx : ∀ i, x.1 ∉ (F.collar i).target) :
    rmap_S12 x = x.1 := by
  unfold rmap_S12
  have hneg : ¬ ∃ i, x.1 ∈ (F.collar i).target := by push Not; exact hx
  simp only [hneg, ↓reduceDIte]

theorem rmap_collar_S12 {x : ↥(cutSet_C2a F)} (i : Fin F.count) {q : Torus × ℝ}
    (hq : q ∈ signedCollarSource) (hx : x.1 = F.collar i q) :
    rmap_S12 x = F.collar i (q.1, rhoHat_S12 q.2) := by
  have ht : x.1 ∈ (F.collar i).target := by rw [hx]; exact collar_mem_target_S12 i hq
  rw [rmap_of_mem_S12 i ht, hx, collar_symm_apply_S12 i hq]

theorem rmap_eq_val_S12 {x : ↥(cutSet_C2a F)}
    (hx : ∀ i, x.1 ∉ F.collar i '' (univ ×ˢ Icc (-7/8 : ℝ) (7/8))) : rmap_S12 x = x.1 := by
  by_cases h : ∃ i, x.1 ∈ (F.collar i).target
  · obtain ⟨i, hi⟩ := h
    have hq : (F.collar i).symm x.1 ∈ signedCollarSource := by
      have := (F.collar i).map_target hi
      rwa [F.source_eq] at this
    have hxq : F.collar i ((F.collar i).symm x.1) = x.1 := (F.collar i).right_inv hi
    rw [rmap_collar_S12 i hq hxq.symm]
    have hge : 7/8 ≤ |((F.collar i).symm x.1).2| := by
      by_contra hlt
      push Not at hlt
      apply hx i
      refine ⟨(F.collar i).symm x.1, ⟨trivial, ?_, ?_⟩, hxq⟩ <;> [linarith [(abs_lt.mp hlt).1]; linarith [(abs_lt.mp hlt).2]]
    rw [rhoHat_of_abs_ge_S12 hge]
    conv_rhs => rw [← hxq]
  · push Not at h
    exact rmap_of_not_mem_S12 h

theorem rmap_eq_gPlus_S12 {x : ↥(cutSet_C2a F)} (i : Fin F.count) {q : Torus × ℝ}
    (hq : q ∈ signedCollarSource) (hq0 : 0 < q.2) (hx : x.1 = F.collar i q) :
    rmap_S12 x = gPlus_S12 F i x.1 := by
  rw [rmap_collar_S12 i hq hx, hx, gPlus_apply_S12 i hq, rhoHat_of_nonneg_S12 hq0.le]

theorem rmap_eq_gMinus_S12 {x : ↥(cutSet_C2a F)} (i : Fin F.count) {q : Torus × ℝ}
    (hq : q ∈ signedCollarSource) (hq0 : q.2 < 0) (hx : x.1 = F.collar i q) :
    rmap_S12 x = gMinus_S12 F i x.1 := by
  rw [rmap_collar_S12 i hq hx, hx, gMinus_apply_S12 i hq, rhoHat_of_neg_S12 hq0]

section Smooth

/-- The closed slab `σ_i(T² × [-7/8, 7/8])`. -/
def slab_S12 (F : CollaredTorusFamily_C2a M.Carrier) (i : Fin F.count) : Set M.Carrier :=
  F.collar i '' (univ ×ˢ Icc (-7/8 : ℝ) (7/8))

theorem Icc_subset_source_S12 {a b : ℝ} (ha : -1 < a) (hb : b < 1) :
    (univ ×ˢ Icc a b : Set (Torus × ℝ)) ⊆ signedCollarSource := by
  rintro ⟨t, s⟩ ⟨-, h1, h2⟩
  exact ⟨by linarith [h1], by linarith [h2]⟩

theorem Ioo_subset_source_S12 {a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1) :
    (univ ×ˢ Ioo a b : Set (Torus × ℝ)) ⊆ signedCollarSource := by
  rintro ⟨t, s⟩ ⟨-, h1, h2⟩
  exact ⟨by linarith [h1], by linarith [h2]⟩

theorem isClosed_slab_S12 (i : Fin F.count) : IsClosed (slab_S12 F i) := by
  have hc : IsCompact (univ ×ˢ Icc (-7/8 : ℝ) (7/8) : Set (Torus × ℝ)) :=
    isCompact_univ.prod isCompact_Icc
  refine (hc.image_of_continuousOn ?_).isClosed
  exact (F.collar i).toOpenPartialHomeomorph.continuousOn.mono
    (by change _ ⊆ (F.collar i).source; rw [F.source_eq]
        exact Icc_subset_source_S12 (by norm_num) (by norm_num))

theorem isOpen_collarImage_S12 (i : Fin F.count) {a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1) :
    IsOpen (F.collar i '' (univ ×ˢ Ioo a b)) := by
  refine (F.collar i).toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_univ.prod isOpen_Ioo) ?_
  change _ ⊆ (F.collar i).source
  rw [F.source_eq]; exact Ioo_subset_source_S12 ha hb

theorem rho_gt_neg_one_S12 {s : ℝ} (hs : 0 ≤ s) : -1 < rho_S12 s := by
  have := strictMono_rho_S12.monotone hs
  rw [rho_zero_S12] at this; linarith

theorem neg_rho_neg_lt_one_S12 {s : ℝ} (hs : s ≤ 0) : -rho_S12 (-s) < 1 := by
  have := rho_gt_neg_one_S12 (show 0 ≤ -s by linarith)
  linarith

theorem neg_rho_neg_gt_S12 {s : ℝ} (hs : -1 < s) : -1 < -rho_S12 (-s) := by
  have := rho_lt_one_S12 (show -s < 1 by linarith)
  linarith

variable (F)

theorem half_le_abs_of_mem_cut_S12 {x : ↥(cutSet_C2a F)} (i : Fin F.count) {q : Torus × ℝ}
    (hq : q ∈ signedCollarSource) (hx : x.1 = F.collar i q) : 1/2 ≤ |q.2| := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  have : x.1 ∈ tubeOpen_C2a F i := by
    rw [hx, collar_mem_tubeOpen_iff_C2a i hq]; exact ⟨by linarith, by linarith⟩
  exact (mem_compl_iff _ _).mp x.2 (mem_iUnion.mpr ⟨i, this⟩)

theorem contMDiff_cutIncl_S12 :
    ContMDiff (cutCarrier_C2a F).model (𝓡 3) ∞ (cutIncl_C2a F) := by
  let _ : ChartedSpace (EuclideanHalfSpace 3) ↥(cutSet_C2a F) := (cutAtlas_C2a F).toChartedSpace
  exact (cutAtlas_C2a F).contMDiff_subtype_val

/-- `rmap_S12` on the cut carrier. -/
def rmapK_S12 : (cutCarrier_C2a F).Carrier → M.Carrier := rmap_S12

theorem contMDiff_rmapK_S12 :
    ContMDiff (cutCarrier_C2a F).model (𝓡 3) ∞ (rmapK_S12 F) := by
  have hval := contMDiff_cutIncl_S12 F
  refine contMDiff_of_locally_contMDiffOn fun x => ?_
  by_cases hs : ∃ i, cutIncl_C2a F x ∈ slab_S12 F i
  · obtain ⟨i, q, ⟨-, hq1, hq2⟩, hxq⟩ := hs
    have hqs : q ∈ signedCollarSource := ⟨by linarith [hq1], by linarith [hq2]⟩
    have hge := half_le_abs_of_mem_cut_S12 F (x := x) i hqs hxq.symm
    rcases lt_or_gt_of_ne (show q.2 ≠ 0 by
      intro h0; rw [h0, abs_zero] at hge; linarith) with hneg | hpos
    · refine ⟨cutIncl_C2a F ⁻¹' (F.collar i '' (univ ×ˢ Ioo (-1 : ℝ) 0)), ?_,
        ⟨q, ⟨trivial, hqs.1, hneg⟩, hxq⟩, ?_⟩
      · exact (isOpen_collarImage_S12 i le_rfl (by norm_num)).preimage hval.continuous
      · have hG : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (gMinus_S12 F i) (gMinus_S12 F i).source :=
          (gMinus_S12 F i).contMDiffOn
        refine (hG.comp hval.contMDiffOn ?_).congr ?_
        · rintro y ⟨q', ⟨-, h1, h2⟩, hyq⟩
          have hq' : q' ∈ signedCollarSource := ⟨h1, by linarith⟩
          change cutIncl_C2a F y ∈ (gMinus_S12 F i).source
          rw [← hyq]
          exact mem_source_gMinus_S12 i hq' (neg_rho_neg_gt_S12 h1) (neg_rho_neg_lt_one_S12 h2.le)
        · rintro y ⟨q', ⟨-, h1, h2⟩, hyq⟩
          have hq' : q' ∈ signedCollarSource := ⟨h1, by linarith⟩
          exact rmap_eq_gMinus_S12 (x := y) i hq' h2 hyq.symm
    · refine ⟨cutIncl_C2a F ⁻¹' (F.collar i '' (univ ×ˢ Ioo (0 : ℝ) 1)), ?_,
        ⟨q, ⟨trivial, hpos, hqs.2⟩, hxq⟩, ?_⟩
      · exact (isOpen_collarImage_S12 i (by norm_num) le_rfl).preimage hval.continuous
      · have hG : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (gPlus_S12 F i) (gPlus_S12 F i).source :=
          (gPlus_S12 F i).contMDiffOn
        refine (hG.comp hval.contMDiffOn ?_).congr ?_
        · rintro y ⟨q', ⟨-, h1, h2⟩, hyq⟩
          have hq' : q' ∈ signedCollarSource := ⟨by linarith, h2⟩
          change cutIncl_C2a F y ∈ (gPlus_S12 F i).source
          rw [← hyq]
          exact mem_source_gPlus_S12 i hq' (rho_gt_neg_one_S12 h1.le) (rho_lt_one_S12 h2)
        · rintro y ⟨q', ⟨-, h1, h2⟩, hyq⟩
          have hq' : q' ∈ signedCollarSource := ⟨by linarith, h2⟩
          exact rmap_eq_gPlus_S12 (x := y) i hq' h1 hyq.symm
  · refine ⟨cutIncl_C2a F ⁻¹' (⋃ i, slab_S12 F i)ᶜ, ?_, ?_, ?_⟩
    · exact (isClosed_iUnion_of_finite isClosed_slab_S12).isOpen_compl.preimage hval.continuous
    · intro h; exact hs (mem_iUnion.mp h)
    · refine hval.contMDiffOn.congr ?_
      intro y hy
      exact rmap_eq_val_S12 (x := y) (fun i h => hy (mem_iUnion.mpr ⟨i, h⟩))

end Smooth

end GC.LongTime.Ch12
