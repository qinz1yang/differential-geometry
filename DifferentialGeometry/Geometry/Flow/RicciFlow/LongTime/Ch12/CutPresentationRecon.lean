import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutPresentationPairing

set_option autoImplicit false
noncomputable section
open Set Function Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

section RhoHat

theorem rhoHat_inj_S12 {s s' : ℝ} (hs : 1/2 ≤ |s|) (hs' : 1/2 ≤ |s'|)
    (h : rhoHat_S12 s = rhoHat_S12 s') : s = s' ∨ (s = 1/2 ∧ s' = -1/2) ∨ (s = -1/2 ∧ s' = 1/2) := by
  have hinj : ∀ a b : ℝ, rho_S12 a = rho_S12 b → a = b := fun a b hab =>
    strictMono_rho_S12.injective hab
  rcases le_or_gt 0 s with h1 | h1 <;> rcases le_or_gt 0 s' with h2 | h2
  · rw [rhoHat_of_nonneg_S12 h1, rhoHat_of_nonneg_S12 h2] at h
    exact Or.inl (hinj _ _ h)
  · rw [rhoHat_of_nonneg_S12 h1, rhoHat_of_neg_S12 h2] at h
    have a1 : 1/2 ≤ s := by rwa [abs_of_nonneg h1] at hs
    have a2 : 1/2 ≤ -s' := by rw [abs_of_neg h2] at hs'; exact hs'
    have b1 := rho_nonneg_S12 a1
    have b2 := rho_nonneg_S12 a2
    have c1 : rho_S12 s = 0 := by linarith
    have c2 : rho_S12 (-s') = 0 := by linarith
    have d1 := hinj _ _ (c1.trans rho_half_S12.symm)
    have d2 := hinj _ _ (c2.trans rho_half_S12.symm)
    exact Or.inr (Or.inl ⟨d1, by linarith⟩)
  · rw [rhoHat_of_neg_S12 h1, rhoHat_of_nonneg_S12 h2] at h
    have a1 : 1/2 ≤ -s := by rw [abs_of_neg h1] at hs; exact hs
    have a2 : 1/2 ≤ s' := by rwa [abs_of_nonneg h2] at hs'
    have b1 := rho_nonneg_S12 a1
    have b2 := rho_nonneg_S12 a2
    have c1 : rho_S12 (-s) = 0 := by linarith
    have c2 : rho_S12 s' = 0 := by linarith
    have d1 := hinj _ _ (c1.trans rho_half_S12.symm)
    have d2 := hinj _ _ (c2.trans rho_half_S12.symm)
    exact Or.inr (Or.inr ⟨by linarith, d2⟩)
  · rw [rhoHat_of_neg_S12 h1, rhoHat_of_neg_S12 h2] at h
    have := hinj _ _ (neg_injective h)
    exact Or.inl (by linarith)

theorem rhoHat_mem_Ioo_S12 {s : ℝ} (hs : 1/2 ≤ |s|) (hs1 : |s| < 1) :
    -1 < rhoHat_S12 s ∧ rhoHat_S12 s < 1 := by
  rcases le_or_gt 0 s with h1 | h1
  · rw [rhoHat_of_nonneg_S12 h1]
    have : s < 1 := by rwa [abs_of_nonneg h1] at hs1
    exact ⟨rho_gt_neg_one_S12 h1, rho_lt_one_S12 this⟩
  · rw [rhoHat_of_neg_S12 h1]
    have : -s < 1 := by rwa [abs_of_neg h1] at hs1
    have a1 : 1/2 ≤ -s := by rw [abs_of_neg h1] at hs; exact hs
    have := rho_lt_one_S12 this
    have := rho_nonneg_S12 a1
    constructor <;> linarith [rho_lt_one_S12 (show -s < 1 by linarith)]

end RhoHat

variable {M : ConnectedClosedOrientedManifold.{u} 3} (F : CollaredTorusFamily_C2a M.Carrier)

theorem rmapK_sideTorus_left_S12 (i : Fin F.count) (t : Torus) :
    rmapK_S12 F (sideTorus_C2a F i hL_C2a t) = F.collar i (t, 0) := by
  have hq : (t, sideParam_C2a (-1) 0) ∈ signedCollarSource :=
    sideParam_mem_source_C2a hL_C2a t le_rfl zero_lt_one
  change rmap_S12 (sideTorus_C2a F i hL_C2a t) = _
  rw [rmap_collar_S12 i hq rfl]
  have : sideParam_C2a (-1) 0 = -(1/2) := by simp [sideParam_C2a]
  change F.collar i (t, rhoHat_S12 (sideParam_C2a (-1) 0)) = _
  rw [this, rhoHat_of_neg_S12 (by norm_num), neg_neg,
    show (1/2 : ℝ) = 1/2 from rfl, rho_half_S12]
  simp

theorem rmapK_sideTorus_right_S12 (i : Fin F.count) (t : Torus) :
    rmapK_S12 F (sideTorus_C2a F i hR_C2a t) = F.collar i (t, 0) := by
  have hq : (t, sideParam_C2a 1 0) ∈ signedCollarSource :=
    sideParam_mem_source_C2a hR_C2a t le_rfl zero_lt_one
  change rmap_S12 (sideTorus_C2a F i hR_C2a t) = _
  rw [rmap_collar_S12 i hq rfl]
  have : sideParam_C2a 1 0 = 1/2 := by simp [sideParam_C2a]
  change F.collar i (t, rhoHat_S12 (sideParam_C2a 1 0)) = _
  rw [this, rhoHat_of_nonneg_S12 (by norm_num), rho_half_S12]

theorem sideTorus_val_left_S12 (i : Fin F.count) (t : Torus) :
    (sideTorus_C2a F i hL_C2a t).1 = F.collar i (t, -1/2) := by
  change F.collar i (t, sideParam_C2a (-1) 0) = _
  congr 2; simp [sideParam_C2a]; norm_num

theorem sideTorus_val_right_S12 (i : Fin F.count) (t : Torus) :
    (sideTorus_C2a F i hR_C2a t).1 = F.collar i (t, 1/2) := by
  change F.collar i (t, sideParam_C2a 1 0) = _
  congr 2; simp [sideParam_C2a]

theorem rmapK_cases_S12 {a b : (cutCarrier_C2a F).Carrier} (h : rmapK_S12 F a = rmapK_S12 F b) :
    a = b ∨ (∃ i t, a = sideTorus_C2a F i hL_C2a t ∧ b = sideTorus_C2a F i hR_C2a t) ∨
      (∃ i t, a = sideTorus_C2a F i hR_C2a t ∧ b = sideTorus_C2a F i hL_C2a t) := by
  have hparam : ∀ (x : (cutCarrier_C2a F).Carrier) (i : Fin F.count), x.1 ∈ (F.collar i).target →
      ∃ q : Torus × ℝ, q ∈ signedCollarSource ∧ x.1 = F.collar i q ∧ 1/2 ≤ |q.2| ∧
        rmapK_S12 F x = F.collar i (q.1, rhoHat_S12 q.2) := by
    intro x i hx
    have hq : (F.collar i).symm x.1 ∈ signedCollarSource := by
      have := (F.collar i).map_target hx; rwa [F.source_eq] at this
    have hxq : x.1 = F.collar i ((F.collar i).symm x.1) := ((F.collar i).right_inv hx).symm
    exact ⟨_, hq, hxq, half_le_abs_of_mem_cut_S12 F i hq hxq, rmap_collar_S12 i hq hxq⟩
  have hnot : ∀ (x : (cutCarrier_C2a F).Carrier), (∀ i, x.1 ∉ (F.collar i).target) →
      rmapK_S12 F x = x.1 := fun x hx => rmap_of_not_mem_S12 hx
  have hmem : ∀ (i : Fin F.count) {q : Torus × ℝ}, q ∈ signedCollarSource → 1/2 ≤ |q.2| →
      F.collar i (q.1, rhoHat_S12 q.2) ∈ (F.collar i).target := by
    intro i q hq hq2
    have := rhoHat_mem_Ioo_S12 hq2 (abs_lt.mpr ⟨hq.1, hq.2⟩)
    exact collar_mem_target_S12 i (q := (q.1, rhoHat_S12 q.2)) ⟨this.1, this.2⟩
  by_cases ha : ∃ i, a.1 ∈ (F.collar i).target <;> by_cases hb : ∃ j, b.1 ∈ (F.collar j).target
  · obtain ⟨i, hi⟩ := ha
    obtain ⟨j, hj⟩ := hb
    obtain ⟨q, hq, hxq, hq2, hRq⟩ := hparam a i hi
    obtain ⟨q', hq', hxq', hq2', hRq'⟩ := hparam b j hj
    have hij : i = j := by
      by_contra hne
      have h1 : rmapK_S12 F a ∈ (F.collar i).target := by rw [hRq]; exact hmem i hq hq2
      have h2 : rmapK_S12 F a ∈ (F.collar j).target := by rw [h, hRq']; exact hmem j hq' hq2'
      exact (Set.disjoint_left.mp (F.disjoint hne)) h1 h2
    subst hij
    rw [hRq, hRq'] at h
    have hs1 := rhoHat_mem_Ioo_S12 hq2 (abs_lt.mpr ⟨hq.1, hq.2⟩)
    have hs2 := rhoHat_mem_Ioo_S12 hq2' (abs_lt.mpr ⟨hq'.1, hq'.2⟩)
    have hinj := (F.collar i).toOpenPartialHomeomorph.injOn
      (by change _ ∈ (F.collar i).source; rw [F.source_eq]; exact ⟨hs1.1, hs1.2⟩)
      (by change _ ∈ (F.collar i).source; rw [F.source_eq]; exact ⟨hs2.1, hs2.2⟩) h
    have e1 : q.1 = q'.1 := (Prod.ext_iff.mp hinj).1
    have e2 : rhoHat_S12 q.2 = rhoHat_S12 q'.2 := (Prod.ext_iff.mp hinj).2
    rcases rhoHat_inj_S12 hq2 hq2' e2 with h3 | ⟨h3, h4⟩ | ⟨h3, h4⟩
    · left
      apply Subtype.ext
      rw [hxq, hxq']
      congr 1
      exact Prod.ext e1 h3
    · right; right
      refine ⟨i, q.1, Subtype.ext ?_, Subtype.ext ?_⟩
      · rw [hxq, sideTorus_val_right_S12]; congr 1; exact Prod.ext rfl h3
      · rw [hxq', sideTorus_val_left_S12]; congr 1; exact Prod.ext e1.symm h4
    · right; left
      refine ⟨i, q.1, Subtype.ext ?_, Subtype.ext ?_⟩
      · rw [hxq, sideTorus_val_left_S12]; congr 1; exact Prod.ext rfl h3
      · rw [hxq', sideTorus_val_right_S12]; congr 1; exact Prod.ext e1.symm h4
  · obtain ⟨i, hi⟩ := ha
    obtain ⟨q, hq, hxq, hq2, hRq⟩ := hparam a i hi
    push Not at hb
    exfalso
    have h1 : rmapK_S12 F a ∈ (F.collar i).target := by rw [hRq]; exact hmem i hq hq2
    rw [h, hnot b hb] at h1
    exact hb i h1
  · obtain ⟨j, hj⟩ := hb
    obtain ⟨q', hq', hxq', hq2', hRq'⟩ := hparam b j hj
    push Not at ha
    exfalso
    have h1 : rmapK_S12 F b ∈ (F.collar j).target := by rw [hRq']; exact hmem j hq' hq2'
    rw [← h, hnot a ha] at h1
    exact ha j h1
  · push Not at ha hb
    left
    apply Subtype.ext
    rw [← hnot a ha, ← hnot b hb]; exact h

theorem rmapK_surjective_S12 : Surjective (rmapK_S12 F) := by
  intro y
  by_cases hy : ∃ i, y ∈ (F.collar i).target
  · obtain ⟨i, hi⟩ := hy
    set q := (F.collar i).symm y with hqdef
    have hq : q ∈ signedCollarSource := by
      have := (F.collar i).map_target hi; rwa [F.source_eq] at this
    have hyq : y = F.collar i q := ((F.collar i).right_inv hi).symm
    rcases le_or_gt 0 q.2 with h0 | h0
    · have hp : (q.1, psi_S12 q.2) ∈ signedCollarSource :=
        ⟨by change -1 < psi_S12 q.2; linarith [half_le_psi_S12 h0],
         by change psi_S12 q.2 < 1; exact psi_lt_one_S12 hq.2⟩
      have hK : F.collar i (q.1, psi_S12 q.2) ∈ cutSet_C2a F :=
        collar_mem_cutSet_C2a i hp (by
          change 1/2 ≤ |psi_S12 q.2|
          rw [abs_of_nonneg (by linarith [half_le_psi_S12 h0])]; exact half_le_psi_S12 h0)
      refine ⟨⟨_, hK⟩, ?_⟩
      change rmap_S12 ⟨_, hK⟩ = y
      rw [rmap_collar_S12 i hp rfl]
      change F.collar i (q.1, rhoHat_S12 (psi_S12 q.2)) = y
      rw [rhoHat_of_nonneg_S12 (by linarith [half_le_psi_S12 h0]), rho_psi_S12, hyq]
    · have h1 : 0 ≤ -q.2 := by linarith
      have hp : (q.1, -psi_S12 (-q.2)) ∈ signedCollarSource :=
        ⟨by change -1 < -psi_S12 (-q.2); linarith [psi_lt_one_S12 (show -q.2 < 1 by linarith [hq.1])],
         by change -psi_S12 (-q.2) < 1; linarith [half_le_psi_S12 h1]⟩
      have hK : F.collar i (q.1, -psi_S12 (-q.2)) ∈ cutSet_C2a F :=
        collar_mem_cutSet_C2a i hp (by
          change 1/2 ≤ |-psi_S12 (-q.2)|
          rw [abs_neg, abs_of_nonneg (by linarith [half_le_psi_S12 h1])]; exact half_le_psi_S12 h1)
      refine ⟨⟨_, hK⟩, ?_⟩
      change rmap_S12 ⟨_, hK⟩ = y
      rw [rmap_collar_S12 i hp rfl]
      change F.collar i (q.1, rhoHat_S12 (-psi_S12 (-q.2))) = y
      rw [rhoHat_of_neg_S12 (by linarith [half_le_psi_S12 h1]), neg_neg, rho_psi_S12, neg_neg, hyq]
  · push Not at hy
    have hK : y ∈ cutSet_C2a F := by
      intro h
      obtain ⟨i, hi⟩ := mem_iUnion.mp h
      obtain ⟨q, ⟨-, hq⟩, rfl⟩ := hi
      exact hy i ((F.collar i).map_source (by rw [F.source_eq]; exact Ioo_subset_collar_C2a ⟨trivial, hq⟩))
    refine ⟨⟨y, hK⟩, ?_⟩
    exact rmap_of_not_mem_S12 (x := ⟨y, hK⟩) hy

theorem quotient_left_right_S12 (i : Fin F.count) (t : Torus) :
    (cutPairing_S12 F).quotientMap (sideTorus_C2a F i hL_C2a t) =
      (cutPairing_S12 F).quotientMap (sideTorus_C2a F i hR_C2a t) :=
  (cutGluing_C2a F).matched_sides_equal i t

theorem rmapK_rel_S12 {a b : (cutCarrier_C2a F).Carrier}
    (h : (cutPairing_S12 F).gluing.rel a b) : rmapK_S12 F a = rmapK_S12 F b := by
  rcases h with rfl | ⟨i, hx, rfl⟩
  · rfl
  · rcases hx with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · have hf : (cutPairing_S12 F).gluing.flip i (sideTorus_C2a F i hL_C2a t) =
          sideTorus_C2a F i hR_C2a t := by
        have h1 := (cutPairing_S12 F).gluing.flip_of_mem_left (i := i)
          (x := sideTorus_C2a F i hL_C2a t) ⟨t, rfl⟩
        rw [h1]
        exact congrArg Subtype.val ((cutPairing_S12 F).matching_eq i t)
      rw [hf]
      exact (rmapK_sideTorus_left_S12 F i t).trans (rmapK_sideTorus_right_S12 F i t).symm
    · have hf : (cutPairing_S12 F).gluing.flip i (sideTorus_C2a F i hR_C2a t) =
          sideTorus_C2a F i hL_C2a t := by
        have h1 := (cutPairing_S12 F).gluing.flip_of_mem_right (i := i)
          (x := sideTorus_C2a F i hR_C2a t) ⟨t, rfl⟩
        rw [h1]
        have h2 := (cutPairing_S12 F).matching_eq i t
        have h3 : ((cutPairing_S12 F).gluing.attaching i).symm
            ((cutPairing_S12 F).rightParam i ((cutPairing_S12 F).matching i t)) =
              (cutPairing_S12 F).leftParam i t := by
          rw [← h2, Homeomorph.symm_apply_apply]
        exact congrArg Subtype.val h3
      rw [hf]
      exact (rmapK_sideTorus_right_S12 F i t).trans (rmapK_sideTorus_left_S12 F i t).symm

/-- The map from the glued space to `M`, `⟦x⟧ ↦ R x`. -/
def reconMap_S12 : (cutPairing_S12 F).QuotientSpace → M.Carrier :=
  Quotient.lift (rmapK_S12 F) (fun _ _ h => rmapK_rel_S12 F h)

theorem reconMap_mk_S12 (x : (cutCarrier_C2a F).Carrier) :
    reconMap_S12 F ((cutPairing_S12 F).quotientMap x) = rmapK_S12 F x := rfl

theorem reconMap_injective_S12 : Injective (reconMap_S12 F) := by
  intro p q hpq
  induction p using Quotient.inductionOn with
  | h a =>
  induction q using Quotient.inductionOn with
  | h b =>
  rcases rmapK_cases_S12 F hpq with rfl | ⟨i, t, rfl, rfl⟩ | ⟨i, t, rfl, rfl⟩
  · rfl
  · exact quotient_left_right_S12 F i t
  · exact (quotient_left_right_S12 F i t).symm

theorem reconMap_surjective_S12 : Surjective (reconMap_S12 F) := by
  intro y
  obtain ⟨x, hx⟩ := rmapK_surjective_S12 F y
  exact ⟨(cutPairing_S12 F).quotientMap x, hx⟩

theorem continuous_reconMap_S12 : Continuous (reconMap_S12 F) :=
  Continuous.quotient_lift (contMDiff_rmapK_S12 F).continuous _

/-- **The reconstruction homeomorphism** `(K / gluing) ≃ₜ M`. -/
def cutRecon_S12 : (cutPairing_S12 F).QuotientSpace ≃ₜ M.Carrier :=
  (continuous_reconMap_S12 F).homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (reconMap_S12 F) ⟨reconMap_injective_S12 F, reconMap_surjective_S12 F⟩)

theorem cutRecon_mk_S12 (x : (cutCarrier_C2a F).Carrier) :
    cutRecon_S12 F ((cutPairing_S12 F).quotientMap x) = rmapK_S12 F x := rfl

end GC.LongTime.Ch12
