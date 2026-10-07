/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.Strata

noncomputable section

open Set Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup

namespace DifferentialGeometry.FixedLocusGeometry

open Hyperbolic HyperbolicAction HyperbolicFaithful OrbifoldStrata

variable {n : ℕ}

def locusSpan (σ : Set (HUpper n)) : Submodule ℝ (LorVec n) :=
  Submodule.span ℝ (HUpper.val '' σ)

def locusRank (σ : Set (HUpper n)) : ℕ :=
  Module.finrank ℝ (locusSpan σ)

theorem locusSpan_mono {σ τ : Set (HUpper n)} (h : σ ⊆ τ) :
    locusSpan σ ≤ locusSpan τ :=
  Submodule.span_mono (Set.image_mono h)

theorem val_mem_locusSpan {σ : Set (HUpper n)} {x : HUpper n} (hx : x ∈ σ) :
    x.val ∈ locusSpan σ :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem locusRank_pos {σ : Set (HUpper n)} (hσ : σ.Nonempty) : 0 < locusRank σ := by
  obtain ⟨x, hx⟩ := hσ
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨x.val, val_mem_locusSpan hx⟩, ?_⟩
  intro hzero
  have hval : x.val = 0 := congrArg Subtype.val hzero
  have hfuture := x.future
  rw [hval] at hfuture
  simp only [tc, Pi.zero_apply, lt_self_iff_false] at hfuture

theorem locusRank_le (σ : Set (HUpper n)) : locusRank σ ≤ n + 1 := by
  have h := Submodule.finrank_le (locusSpan σ)
  simpa only [locusRank, LorVec, Module.finrank_pi, Fintype.card_sum,
    Fintype.card_fin] using h

theorem locusRank_image_smul_le (hn : 1 ≤ n) (g : PO n 1) (σ : Set (HUpper n)) :
    locusRank ((fun x : HUpper n => (poMulAction hn).smul g x) '' σ) ≤ locusRank σ := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (LorGrp n)) g
  let L : LorVec n →ₗ[ℝ] LorVec n := Matrix.mulVecLin (matOf A)
  have hspan : locusSpan ((fun x : HUpper n =>
      (poMulAction hn).smul (QuotientGroup.mk' (Subgroup.center (LorGrp n)) A) x) '' σ) ≤
      (locusSpan σ).map L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    have hqL : matOf A *ᵥ q.val ∈ (locusSpan σ).map L :=
      ⟨q.val, val_mem_locusSpan hq, rfl⟩
    change upperize (matOf A *ᵥ q.val) ∈ (locusSpan σ).map L
    unfold upperize
    split_ifs
    · exact hqL
    · exact ((locusSpan σ).map L).neg_mem hqL
  exact (Submodule.finrank_mono hspan).trans (Submodule.finrank_map_le L (locusSpan σ))

theorem locusRank_image_smul (hn : 1 ≤ n) (g : PO n 1) (σ : Set (HUpper n)) :
    locusRank ((fun x : HUpper n => (poMulAction hn).smul g x) '' σ) = locusRank σ := by
  let := poMulAction hn
  apply le_antisymm (locusRank_image_smul_le hn g σ)
  have h := locusRank_image_smul_le hn g⁻¹
    ((fun x : HUpper n => (poMulAction hn).smul g x) '' σ)
  change locusRank ((fun x : HUpper n => g⁻¹ • x) '' ((fun x : HUpper n => g • x) '' σ)) ≤
    locusRank ((fun x : HUpper n => g • x) '' σ) at h
  change locusRank σ ≤ locusRank ((fun x : HUpper n => g • x) '' σ)
  simpa only [image_image, inv_smul_smul, image_id'] using h

theorem eigen_sign_eq_of_fixed (A : LorGrp n) (p q : HUpper n) {c d : ℝ}
    (hc : c = 1 ∨ c = -1) (hd : d = 1 ∨ d = -1)
    (hp : matOf A *ᵥ p.val = c • p.val) (hq : matOf A *ᵥ q.val = d • q.val) :
    c = d := by
  have hpair := lorB_matOf_mulVec A p.val q.val
  rw [hp, hq, lorB_smul_left, lorB_smul_right] at hpair
  have hnonzero : lorB p.val q.val ≠ 0 := by
    have h := HUpper.one_le_neg_lorB p q
    linarith
  have hcd : c * d = 1 := by
    apply mul_right_cancel₀ hnonzero
    calc
      (c * d) * lorB p.val q.val = c * (d * lorB p.val q.val) := mul_assoc _ _ _
      _ = lorB p.val q.val := hpair
      _ = 1 * lorB p.val q.val := (one_mul _).symm
  rcases hc with hc | hc <;> rcases hd with hd | hd <;> nlinarith

theorem mem_fixedLocus_of_val_mem_span (hn : 1 ≤ n) (D : Subgroup (PO n 1))
    (hD : (fixedLocus hn D).Nonempty) {x : HUpper n}
    (hx : x.val ∈ locusSpan (fixedLocus hn D)) :
    x ∈ fixedLocus hn D := by
  let := poMulAction hn
  obtain ⟨p, hp⟩ := hD
  intro γ
  obtain ⟨A, hA⟩ := QuotientGroup.mk'_surjective (Subgroup.center (LorGrp n)) (γ : PO n 1)
  have hfix (q : HUpper n) (hq : q ∈ fixedLocus hn D) : actH A q = q := by
    have h : (γ : PO n 1) • q = q := hq γ
    rw [← hA, po_smul_mk hn A q] at h
    exact h
  obtain ⟨c, hc, hcp⟩ := exists_sign_smul_of_actH_eq (hfix p hp)
  have heigen (q : HUpper n) (hq : q ∈ fixedLocus hn D) :
      matOf A *ᵥ q.val = c • q.val := by
    obtain ⟨d, hd, hdq⟩ := exists_sign_smul_of_actH_eq (hfix q hq)
    rw [hdq, eigen_sign_eq_of_fixed A q p hd hc hdq hcp]
  let L : LorVec n →ₗ[ℝ] LorVec n := Matrix.mulVecLin (matOf A) - c • LinearMap.id
  have hspan : locusSpan (fixedLocus hn D) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨q, hq, rfl⟩
    change matOf A *ᵥ q.val - c • q.val = 0
    rw [heigen q hq, sub_self]
  have hxA : matOf A *ᵥ x.val = c • x.val :=
    sub_eq_zero.mp (show matOf A *ᵥ x.val - c • x.val = 0 from hspan hx)
  change (γ : PO n 1) • x = x
  rw [← hA, po_smul_mk hn A x]
  apply HUpper.ext
  change upperize (matOf A *ᵥ x.val) = x.val
  rw [hxA]
  rcases hc with rfl | rfl
  · rw [one_smul]
    exact ite_eq_left x.future
  · rw [neg_one_smul, upperize_neg x.future.ne']
    exact ite_eq_left x.future

theorem fixedLocus_eq_preimage_span (hn : 1 ≤ n) (D : Subgroup (PO n 1))
    (hD : (fixedLocus hn D).Nonempty) :
    fixedLocus hn D =
      {x : HUpper n | x.val ∈ locusSpan (fixedLocus hn D)} :=
  Set.Subset.antisymm (fun _ hx => val_mem_locusSpan hx)
    (fun _ hx => mem_fixedLocus_of_val_mem_span hn D hD hx)

theorem locusRank_lt_of_fixedLocus_ssubset (hn : 1 ≤ n)
    (D E : Subgroup (PO n 1)) (hD : (fixedLocus hn D).Nonempty)
    (hsub : fixedLocus hn D ⊂ fixedLocus hn E) :
    locusRank (fixedLocus hn D) < locusRank (fixedLocus hn E) := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine (locusSpan_mono hsub.subset).lt_of_ne ?_
  intro heq
  apply hsub.ne
  apply Set.Subset.antisymm hsub.subset
  intro x hx
  apply mem_fixedLocus_of_val_mem_span hn D hD
  rw [heq]
  exact val_mem_locusSpan hx

theorem locusRank_lt_of_incident (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    {σ τ : Set (HUpper n)} (hσ : σ.Nonempty) (hne : σ ≠ τ) {x : HUpper n}
    (hx : x ∈ fixedStratum hn Γ ε σ) (hxt : x ∈ closure (fixedStratum hn Γ ε τ)) :
    locusRank σ < locusRank τ := by
  obtain ⟨y, hy⟩ :=
    (show (closure (fixedStratum hn Γ ε τ)).Nonempty from ⟨x, hxt⟩).of_closure
  have hs : fixedLocus hn (closedSmallSubgroup hn Γ ε x) = σ := hx
  have ht : fixedLocus hn (closedSmallSubgroup hn Γ ε y) = τ := hy
  have h := locusRank_lt_of_fixedLocus_ssubset hn
    (closedSmallSubgroup hn Γ ε x) (closedSmallSubgroup hn Γ ε y)
    (hs.symm ▸ hσ) (by
      rw [hs, ht]
      exact fixedLocus_ssubset_of_incident hn Γ hΓ ε hne hx hxt)
  simpa only [hs, ht] using h

theorem incidence_chain_length_le (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (ε : ℝ)
    (σ : ℕ → Set (HUpper n)) (k : ℕ) (hzero : (σ 0).Nonempty)
    (hstep : ∀ i < k, σ i ≠ σ (i + 1) ∧
      ∃ x : HUpper n, x ∈ fixedStratum hn Γ ε (σ i) ∧
        x ∈ closure (fixedStratum hn Γ ε (σ (i + 1)))) :
    k ≤ n := by
  have hbound : ∀ i ≤ k, (σ i).Nonempty ∧ i + 1 ≤ locusRank (σ i) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨hzero, locusRank_pos hzero⟩
    | succ i ih =>
      intro hi
      obtain ⟨hσ, hrank⟩ := ih (by omega)
      obtain ⟨hne, x, hx, hxt⟩ := hstep i (by omega)
      have hsub := fixedLocus_subset_of_incident hn Γ hΓ ε hx hxt
      have hlt := locusRank_lt_of_incident hn Γ hΓ ε hσ hne hx hxt
      exact ⟨hσ.mono hsub, by omega⟩
  have hlow := (hbound k le_rfl).2
  have hupp := locusRank_le (σ k)
  omega

end DifferentialGeometry.FixedLocusGeometry
