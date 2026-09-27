/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FoldCrossing

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def linearHalfSpace (S : Submodule ℝ E) (u : E) : Set E :=
  {x | ∃ s ∈ S, ∃ r : ℝ, 0 ≤ r ∧ x = s + r • u}

def foldedPlane (S : Submodule ℝ E) (u v : E) : Set E :=
  linearHalfSpace S u ∪ linearHalfSpace S v

theorem linearHalfSpace_smul_of_pos (S : Submodule ℝ E) (u : E) {c : ℝ} (hc : 0 < c) :
    linearHalfSpace S (c • u) = linearHalfSpace S u := by
  ext x
  constructor
  · rintro ⟨s, hs, r, hr, rfl⟩
    refine ⟨s, hs, r * c, mul_nonneg hr hc.le, ?_⟩
    rw [smul_smul]
  · rintro ⟨s, hs, r, hr, rfl⟩
    refine ⟨s, hs, r / c, div_nonneg hr hc.le, ?_⟩
    rw [smul_smul, div_mul_cancel₀ _ hc.ne']

theorem linearHalfSpace_eq_of_sub_mem (S : Submodule ℝ E) {u v : E}
    (huv : u - v ∈ S) : linearHalfSpace S u = linearHalfSpace S v :=
  halfSpace_eq_of_sub_mem S huv

theorem exists_common_direction_of_eq_apply {S T : Submodule ℝ E}
    (ℓ : E →ₗ[ℝ] ℝ) (hST : S ⊔ T = LinearMap.ker ℓ) {u v : E}
    (huv : ℓ u = ℓ v) :
    ∃ w : E, u - w ∈ S ∧ v - w ∈ T ∧ ℓ w = ℓ u := by
  have hd : u - v ∈ S ⊔ T := by
    rw [hST, LinearMap.mem_ker, map_sub, huv, sub_self]
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp hd
  refine ⟨u - s, ?_, ?_, ?_⟩
  · have heq : u - (u - s) = s := by abel
    rw [heq]
    exact hs
  · have heq : v - (u - s) = -t := by
      calc
        v - (u - s) = -(u - v) + s := by abel
        _ = -(s + t) + s := by rw [← hst]
        _ = -t := by abel
    rw [heq]
    exact T.neg_mem ht
  · have hsKer : s ∈ LinearMap.ker ℓ := by
      rw [← hST]
      exact Submodule.mem_sup_left hs
    rw [map_sub, LinearMap.mem_ker.mp hsKer, sub_zero]

theorem exists_isPLHomeomorphOn_straighten_two_folds [FiniteDimensional ℝ E]
    (ℓ : E →ₗ[ℝ] ℝ) {S T : Submodule ℝ E}
    (hST : S ⊔ T = LinearMap.ker ℓ) {aPos aNeg bPos bNeg : E}
    (haPos : 0 < ℓ aPos) (haNeg : ℓ aNeg < 0)
    (hbPos : 0 < ℓ bPos) (hbNeg : ℓ bNeg < 0) :
    ∃ (w : E) (h : E → E), ℓ w = 1 ∧ IsPLHomeomorphOn h univ univ ∧
      EqOn h id (LinearMap.ker ℓ : Set E) ∧
        h '' foldedPlane S aPos aNeg = (S ⊔ Submodule.span ℝ {w} : Submodule ℝ E) ∧
          h '' foldedPlane T bPos bNeg = (T ⊔ Submodule.span ℝ {w} : Submodule ℝ E) := by
  let a₁ := (ℓ aPos)⁻¹ • aPos
  let b₁ := (ℓ bPos)⁻¹ • bPos
  let a₂ := (-ℓ aNeg)⁻¹ • aNeg
  let b₂ := (-ℓ bNeg)⁻¹ • bNeg
  have ha₁ : ℓ a₁ = 1 := by
    simp only [a₁, map_smul, smul_eq_mul, inv_mul_cancel₀ haPos.ne']
  have hb₁ : ℓ b₁ = 1 := by
    simp only [b₁, map_smul, smul_eq_mul, inv_mul_cancel₀ hbPos.ne']
  have ha₂ : ℓ a₂ = -1 := by
    simp only [a₂, map_smul, smul_eq_mul, inv_neg, neg_mul,
      inv_mul_cancel₀ haNeg.ne]
  have hb₂ : ℓ b₂ = -1 := by
    simp only [b₂, map_smul, smul_eq_mul, inv_neg, neg_mul,
      inv_mul_cancel₀ hbNeg.ne]
  obtain ⟨w, hawS, hbwT, hw⟩ :=
    exists_common_direction_of_eq_apply ℓ hST (ha₁.trans hb₁.symm)
  obtain ⟨z, hazS, hbzT, hz⟩ :=
    exists_common_direction_of_eq_apply ℓ hST (ha₂.trans hb₂.symm)
  have hw1 : ℓ w = 1 := hw.trans ha₁
  have hzm1 : ℓ z = -1 := hz.trans ha₂
  have hwpos : 0 < ℓ w := by rw [hw1]; norm_num
  have hzneg : ℓ z < 0 := by rw [hzm1]; norm_num
  obtain ⟨h, hh, hfix, hru, hrv, hadd, _⟩ :=
    exists_isPLHomeomorphOn_straighten_rays ℓ hwpos hzneg
  have hSker : S ≤ LinearMap.ker ℓ := by
    intro s hs
    rw [← hST]
    exact Submodule.mem_sup_left hs
  have hTker : T ≤ LinearMap.ker ℓ := by
    intro t ht
    rw [← hST]
    exact Submodule.mem_sup_right ht
  have himage : ∀ R : Submodule ℝ E, R ≤ LinearMap.ker ℓ →
      h '' foldedPlane R w z = (R ⊔ Submodule.span ℝ {w} : Submodule ℝ E) := by
    intro R hR
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      rcases hx with ⟨s, hs, r, hr, rfl⟩ | ⟨s, hs, r, hr, rfl⟩
      · rw [hadd s (r • w) (LinearMap.mem_ker.mp (hR hs)), hru r hr]
        exact Submodule.add_mem _ (Submodule.mem_sup_left hs)
          (Submodule.mem_sup_right (Submodule.smul_mem _ r
            (Submodule.subset_span (Set.mem_singleton w))))
      · rw [hadd s (r • z) (LinearMap.mem_ker.mp (hR hs)), hrv r hr]
        exact Submodule.add_mem _ (Submodule.mem_sup_left hs)
          (Submodule.mem_sup_right (Submodule.smul_mem _ _
            (Submodule.subset_span (Set.mem_singleton w))))
    · intro y hy
      obtain ⟨s, hs, p, hp, hsp⟩ := Submodule.mem_sup.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hp
      by_cases hc : 0 ≤ c
      · refine ⟨s + c • w, Or.inl ⟨s, hs, c, hc, rfl⟩, ?_⟩
        rw [hadd s (c • w) (LinearMap.mem_ker.mp (hR hs)), hru c hc]
        exact hsp
      · have hc' : 0 ≤ -c := neg_nonneg.mpr (le_of_not_ge hc)
        refine ⟨s + (-c) • z, Or.inr ⟨s, hs, -c, hc', rfl⟩, ?_⟩
        calc
          h (s + (-c) • z) = s + h ((-c) • z) :=
            hadd s ((-c) • z) (LinearMap.mem_ker.mp (hR hs))
          _ = s + ((-c) * (ℓ z / ℓ w)) • w := by rw [hrv (-c) hc']
          _ = s + c • w := by rw [hzm1, hw1]; module
          _ = y := hsp
  have hSaPos : linearHalfSpace S aPos = linearHalfSpace S w := by
    calc
      linearHalfSpace S aPos = linearHalfSpace S a₁ :=
        (linearHalfSpace_smul_of_pos S aPos (inv_pos.mpr haPos)).symm
      _ = linearHalfSpace S w := linearHalfSpace_eq_of_sub_mem S hawS
  have hSaNeg : linearHalfSpace S aNeg = linearHalfSpace S z := by
    calc
      linearHalfSpace S aNeg = linearHalfSpace S a₂ :=
        (linearHalfSpace_smul_of_pos S aNeg (inv_pos.mpr (neg_pos.mpr haNeg))).symm
      _ = linearHalfSpace S z := linearHalfSpace_eq_of_sub_mem S hazS
  have hTbPos : linearHalfSpace T bPos = linearHalfSpace T w := by
    calc
      linearHalfSpace T bPos = linearHalfSpace T b₁ :=
        (linearHalfSpace_smul_of_pos T bPos (inv_pos.mpr hbPos)).symm
      _ = linearHalfSpace T w := linearHalfSpace_eq_of_sub_mem T hbwT
  have hTbNeg : linearHalfSpace T bNeg = linearHalfSpace T z := by
    calc
      linearHalfSpace T bNeg = linearHalfSpace T b₂ :=
        (linearHalfSpace_smul_of_pos T bNeg (inv_pos.mpr (neg_pos.mpr hbNeg))).symm
      _ = linearHalfSpace T z := linearHalfSpace_eq_of_sub_mem T hbzT
  refine ⟨w, h, hw1, hh, hfix, ?_, ?_⟩
  · rw [foldedPlane, hSaPos, hSaNeg]
    exact himage S hSker
  · rw [foldedPlane, hTbPos, hTbNeg]
    exact himage T hTker

theorem hasPLCrossingAt_of_two_folds [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 3) {S T : Submodule ℝ E}
    (hSdim : Module.finrank ℝ S = 1) (hTdim : Module.finrank ℝ T = 1)
    (ℓ : E →ₗ[ℝ] ℝ) (hST : S ⊔ T = LinearMap.ker ℓ)
    {aPos aNeg bPos bNeg x : E}
    (haPos : 0 < ℓ aPos) (haNeg : ℓ aNeg < 0)
    (hbPos : 0 < ℓ bPos) (hbNeg : ℓ bNeg < 0) {A B : Set E}
    (hA : ∀ᶠ y in 𝓝 x, y ∈ A ↔ y - x ∈ foldedPlane S aPos aNeg)
    (hB : ∀ᶠ y in 𝓝 x, y ∈ B ↔ y - x ∈ foldedPlane T bPos bNeg) :
    HasPLCrossingAt A B x := by
  obtain ⟨w, f, hw, hf, hfix, hfoldA, hfoldB⟩ :=
    exists_isPLHomeomorphOn_straighten_two_folds ℓ hST haPos haNeg hbPos hbNeg
  let W : Submodule ℝ E := Submodule.span ℝ {w}
  let P : Submodule ℝ E := S ⊔ W
  let Q : Submodule ℝ E := T ⊔ W
  have hw0 : w ≠ 0 := by
    intro hw0
    rw [hw0, map_zero] at hw
    norm_num at hw
  have hwS : w ∉ S := by
    intro hwS
    have hwker : w ∈ LinearMap.ker ℓ := by
      rw [← hST]
      exact Submodule.mem_sup_left hwS
    rw [LinearMap.mem_ker, hw] at hwker
    norm_num at hwker
  have hwT : w ∉ T := by
    intro hwT
    have hwker : w ∈ LinearMap.ker ℓ := by
      rw [← hST]
      exact Submodule.mem_sup_right hwT
    rw [LinearMap.mem_ker, hw] at hwker
    norm_num at hwker
  have hWdim : Module.finrank ℝ W = 1 := finrank_span_singleton hw0
  have hSW0 : Module.finrank ℝ (S ⊓ W : Submodule ℝ E) = 0 :=
    Submodule.finrank_eq_zero.mpr
      (disjoint_iff.mp (Submodule.disjoint_span_singleton_of_notMem hwS))
  have hTW0 : Module.finrank ℝ (T ⊓ W : Submodule ℝ E) = 0 :=
    Submodule.finrank_eq_zero.mpr
      (disjoint_iff.mp (Submodule.disjoint_span_singleton_of_notMem hwT))
  have hPdim : Module.finrank ℝ P = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq S W
    change Module.finrank ℝ P + Module.finrank ℝ (S ⊓ W : Submodule ℝ E) =
      Module.finrank ℝ S + Module.finrank ℝ W at h
    omega
  have hQdim : Module.finrank ℝ Q = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq T W
    change Module.finrank ℝ Q + Module.finrank ℝ (T ⊓ W : Submodule ℝ E) =
      Module.finrank ℝ T + Module.finrank ℝ W at h
    omega
  have hWker : W ⊔ LinearMap.ker ℓ = ⊤ :=
    sup_ker_eq_top_of_apply_ne_zero W ℓ
      (Submodule.subset_span (Set.mem_singleton w)) (by rw [hw]; norm_num)
  have hPQ : P ⊔ Q = ⊤ := by
    change (S ⊔ W) ⊔ (T ⊔ W) = ⊤
    rw [show (S ⊔ W) ⊔ (T ⊔ W) = (S ⊔ T) ⊔ W by ac_rfl, hST]
    simpa only [sup_comm] using hWker
  have hIdim : Module.finrank ℝ (P ⊓ Q : Submodule ℝ E) = 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P Q
    rw [hPQ, finrank_top, hdim, hPdim, hQdim] at h
    omega
  have hfinj : Function.Injective f := fun a b hab =>
    hf.bijOn.injOn (mem_univ a) (mem_univ b) hab
  have hmem : ∀ (C : Set E) (y : E), f y ∈ f '' C ↔ y ∈ C := by
    intro C y
    exact hfinj.mem_set_image
  let h : E → E := fun y => f (y - x)
  have hh : IsPLHomeomorphOn h univ univ := by
    have hcomp := (isPLHomeomorphOn_add_const (-x)).trans hf
    apply hcomp.congr
    intro y _
    change f (y - x) = f (y + -x)
    rw [sub_eq_add_neg]
  have hhx : h x = 0 := by
    change f (x - x) = 0
    rw [sub_self]
    exact hfix (LinearMap.ker ℓ).zero_mem
  refine ⟨univ, univ, h, P, Q, 0, 0, isOpen_univ, isOpen_univ, mem_univ x,
    hh, hhx, hPdim, hQdim, hIdim, hPQ, Or.inl rfl, Or.inl rfl, Or.inl rfl, ?_⟩
  filter_upwards [hA, hB] with y hyA hyB
  simp only [LinearMap.zero_apply, le_refl, and_true]
  constructor
  · have hm := hmem (foldedPlane S aPos aNeg) (y - x)
    rw [hfoldA] at hm
    exact hyA.trans hm.symm
  · have hm := hmem (foldedPlane T bPos bNeg) (y - x)
    rw [hfoldB] at hm
    exact hyB.trans hm.symm

end DifferentialGeometry.Topology.PiecewiseLinear
