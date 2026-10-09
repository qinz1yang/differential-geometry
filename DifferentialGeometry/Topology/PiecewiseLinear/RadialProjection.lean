/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Cone
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialImage
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eq_zero_of_sum_eq_zero_of_affineIndependent {t : Finset E}
    (ht : AffineIndependent ℝ ((↑) : t → E)) {a : E → ℝ} (h₀ : ∑ v ∈ t, a v = 0)
    (h₁ : ∑ v ∈ t, a v • v = 0) : ∀ v ∈ t, a v = 0 := by
  have h := affineIndependent_iff.mp ht Finset.univ (fun i : t => a i) ?_ ?_
  · intro v hv
    exact h ⟨v, hv⟩ (Finset.mem_univ _)
  · rw [Finset.sum_coe_sort t a]
    exact h₀
  · rw [Finset.sum_coe_sort t fun v => a v • v]
    exact h₁

theorem affineIndependent_of_forall_eq_zero {t : Finset E}
    (h : ∀ a : E → ℝ, ∑ v ∈ t, a v = 0 → ∑ v ∈ t, a v • v = 0 → ∀ v ∈ t, a v = 0) :
    AffineIndependent ℝ ((↑) : t → E) := by
  classical
  rw [affineIndependent_iff_of_fintype]
  intro w hw hvs
  rw [Finset.weightedVSub_eq_linear_combination _ hw] at hvs
  let m : E → ℝ := fun v => if hv : v ∈ t then w ⟨v, hv⟩ else 0
  have hm : ∀ i : t, m i = w i := fun i => by simp [m, i.2]
  have hm₀ : ∑ v ∈ t, m v = 0 := by
    rw [← Finset.sum_coe_sort t m]
    simp_rw [hm]
    exact hw
  have hm₁ : ∑ v ∈ t, m v • v = 0 := by
    rw [← Finset.sum_coe_sort t fun v => m v • v]
    simp_rw [hm]
    exact hvs
  intro i
  rw [← hm i]
  exact h m hm₀ hm₁ i i.2

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem sum_pos_of_weights {σ : Finset E} {μ c : E → ℝ} (hμ₀ : ∀ v ∈ σ, 0 ≤ μ v)
    (hμ₁ : ∑ v ∈ σ, μ v = 1) (hc : ∀ v ∈ σ, 0 < c v) : 0 < ∑ v ∈ σ, μ v * c v := by
  by_contra h
  have hnn : 0 ≤ ∑ v ∈ σ, μ v * c v :=
    Finset.sum_nonneg fun v hv => mul_nonneg (hμ₀ v hv) (hc v hv).le
  have h0 : ∑ v ∈ σ, μ v * c v = 0 := le_antisymm (not_lt.mp h) hnn
  have hall := (Finset.sum_eq_zero_iff_of_nonneg fun v hv =>
    mul_nonneg (hμ₀ v hv) (hc v hv).le).mp h0
  have : ∑ v ∈ σ, μ v = 0 := Finset.sum_eq_zero fun v hv => by
    rcases mul_eq_zero.mp (hall v hv) with h | h
    · exact h
    · exact absurd h (hc v hv).ne'
  linarith

theorem sum_smul_radial_eq {σ : Finset E} {lam c : E → ℝ} (hlam : ∑ v ∈ σ, lam v = 1) (p : E)
    (hS : ∑ v ∈ σ, lam v * c v ≠ 0) :
    ∑ v ∈ σ, lam v • (p + c v • (v - p)) =
      p + (∑ v ∈ σ, lam v * c v) •
        ((∑ v ∈ σ, ((∑ u ∈ σ, lam u * c u)⁻¹ * (lam v * c v)) • v) - p) := by
  have h2 : (∑ v ∈ σ, lam v * c v) • ∑ v ∈ σ, ((∑ u ∈ σ, lam u * c u)⁻¹ * (lam v * c v)) • v =
      ∑ v ∈ σ, (lam v * c v) • v := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [smul_smul, mul_inv_cancel_left₀ hS]
  rw [smul_sub, h2]
  simp_rw [smul_add, smul_sub, smul_smul]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.sum_smul]
  rw [hlam, one_smul]

theorem simplicialMap_radialProj_eq (L' : Geometry.SimplicialComplex ℝ E) (p : E) (S : Set E)
    {σ : Finset E} (hσ : σ ∈ L'.faces) {x : E} (hx : x ∈ convexHull ℝ (σ : Set E)) :
    ∃ (T : ℝ) (z : E), 0 < T ∧ z ∈ convexHull ℝ (σ : Set E) ∧
      simplicialMap L' (radialProj p S) x = p + T • (z - p) ∧
      ∀ v ∈ σ, weights σ x v * radialRatio p S v = T * weights σ z v := by
  have hlam₀ : ∀ v ∈ σ, 0 ≤ weights σ x v := fun v hv => weights_nonneg hx hv
  have hlam₁ : ∑ v ∈ σ, weights σ x v = 1 := sum_weights hx
  have hc_pos : ∀ v, 0 < radialRatio p S v := radialRatio_pos p S
  have hT : 0 < ∑ v ∈ σ, weights σ x v * radialRatio p S v :=
    sum_pos_of_weights hlam₀ hlam₁ fun v _ => hc_pos v
  have hz₀ : ∀ v ∈ σ, 0 ≤ (∑ u ∈ σ, weights σ x u * radialRatio p S u)⁻¹ *
      (weights σ x v * radialRatio p S v) := fun v hv =>
    mul_nonneg (inv_pos.mpr hT).le (mul_nonneg (hlam₀ v hv) (hc_pos v).le)
  have hz₁ : ∑ v ∈ σ, (∑ u ∈ σ, weights σ x u * radialRatio p S u)⁻¹ *
      (weights σ x v * radialRatio p S v) = 1 := by
    rw [← Finset.mul_sum, inv_mul_cancel₀ hT.ne']
  have hz : ∑ v ∈ σ, ((∑ u ∈ σ, weights σ x u * radialRatio p S u)⁻¹ *
      (weights σ x v * radialRatio p S v)) • v ∈ convexHull ℝ (σ : Set E) :=
    (convex_convexHull ℝ _).sum_mem hz₀ hz₁ fun v hv =>
      subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)
  refine ⟨_, _, hT, hz, ?_, fun v hv => ?_⟩
  · rw [simplicialMap_eq_of_mem L' _ hσ hx]
    exact sum_smul_radial_eq hlam₁ p hT.ne'
  · rw [weights_eq (L'.indep hσ) hz hz₁ rfl v hv, mul_inv_cancel_left₀ hT.ne']

theorem injOn_simplicialMap_radialProj (p : E) (L' : Geometry.SimplicialComplex ℝ E)
    (hL' : IsConeBase p L') (S : Set E) :
    InjOn (simplicialMap L' (radialProj p S)) L'.space := by
  classical
  intro x₁ hx₁ x₂ hx₂ hx
  obtain ⟨σ₁, hσ₁, hx₁σ⟩ := L'.mem_space_iff.mp hx₁
  obtain ⟨σ₂, hσ₂, hx₂σ⟩ := L'.mem_space_iff.mp hx₂
  obtain ⟨T₁, z₁, hT₁, hz₁, he₁, hw₁⟩ := simplicialMap_radialProj_eq L' p S hσ₁ hx₁σ
  obtain ⟨T₂, z₂, hT₂, hz₂, he₂, hw₂⟩ := simplicialMap_radialProj_eq L' p S hσ₂ hx₂σ
  have hz₁L : z₁ ∈ L'.space := L'.convexHull_subset_space hσ₁ hz₁
  have hz₂L : z₂ ∈ L'.space := L'.convexHull_subset_space hσ₂ hz₂
  rw [he₁, he₂, add_right_inj] at hx
  have hzz : z₂ = z₁ := by
    refine hL'.radial z₁ hz₁L z₂ hz₂L (T₁ / T₂) (div_pos hT₁ hT₂) ?_
    rw [div_eq_inv_mul, mul_smul, hx, smul_smul, inv_mul_cancel₀ hT₂.ne', one_smul,
      add_sub_cancel]
  rw [hzz] at hz₂ hw₂ hx
  have hTT : T₂ = T₁ := by
    have hne : z₁ - p ≠ 0 := sub_ne_zero.mpr (ne_of_mem_of_not_mem hz₁L hL'.notMem_space)
    have h0 : (T₁ - T₂) • (z₁ - p) = 0 := by rw [sub_smul, hx, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hne
  have hzν : z₁ ∈ convexHull ℝ ((σ₁ ∩ σ₂ : Finset E) : Set E) := by
    rw [Finset.coe_inter]
    exact L'.inter_subset_convexHull hσ₁ hσ₂ ⟨hz₁, hz₂⟩
  have hc_pos : ∀ v, 0 < radialRatio p S v := radialRatio_pos p S
  have hx₁' : ∑ v ∈ σ₁ ∩ σ₂, weights σ₁ x₁ v • v = x₁ := by
    refine (Finset.sum_subset Finset.inter_subset_left fun v hv hvν => ?_).trans
      (sum_weights_smul hx₁σ)
    have h0 : weights σ₁ z₁ v = 0 :=
      weights_eq_zero_of_subset_of_notMem (L'.indep hσ₁) Finset.inter_subset_left hzν hv hvν
    have h := hw₁ v hv
    rw [h0, mul_zero, mul_eq_zero] at h
    rcases h with h | h
    · rw [h, zero_smul]
    · exact absurd h (hc_pos v).ne'
  have hx₂' : ∑ v ∈ σ₁ ∩ σ₂, weights σ₂ x₂ v • v = x₂ := by
    refine (Finset.sum_subset Finset.inter_subset_right fun v hv hvν => ?_).trans
      (sum_weights_smul hx₂σ)
    have h0 : weights σ₂ z₁ v = 0 :=
      weights_eq_zero_of_subset_of_notMem (L'.indep hσ₂) Finset.inter_subset_right hzν hv hvν
    have h := hw₂ v hv
    rw [h0, mul_zero, mul_eq_zero] at h
    rcases h with h | h
    · rw [h, zero_smul]
    · exact absurd h (hc_pos v).ne'
  calc x₁ = ∑ v ∈ σ₁ ∩ σ₂, weights σ₁ x₁ v • v := hx₁'.symm
    _ = ∑ v ∈ σ₁ ∩ σ₂, weights σ₂ x₂ v • v := by
        refine Finset.sum_congr rfl fun v hv => ?_
        have hv₁ : v ∈ σ₁ := Finset.mem_of_mem_inter_left hv
        have hv₂ : v ∈ σ₂ := Finset.mem_of_mem_inter_right hv
        have e₁ : weights σ₁ z₁ v = weights (σ₁ ∩ σ₂) z₁ v :=
          weights_eq_of_subset_of_mem (L'.indep hσ₁) Finset.inter_subset_left hzν hv
        have e₂ : weights σ₂ z₁ v = weights (σ₁ ∩ σ₂) z₁ v :=
          weights_eq_of_subset_of_mem (L'.indep hσ₂) Finset.inter_subset_right hzν hv
        have h₁ := hw₁ v hv₁
        have h₂ := hw₂ v hv₂
        rw [e₁] at h₁
        rw [e₂, hTT] at h₂
        rw [mul_right_cancel₀ (hc_pos v).ne' (h₁.trans h₂.symm)]
    _ = x₂ := hx₂'

theorem affineIndependent_image_radialProj [DecidableEq E] (p : E)
    (L' : Geometry.SimplicialComplex ℝ E) (hL' : IsConeBase p L') (S : Set E) {σ : Finset E}
    (hσ : σ ∈ L'.faces) :
    AffineIndependent ℝ ((↑) : {u // u ∈ σ.image (radialProj p S)} → E) := by
  have hc_pos : ∀ v, 0 < radialRatio p S v := radialRatio_pos p S
  have hvert : ∀ v ∈ σ, v ∈ L'.space := fun v hv =>
    L'.convexHull_subset_space hσ (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))
  have hrinj : ∀ v ∈ σ, ∀ w ∈ σ, radialProj p S v = radialProj p S w → v = w := by
    intro v hv w hw hvw
    refine (hL'.radial v (hvert v hv) w (hvert w hw) (radialRatio p S v / radialRatio p S w)
      (div_pos (hc_pos v) (hc_pos w)) ?_).symm
    have h : radialRatio p S v • (v - p) = radialRatio p S w • (w - p) := by
      rw [← radialProj_sub, ← radialProj_sub, hvw]
    rw [div_eq_inv_mul, mul_smul, h, smul_smul, inv_mul_cancel₀ (hc_pos w).ne', one_smul,
      add_sub_cancel]
  refine affineIndependent_of_forall_eq_zero fun a ha₀ ha₁ => ?_
  rw [Finset.sum_image hrinj] at ha₀ ha₁
  have hpσ : p ∉ σ := fun h => hL'.notMem_space (hvert p h)
  have hind : AffineIndependent ℝ ((↑) : {x // x ∈ (insert p σ : Finset E)} → E) := by
    have h := hL'.indep σ hσ
    rwa [← Finset.coe_insert] at h
  let b : E → ℝ := fun v =>
    if v = p then -(∑ u ∈ σ, a (radialProj p S u) * radialRatio p S u)
    else a (radialProj p S v) * radialRatio p S v
  have hb : ∀ v ∈ σ, b v = a (radialProj p S v) * radialRatio p S v := fun v hv => by
    simp only [b, ite_eq_right (ne_of_mem_of_not_mem hv hpσ)]
  have hb₀ : ∑ v ∈ insert p σ, b v = 0 := by
    rw [Finset.sum_insert hpσ, Finset.sum_congr rfl hb]
    simp [b]
  have hb₁ : ∑ v ∈ insert p σ, b v • v = 0 := by
    rw [Finset.sum_insert hpσ, Finset.sum_congr rfl fun v hv => by rw [hb v hv]]
    simp only [b, ite_true]
    have hsplit : ∑ v ∈ σ, a (radialProj p S v) • radialProj p S v =
        ∑ v ∈ σ, a (radialProj p S v) • p +
          ∑ v ∈ σ, (a (radialProj p S v) * radialRatio p S v) • (v - p) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [← smul_smul, ← smul_add, ← radialProj_sub, add_sub_cancel]
    rw [hsplit, ← Finset.sum_smul, ha₀, zero_smul, zero_add] at ha₁
    simp_rw [smul_sub] at ha₁
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, sub_eq_zero] at ha₁
    rw [ha₁, neg_smul, neg_add_cancel]
  have hzero := eq_zero_of_sum_eq_zero_of_affineIndependent hind hb₀ hb₁
  intro u hu
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
  have h := hzero v (Finset.mem_insert_of_mem hv)
  rw [hb v hv, mul_eq_zero] at h
  rcases h with h | h
  · exact h
  · exact absurd h (hc_pos v).ne'

theorem radialProj_mem_convexHull_image [DecidableEq E] (p : E)
    (L : Geometry.SimplicialComplex ℝ E) (hrayL : IsRadiallyInjective p L.space) {σ : Finset E}
    (hσ : ∃ τ ∈ L.faces, ∀ v ∈ σ, radialProj p L.space v ∈ convexHull ℝ (τ : Set E)) {w : E}
    (hw : w ∈ convexHull ℝ (σ : Set E)) (hwL : ∃ t : ℝ, 0 < t ∧ p + t • (w - p) ∈ L.space) :
    radialProj p L.space w ∈
      convexHull ℝ ((σ.image (radialProj p L.space) : Finset E) : Set E) := by
  obtain ⟨τ, hτ, hrτ⟩ := hσ
  have hrw : radialProj p L.space w ∈ L.space := radialProj_mem hwL
  have hμ₀ : ∀ v ∈ σ, 0 ≤ weights σ w v := fun v hv => weights_nonneg hw hv
  have hμ₁ : ∑ v ∈ σ, weights σ w v = 1 := sum_weights hw
  have hμw : ∑ v ∈ σ, weights σ w v • v = w := sum_weights_smul hw
  have hc_pos : ∀ v, 0 < radialRatio p L.space v := radialRatio_pos p L.space
  let β : E → ℝ := fun v => radialRatio p L.space w * weights σ w v * (radialRatio p L.space v)⁻¹
  have hβ₀ : ∀ v ∈ σ, 0 ≤ β v := fun v hv =>
    mul_nonneg (mul_nonneg (hc_pos w).le (hμ₀ v hv)) (inv_pos.mpr (hc_pos v)).le
  have hB : 0 < ∑ v ∈ σ, β v := by
    have : ∑ v ∈ σ, β v =
        ∑ v ∈ σ, weights σ w v * (radialRatio p L.space w * (radialRatio p L.space v)⁻¹) :=
      Finset.sum_congr rfl fun v _ => by simp only [β]; ring
    rw [this]
    exact sum_pos_of_weights hμ₀ hμ₁ fun v _ => mul_pos (hc_pos w) (inv_pos.mpr (hc_pos v))
  have hkey : radialProj p L.space w - p = ∑ v ∈ σ, β v • (radialProj p L.space v - p) := by
    rw [radialProj_sub]
    simp_rw [radialProj_sub p L.space, smul_smul]
    have hβc : ∀ v ∈ σ, β v * radialRatio p L.space v = radialRatio p L.space w * weights σ w v :=
      fun v hv => by
        simp only [β]
        rw [mul_assoc, inv_mul_cancel₀ (hc_pos v).ne', mul_one]
    rw [Finset.sum_congr rfl fun v hv => by rw [hβc v hv]]
    simp_rw [mul_smul]
    rw [← Finset.smul_sum]
    congr 1
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hμ₁, one_smul, hμw]
  have hq₀ : ∀ v ∈ σ, 0 ≤ (∑ u ∈ σ, β u)⁻¹ * β v := fun v hv =>
    mul_nonneg (inv_pos.mpr hB).le (hβ₀ v hv)
  have hq₁ : ∑ v ∈ σ, (∑ u ∈ σ, β u)⁻¹ * β v = 1 := by
    rw [← Finset.mul_sum, inv_mul_cancel₀ hB.ne']
  have hqmem : ∑ v ∈ σ, ((∑ u ∈ σ, β u)⁻¹ * β v) • radialProj p L.space v ∈
      convexHull ℝ ((σ.image (radialProj p L.space) : Finset E) : Set E) :=
    (convex_convexHull ℝ _).sum_mem hq₀ hq₁ fun v hv =>
      subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hv))
  have himg : convexHull ℝ ((σ.image (radialProj p L.space) : Finset E) : Set E) ⊆ L.space := by
    refine (convexHull_min ?_ (convex_convexHull ℝ _)).trans (L.convexHull_subset_space hτ)
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hu)
    exact hrτ v hv
  have hq : ∑ v ∈ σ, ((∑ u ∈ σ, β u)⁻¹ * β v) • radialProj p L.space v =
      p + (∑ u ∈ σ, β u)⁻¹ • (radialProj p L.space w - p) := by
    rw [hkey, Finset.smul_sum]
    simp_rw [smul_smul, smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hq₁, one_smul]
    abel
  have := hrayL _ (himg hqmem) _ hrw _ hB (by
    rw [hq, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hB.ne', one_smul, add_sub_cancel])
  rw [this]
  exact hqmem

theorem image_simplicialMap_radialProj_eq (p : E) (L L' : Geometry.SimplicialComplex ℝ E)
    (hrayL : IsRadiallyInjective p L.space) (hL' : IsConeBase p L')
    (hadapt : ∀ σ ∈ L'.faces, ∃ τ ∈ L.faces, ∀ w ∈ σ,
      ∃ s : ℝ, 0 < s ∧ p + s • (w - p) ∈ convexHull ℝ (τ : Set E))
    (hsurj : ∀ x ∈ L.space, ∃ s : ℝ, 0 < s ∧ p + s • (x - p) ∈ L'.space) :
    simplicialMap L' (radialProj p L.space) '' L'.space = L.space := by
  classical
  have hτ : ∀ σ ∈ L'.faces, ∃ τ ∈ L.faces, ∀ v ∈ σ,
      radialProj p L.space v ∈ convexHull ℝ (τ : Set E) := by
    intro σ hσ
    obtain ⟨τ, hτ, h⟩ := hadapt σ hσ
    refine ⟨τ, hτ, fun v hv => ?_⟩
    obtain ⟨s, hs, hmem⟩ := h v hv
    rw [← hrayL.eq_radialProj hs (L.convexHull_subset_space hτ hmem)]
    exact hmem
  have hinj := injOn_simplicialMap_radialProj p L' hL' L.space
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hσ := carrierFace_mem hx
    have hxσ := mem_convexHull_carrierFace hx
    obtain ⟨τ, hτ', hrτ⟩ := hτ _ hσ
    refine L.convexHull_subset_space hτ' ?_
    refine (convexHull_min ?_ (convex_convexHull ℝ _))
      (simplicialMap_mem_convexHull_image L' _ hσ hxσ)
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hu)
    exact hrτ v hv
  · intro x hx
    obtain ⟨s, hs, hw⟩ := hsurj x hx
    have hσ := carrierFace_mem hw
    have hwσ := mem_convexHull_carrierFace hw
    have h1 : p + s⁻¹ • (p + s • (x - p) - p) = x := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs.ne', one_smul, add_sub_cancel]
    have hmem : p + s⁻¹ • (p + s • (x - p) - p) ∈ L.space := by
      rw [h1]
      exact hx
    have hrw : radialProj p L.space (p + s • (x - p)) = x :=
      (hrayL.eq_radialProj (inv_pos.mpr hs) hmem).symm.trans h1
    have hmemimg := radialProj_mem_convexHull_image p L hrayL (hτ _ hσ) hwσ
      ⟨s⁻¹, inv_pos.mpr hs, hmem⟩
    rw [hrw, ← image_convexHull_simplicialMap L' _ hσ
      (injOn_of_injOn_simplicialMap L' _ hinj hσ)] at hmemimg
    exact image_mono (L'.convexHull_subset_space hσ) hmemimg

theorem exists_isPLHomeomorphOn_of_radial [FiniteDimensional ℝ E] (p : E)
    (L L' : Geometry.SimplicialComplex ℝ E) [Finite L'.faces]
    (hrayL : IsRadiallyInjective p L.space) (hL' : IsConeBase p L')
    (hadapt : ∀ σ ∈ L'.faces, ∃ τ ∈ L.faces, ∀ w ∈ σ,
      ∃ s : ℝ, 0 < s ∧ p + s • (w - p) ∈ convexHull ℝ (τ : Set E))
    (hsurj : ∀ x ∈ L.space, ∃ s : ℝ, 0 < s ∧ p + s • (x - p) ∈ L'.space) :
    ∃ f : E → E, IsPLHomeomorphOn f L'.space L.space := by
  classical
  refine ⟨simplicialMap L' (radialProj p L.space), ?_⟩
  have h := isPLHomeomorphOn_simplicialImage L' (radialProj p L.space)
    (fun σ hσ => affineIndependent_image_radialProj p L' hL' L.space hσ)
    (injOn_simplicialMap_radialProj p L' hL' L.space)
  rwa [simplicialImage_space, image_simplicialMap_radialProj_eq p L L' hrayL hL' hadapt hsurj]
    at h

end DifferentialGeometry.Topology.PiecewiseLinear
