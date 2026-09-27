/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.RadialBandPush
import DifferentialGeometry.External.Schoenflies.Plane

open Set Metric Topology Schoenflies

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem norm_radialBandPush_const_mem {α β p q : ℝ} (hα : 0 < α) (hαp : α < p) (hpβ : p < β)
    (hαq : α < q) (hqβ : q < β) {x : Plane} :
    (α ≤ ‖x‖ → ‖x‖ ≤ p → α ≤ ‖radialBandPush α β (fun _ => p) (fun _ => q) x‖ ∧
      ‖radialBandPush α β (fun _ => p) (fun _ => q) x‖ ≤ q) ∧
    (p ≤ ‖x‖ → ‖x‖ ≤ β → q ≤ ‖radialBandPush α β (fun _ => p) (fun _ => q) x‖ ∧
      ‖radialBandPush α β (fun _ => p) (fun _ => q) x‖ ≤ β) := by
  have hP : ∀ u : Plane, α < (fun _ => p) u ∧ (fun _ => p) u < β := fun _ => ⟨hαp, hpβ⟩
  have hQ : ∀ u : Plane, α < (fun _ => q) u ∧ (fun _ => q) u < β := fun _ => ⟨hαq, hqβ⟩
  constructor
  · intro h1 h2
    rcases le_or_gt ‖x‖ α with hxa | hxa
    · rw [radialBandPush_of_norm_le (fun u => (hP u).1) hxa]
      exact ⟨h1, by linarith⟩
    · rw [norm_radialBandPush hα hP hQ hxa]
      exact ⟨(lt_radialProfile hαp hpβ hαq hqβ hxa).le, radialProfile_le hαp hpβ hαq h2⟩
  · intro h1 h2
    have hxa : α < ‖x‖ := by linarith
    rcases eq_or_lt_of_le h2 with hxb | hxb
    · rw [radialBandPush_of_le_norm (fun u => (hP u).2) hxb.symm.le, hxb]
      exact ⟨hqβ.le, le_rfl⟩
    · rw [norm_radialBandPush hα hP hQ hxa, radialProfile_of_le_of_le_right hαp hpβ h1 h2]
      constructor
      · have : (β - ‖x‖) * (β - q) / (β - p) ≤ β - q := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith [mul_nonneg (sub_nonneg.mpr hqβ.le) (sub_nonneg.mpr h1)]
        linarith
      · have : 0 ≤ (β - ‖x‖) * (β - q) / (β - p) :=
          div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
        linarith

theorem image_radialBandPush_const {α β p q : ℝ} (hα : 0 < α) (hαp : α < p) (hpβ : p < β)
    (hαq : α < q) (hqβ : q < β) :
    radialBandPush α β (fun _ => p) (fun _ => q) '' {x : Plane | α ≤ ‖x‖ ∧ ‖x‖ ≤ p} =
      {x : Plane | α ≤ ‖x‖ ∧ ‖x‖ ≤ q} ∧
    radialBandPush α β (fun _ => p) (fun _ => q) '' {x : Plane | p ≤ ‖x‖ ∧ ‖x‖ ≤ β} =
      {x : Plane | q ≤ ‖x‖ ∧ ‖x‖ ≤ β} := by
  have hP : ∀ u : Plane, α < (fun _ => p) u ∧ (fun _ => p) u < β := fun _ => ⟨hαp, hpβ⟩
  have hQ : ∀ u : Plane, α < (fun _ => q) u ∧ (fun _ => q) u < β := fun _ => ⟨hαq, hqβ⟩
  have hinv : ∀ y : Plane, radialBandPush α β (fun _ => p) (fun _ => q)
      (radialBandPush α β (fun _ => q) (fun _ => p) y) = y :=
    fun y => radialBandPush_radialBandPush hα hQ hP y
  constructor
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (norm_radialBandPush_const_mem hα hαp hpβ hαq hqβ).1 hx.1 hx.2
    · intro hy
      refine ⟨radialBandPush α β (fun _ => q) (fun _ => p) y, ?_, hinv y⟩
      exact (norm_radialBandPush_const_mem hα hαq hqβ hαp hpβ).1 hy.1 hy.2
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (norm_radialBandPush_const_mem hα hαp hpβ hαq hqβ).2 hx.1 hx.2
    · intro hy
      refine ⟨radialBandPush α β (fun _ => q) (fun _ => p) y, ?_, hinv y⟩
      exact (norm_radialBandPush_const_mem hα hαq hqβ hαp hpβ).2 hy.1 hy.2

theorem exists_radialBandPush_const_family {α β p q : ℝ} (hα : 0 < α) (hαp : α < p)
    (hpβ : p < β) (hαq : α < q) (hqβ : q < β) :
    ∃ σ : ℝ → Plane ≃ₜ Plane, Continuous (fun z : ℝ × Plane => σ z.1 z.2) ∧
      Continuous (fun z : ℝ × Plane => (σ z.1).symm z.2) ∧ σ 0 = Homeomorph.refl Plane ∧
      (∀ t, EqOn (σ t) id {x : Plane | α < ‖x‖ ∧ ‖x‖ < β}ᶜ) ∧
      ∀ x, σ 1 x = radialBandPush α β (fun _ => p) (fun _ => q) x := by
  let P : ℝ × Plane → ℝ := fun _ => p
  let Q : ℝ × Plane → ℝ := fun z => p + max 0 (min 1 z.1) * (q - p)
  have hQm : ∀ t : ℝ, 0 ≤ max 0 (min 1 t) ∧ max 0 (min 1 t) ≤ 1 := fun t =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hQ : ∀ z, α < Q z ∧ Q z < β := by
    intro z
    obtain ⟨h0, h1⟩ := hQm z.1
    change α < p + max 0 (min 1 z.1) * (q - p) ∧ p + max 0 (min 1 z.1) * (q - p) < β
    set m := max 0 (min 1 z.1) with hm
    have e : p + m * (q - p) = (1 - m) * p + m * q := by ring
    rw [e]
    rcases eq_or_lt_of_le h0 with hm0 | hm0
    · rw [← hm0]
      constructor <;> linarith
    · constructor
      · nlinarith [mul_pos hm0 (sub_pos.mpr hαq), mul_nonneg (sub_nonneg.mpr h1)
          (sub_pos.mpr hαp).le]
      · nlinarith [mul_pos hm0 (sub_pos.mpr hqβ), mul_nonneg (sub_nonneg.mpr h1)
          (sub_pos.mpr hpβ).le]
  obtain ⟨σ, hσc, hσi, hσeq⟩ := exists_radialBandPush_family hα (P := P) (Q := Q)
    continuous_const (continuous_const.add ((continuous_const.max (continuous_const.min
      continuous_fst)).mul continuous_const)) (fun _ => ⟨hαp, hpβ⟩) hQ
  refine ⟨σ, hσc, hσi, ?_, fun t x hx => ?_, fun x => ?_⟩
  · refine Homeomorph.ext fun x => ?_
    rw [(hσeq 0 x).1]
    apply radialBandPush_of_eq
    change p = p + max 0 (min 1 (0 : ℝ)) * (q - p)
    simp
  · rw [(hσeq t x).1]
    simp only [mem_compl_iff, mem_ofPred_eq, not_and_or, not_lt] at hx
    rcases hx with hx | hx
    · exact radialBandPush_of_norm_le (fun _ => hαp) hx
    · exact radialBandPush_of_le_norm (fun _ => hpβ) hx
  · rw [(hσeq 1 x).1]
    congr 1
    funext u
    change p + max 0 (min 1 (1 : ℝ)) * (q - p) = q
    simp

theorem exists_isotopy_radial_annulus {r₁ r₂ q₁ q₂ : ℝ} (h1 : 1 < r₁) (h12 : r₁ < r₂)
    (h2 : r₂ < 2) (g1 : 1 < q₁) (g12 : q₁ < q₂) (g2 : q₂ < 2) :
    ∃ R : ℝ → Plane ≃ₜ Plane, Continuous (fun z : ℝ × Plane => R z.1 z.2) ∧
      Continuous (fun z : ℝ × Plane => (R z.1).symm z.2) ∧ R 0 = Homeomorph.refl Plane ∧
      ∃ α β : ℝ, 1 < α ∧ α < β ∧ β < 2 ∧
        (∀ t, EqOn (R t) id {x : Plane | α < ‖x‖ ∧ ‖x‖ < β}ᶜ ∧
          EqOn (R t).symm id {x : Plane | α < ‖x‖ ∧ ‖x‖ < β}ᶜ) ∧
        R 1 '' {x : Plane | r₁ ≤ ‖x‖ ∧ ‖x‖ ≤ r₂} = {x : Plane | q₁ ≤ ‖x‖ ∧ ‖x‖ ≤ q₂} := by
  obtain ⟨η, hη, hη1, hη2, hη3, hη4⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ (r₁ - 1) / 2 ∧ η ≤ (q₁ - 1) / 2 ∧
      η ≤ (2 - r₂) / 2 ∧ η ≤ (2 - q₂) / 2 :=
    ⟨min (min ((r₁ - 1) / 2) ((q₁ - 1) / 2)) (min ((2 - r₂) / 2) ((2 - q₂) / 2)),
      lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith)),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  obtain ⟨σ₁, hσ₁c, hσ₁i, hσ₁0, hσ₁fix, hσ₁1⟩ := exists_radialBandPush_const_family
    (α := r₁) (β := 2 - η) (p := r₂) (q := 2 - 2 * η) (by linarith) h12 (by linarith)
    (by linarith) (by linarith)
  obtain ⟨σ₂, hσ₂c, hσ₂i, hσ₂0, hσ₂fix, hσ₂1⟩ := exists_radialBandPush_const_family
    (α := 1 + η) (β := 2 - 2 * η) (p := r₁) (q := q₁) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)
  obtain ⟨σ₃, hσ₃c, hσ₃i, hσ₃0, hσ₃fix, hσ₃1⟩ := exists_radialBandPush_const_family
    (α := q₁) (β := 2 - η) (p := 2 - 2 * η) (q := q₂) (by linarith) (by linarith)
    (by linarith) g12 (by linarith)
  let R : ℝ → Plane ≃ₜ Plane := fun t => (σ₁ t).trans ((σ₂ t).trans (σ₃ t))
  have hfix : ∀ t, EqOn (R t) id {x : Plane | 1 + η < ‖x‖ ∧ ‖x‖ < 2 - η}ᶜ := by
    intro t x hx
    simp only [mem_compl_iff, mem_ofPred_eq, not_and_or, not_lt] at hx
    have h1x : σ₁ t x = x := hσ₁fix t (by
      simp only [mem_compl_iff, mem_ofPred_eq, not_and_or, not_lt]
      rcases hx with hx | hx
      · exact Or.inl (by linarith)
      · exact Or.inr hx)
    have h2x : σ₂ t x = x := hσ₂fix t (by
      simp only [mem_compl_iff, mem_ofPred_eq, not_and_or, not_lt]
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (by linarith))
    have h3x : σ₃ t x = x := hσ₃fix t (by
      simp only [mem_compl_iff, mem_ofPred_eq, not_and_or, not_lt]
      rcases hx with hx | hx
      · exact Or.inl (by linarith)
      · exact Or.inr hx)
    change σ₃ t (σ₂ t (σ₁ t x)) = x
    rw [h1x, h2x, h3x]
  refine ⟨R, hσ₃c.comp (continuous_fst.prodMk (hσ₂c.comp (continuous_fst.prodMk hσ₁c))),
    hσ₁i.comp (continuous_fst.prodMk (hσ₂i.comp (continuous_fst.prodMk hσ₃i))), ?_,
    1 + η, 2 - η, by linarith, by linarith, by linarith, fun t => ⟨hfix t, fun y hy => ?_⟩, ?_⟩
  · refine Homeomorph.ext fun x => ?_
    change σ₃ 0 (σ₂ 0 (σ₁ 0 x)) = x
    rw [hσ₁0, hσ₂0, hσ₃0]
    rfl
  · have h : R t y = y := hfix t hy
    change (R t).symm y = y
    conv_lhs => rw [← h]
    exact (R t).symm_apply_apply y
  · have e1 : (σ₁ 1 : Plane → Plane) = radialBandPush r₁ (2 - η) (fun _ => r₂)
        (fun _ => 2 - 2 * η) := funext hσ₁1
    have e2 : (σ₂ 1 : Plane → Plane) = radialBandPush (1 + η) (2 - 2 * η) (fun _ => r₁)
        (fun _ => q₁) := funext hσ₂1
    have e3 : (σ₃ 1 : Plane → Plane) = radialBandPush q₁ (2 - η) (fun _ => 2 - 2 * η)
        (fun _ => q₂) := funext hσ₃1
    have hR : ((R 1 : Plane ≃ₜ Plane) : Plane → Plane) = σ₃ 1 ∘ σ₂ 1 ∘ σ₁ 1 := rfl
    rw [hR, image_comp, image_comp, e1, e2, e3,
      (image_radialBandPush_const (by linarith) h12 (by linarith) (by linarith)
        (by linarith)).1,
      (image_radialBandPush_const (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith)).2,
      (image_radialBandPush_const (by linarith) (by linarith) (by linarith) g12
        (by linarith)).1]

end DifferentialGeometry.Topology.PiecewiseLinear
