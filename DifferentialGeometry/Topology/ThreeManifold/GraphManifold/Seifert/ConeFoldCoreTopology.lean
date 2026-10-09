import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldCoreChart

/-!
# The triangle minus the Jordan core is preconnected

Lane A4b2 (design `docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, §7). In the
disc chart `coreMap` of `SF/ConeFoldCoreChart.lean` the triangle is star-shaped about `0`
(`coreInv_smul_mem_triangle`: each of the three walls is a hyperbolic half-plane positive at the
centre `coreHyp`), and the closed chart disc of radius `89/1000` lies inside the triangle. Hence
every point of `coreOut = {z ∈ T | 87/1000 < ‖coreMap z‖}` is joined inside `coreOut` by a chart
segment to the circle `‖w‖ = 89/1000`, and `coreOut` is preconnected (`isPreconnected_coreOut`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set Metric
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

open ConeLayout

namespace ConeShape

variable (σ : ConeShape)

theorem coreHyp_mem_outer : normSq (coreHyp - coreCentre) ≤ coreOuter ^ 2 := by
  rw [normSq_sub_coreCentre, coreOuter]
  simp [coreHyp]
  norm_num

theorem wallOneChart_eq (ζ : ℂ) :
    σ.wallOneChart ζ = (-(1 - Real.cos σ.θ₁)) * normSq ζ +
      (2 * σ.chartScale * Real.cos σ.θ₁) * ζ.re + (1 + Real.cos σ.θ₂) := by
  unfold wallOneChart; ring

theorem wallZeroChart_eq (ζ : ℂ) :
    σ.wallZeroChart ζ = (1 + Real.cos σ.θ₂) * normSq ζ +
      (2 * σ.chartScale * Real.cos σ.θ₂) * ζ.re + (-(σ.chartScale ^ 2 * (1 - Real.cos σ.θ₂))) := by
  unfold wallZeroChart; ring

theorem wallSide_two_nonneg_iff {z : ℂ} (hz : 0 < z.im) :
    0 ≤ σ.wallSide 2 z ↔ 0 ≤ -(σ.fermiChart z).re := by
  have hN := σ.normSq_sub_rightFoot_pos hz
  have hk := σ.chartScale_pos
  rw [σ.fermiChart_re, neg_neg]
  constructor
  · intro h; positivity
  · intro h
    have := mul_nonneg h hN.le
    rw [div_mul_cancel₀ _ hN.ne'] at this
    exact nonneg_of_mul_nonneg_right this hk

theorem wallSide_one_nonneg_iff {z : ℂ} (hz : 0 < z.im) :
    0 ≤ σ.wallSide 1 z ↔ 0 ≤ σ.wallOneChart (σ.fermiChart z) := by
  have hN := σ.normSq_sub_rightFoot_pos hz
  have hk := σ.chartScale_pos
  rw [σ.wallOneChart_fermiChart hz]
  constructor
  · intro h; positivity
  · intro h
    have := mul_nonneg h hN.le
    rw [div_mul_cancel₀ _ hN.ne'] at this
    exact nonneg_of_mul_nonneg_right this (by positivity)

theorem wallSide_zero_nonneg_iff {z : ℂ} (hz : 0 < z.im) :
    0 ≤ σ.wallSide 0 z ↔ 0 ≤ σ.wallZeroChart (σ.fermiChart z) := by
  have hN := σ.normSq_sub_rightFoot_pos hz
  have hk := σ.chartScale_pos
  rw [σ.wallZeroChart_fermiChart hz]
  constructor
  · intro h; positivity
  · intro h
    have := mul_nonneg h hN.le
    rw [div_mul_cancel₀ _ hN.ne'] at this
    exact nonneg_of_mul_nonneg_right this (by positivity)

theorem coreInv_smul_mem_triangle (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
    (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂) {z : ℂ} (hz : z ∈ σ.triangle) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : σ.coreInv ((t : ℂ) * σ.coreMap z) ∈ σ.triangle := by
  have ha := coreHyp_im_pos
  have hY := σ.fermiChart_im_pos hz.1
  have hw := σ.norm_coreMap_lt_one hz.1
  have htw : ‖(t : ℂ) * σ.coreMap z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    nlinarith [norm_nonneg (σ.coreMap z)]
  have hζt := discInv_im_pos ha htw
  have hzt := σ.coreInv_im_pos htw
  have hchart : σ.fermiChart (σ.coreInv ((t : ℂ) * σ.coreMap z)) =
      discInv coreHyp ((t : ℂ) * σ.coreMap z) := σ.fermiChart_chartInv hζt
  have hback : discInv coreHyp (σ.coreMap z) = σ.fermiChart z := discInv_coneDisc ha hY
  refine ⟨hzt, fun i => ?_⟩
  fin_cases i
  · change 0 ≤ σ.wallSide 0 _
    rw [σ.wallSide_zero_nonneg_iff hzt, hchart, wallZeroChart_eq]
    refine wall_discInv_smul_nonneg ?_ hw ?_ ht0 ht1
    · rw [← wallZeroChart_eq]; exact core_wallZero_pos σ h₁ h₂ coreHyp_mem_outer
    · rw [← wallZeroChart_eq, hback, ← σ.wallSide_zero_nonneg_iff hz.1]; exact hz.2 0
  · change 0 ≤ σ.wallSide 1 _
    rw [σ.wallSide_one_nonneg_iff hzt, hchart, wallOneChart_eq]
    refine wall_discInv_smul_nonneg ?_ hw ?_ ht0 ht1
    · rw [← wallOneChart_eq]; exact core_wallOne_pos σ h₁ h₂ coreHyp_mem_outer
    · rw [← wallOneChart_eq, hback, ← σ.wallSide_one_nonneg_iff hz.1]; exact hz.2 1
  · change 0 ≤ σ.wallSide 2 _
    rw [σ.wallSide_two_nonneg_iff hzt, hchart]
    have e : ∀ ζ : ℂ, -ζ.re = 0 * normSq ζ + (-1) * ζ.re + 0 := fun ζ => by ring
    rw [e]
    refine wall_discInv_smul_nonneg ?_ hw ?_ ht0 ht1
    · simp [coreHyp]
    · rw [← e, hback, ← σ.wallSide_two_nonneg_iff hz.1]; exact hz.2 2

def coreOut : Set ℂ := {z | z ∈ σ.triangle ∧ 87 / 1000 < ‖σ.coreMap z‖}

theorem isPreconnected_coreOut (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
    (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂) : IsPreconnected σ.coreOut := by
  obtain ⟨ρ₂, hρ₂⟩ : ∃ ρ₂ : ℝ, ρ₂ = 89 / 1000 := ⟨_, rfl⟩
  set C := σ.coreInv '' sphere (0 : ℂ) ρ₂ with hC
  have hball : ∀ w : ℂ, ‖w‖ ≤ ρ₂ → ‖w‖ < 1 := fun w hw => by rw [hρ₂] at hw; linarith
  have hinT : ∀ w : ℂ, ‖w‖ ≤ ρ₂ → σ.coreInv w ∈ σ.triangle := by
    intro w hw
    have h1 := hball w hw
    have hz := σ.coreInv_im_pos h1
    refine (σ.mem_triangle_of_coreMap_le h₁ h₂ hz ?_).1
    rw [σ.coreMap_coreInv h1, ← hρ₂]
    exact hw
  have hCsub : C ⊆ σ.coreOut := by
    rintro _ ⟨q, hq, rfl⟩
    have hq' : ‖q‖ = ρ₂ := by simpa using hq
    refine ⟨hinT q hq'.le, ?_⟩
    rw [σ.coreMap_coreInv (hball q hq'.le), hq', hρ₂]
    norm_num
  have hCc : IsPreconnected C :=
    (isPreconnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 ρ₂).image _
      (σ.continuousOn_coreInv.mono fun q hq => by
        have : ‖q‖ = ρ₂ := by simpa using hq
        simp only [mem_ball, dist_zero_right]
        rw [this, hρ₂]; norm_num)
  have hx₀ : σ.coreInv (ρ₂ : ℂ) ∈ C := ⟨(ρ₂ : ℂ), by simp [hρ₂], rfl⟩
  refine isPreconnected_of_forall (σ.coreInv (ρ₂ : ℂ)) fun z hz => ?_
  obtain ⟨hzT, hzr⟩ := hz
  set w := σ.coreMap z with hw
  set r := ‖w‖ with hr
  have hr1 : r < 1 := σ.norm_coreMap_lt_one hzT.1
  have hr0 : 0 < r := by linarith
  set seg := (fun s : ℝ => σ.coreInv ((s : ℂ) * w)) '' uIcc 1 (ρ₂ / r) with hseg
  have hnorm : ∀ s ∈ uIcc 1 (ρ₂ / r), ‖(s : ℂ) * w‖ = s * r ∧ 0 ≤ s := by
    intro s hs
    have hs0 : 0 ≤ s := by
      rcases le_total 1 (ρ₂ / r) with h | h
      · rw [uIcc_of_le h] at hs; linarith [hs.1]
      · rw [uIcc_of_ge h] at hs; linarith [hs.1, div_pos (by rw [hρ₂]; norm_num : (0 : ℝ) < ρ₂) hr0]
    refine ⟨?_, hs0⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
  have hsr : ∀ s ∈ uIcc 1 (ρ₂ / r), (87 / 1000 < s * r ∧ s * r ≤ max r ρ₂) := by
    intro s hs
    have hρr : ρ₂ / r * r = ρ₂ := div_mul_cancel₀ _ hr0.ne'
    rcases le_total 1 (ρ₂ / r) with h | h
    · rw [uIcc_of_le h] at hs
      have h1 := mul_le_mul_of_nonneg_right hs.2 hr0.le
      have h2 := mul_le_mul_of_nonneg_right hs.1 hr0.le
      rw [hρr] at h1
      constructor <;> nlinarith [le_max_right r ρ₂]
    · rw [uIcc_of_ge h] at hs
      have h1 := mul_le_mul_of_nonneg_right hs.2 hr0.le
      have h2 := mul_le_mul_of_nonneg_right hs.1 hr0.le
      rw [hρr] at h2
      constructor <;> nlinarith [le_max_left r ρ₂]
  have hsegsub : seg ⊆ σ.coreOut := by
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨hn, hs0⟩ := hnorm s hs
    obtain ⟨hlo, hhi⟩ := hsr s hs
    have h1 : ‖(s : ℂ) * w‖ < 1 := by
      rw [hn]; exact lt_of_le_of_lt hhi (max_lt hr1 (by rw [hρ₂]; norm_num))
    refine ⟨?_, by rw [σ.coreMap_coreInv h1, hn]; exact hlo⟩
    rcases le_or_gt s 1 with hs1 | hs1
    · rw [hw]; exact σ.coreInv_smul_mem_triangle h₁ h₂ hzT hs0 hs1
    · apply hinT
      rw [hn]
      have hle : ρ₂ / r ≥ s := by
        rcases le_total 1 (ρ₂ / r) with h | h
        · rw [uIcc_of_le h] at hs; exact hs.2
        · rw [uIcc_of_ge h] at hs; linarith [hs.2]
      have := (le_div_iff₀ hr0).1 hle
      linarith
  have hsegc : IsPreconnected seg := by
    refine isPreconnected_uIcc.image _ fun s hs => ?_
    obtain ⟨hn, -⟩ := hnorm s hs
    obtain ⟨-, hhi⟩ := hsr s hs
    have h1 : ‖(s : ℂ) * w‖ < 1 := by
      rw [hn]; exact lt_of_le_of_lt hhi (max_lt hr1 (by rw [hρ₂]; norm_num))
    have hc := (σ.contDiffAt_coreInv h1).continuousAt
    have hf : ContinuousAt (fun s : ℝ => (s : ℂ) * w) s := by fun_prop
    exact (ContinuousAt.comp (g := σ.coreInv) (f := fun s : ℝ => (s : ℂ) * w) hc
      hf).continuousWithinAt
  have hzseg : z ∈ seg := ⟨1, left_mem_uIcc, by
    simp only [ofReal_one, one_mul, hw]; exact σ.coreInv_coreMap hzT.1⟩
  have hcseg : σ.coreInv (((ρ₂ / r : ℝ) : ℂ) * w) ∈ seg := ⟨ρ₂ / r, right_mem_uIcc, rfl⟩
  have hcC : σ.coreInv (((ρ₂ / r : ℝ) : ℂ) * w) ∈ C := by
    refine ⟨((ρ₂ / r : ℝ) : ℂ) * w, ?_, rfl⟩
    rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos (by rw [hρ₂]; norm_num) hr0), ← hr, div_mul_cancel₀ _ hr0.ne']
  refine ⟨seg ∪ C, union_subset hsegsub hCsub, Or.inr hx₀, Or.inl hzseg,
    hsegc.union _ hcseg hcC hCc⟩

end ConeShape

end GC.Seifert
