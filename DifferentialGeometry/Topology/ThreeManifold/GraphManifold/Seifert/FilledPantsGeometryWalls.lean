import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryPhase
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldSpec
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldQuotient

/-!
# The two-cone shape and the images of the walls under the fold

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §3.3
step 2, with review 21 §4.4). `TwoConeFold.shape p₁ p₂` is the shape with angles `π/p₁`, `π/p₂`
(`(p₁, p₂) ≠ (2, 2)`). For a fold datum `D : σ.FoldData` of a shape with `θ₁ p₁ = π` and
`θ₂ p₂ = π`, the walls minus the vertices are preconnected, `f` is real and injective on them,
avoids `± 3/2 = f(vᵢ)` there, and the apex germs fix the side near each vertex; hence
`f (wall 1 \ {v₁}) ⊆ (3/2, 3)`, `f (wall 2 \ {v₁, v₂}) ⊆ (-3/2, 3/2)`,
`f (wall 0 \ {v₂}) ⊆ (-3, -3/2)`
(`re_f_of_mem_foldWall_one`, `_two`, `_zero`). These are the three disjoint real segments of the
product part, derived from the `FoldData` fields only (no new hypothesis).
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open scoped Topology ComplexConjugate ContDiff

namespace GC.Seifert

namespace TwoConeFold

open ConeShape

def shape (p₁ p₂ : ℕ) (h₁ : 2 ≤ p₁) (h₂ : 2 ≤ p₂) (hne : ¬(p₁ = 2 ∧ p₂ = 2)) :
    ConeShape where
  θ₁ := Real.pi / p₁
  θ₂ := Real.pi / p₂
  θ₁_pos := div_pos Real.pi_pos (by exact_mod_cast (by omega : 0 < p₁))
  θ₁_le := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by exact_mod_cast h₁)
  θ₂_nonneg := div_nonneg Real.pi_pos.le (Nat.cast_nonneg _)
  θ₂_le := div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by exact_mod_cast h₂)
  sum_lt := by
    have hp₁ : (0 : ℝ) < p₁ := by exact_mod_cast (by omega : 0 < p₁)
    have hp₂ : (0 : ℝ) < p₂ := by exact_mod_cast (by omega : 0 < p₂)
    have key : 1 / (p₁ : ℝ) + 1 / p₂ < 1 := by
      rcases (show 3 ≤ p₁ ∨ 3 ≤ p₂ by omega) with h | h
      · have a1 : 1 / (p₁ : ℝ) ≤ 1 / 3 := by
          rw [div_le_div_iff₀ hp₁ (by norm_num), one_mul, one_mul]
          exact_mod_cast (by omega : 3 ≤ p₁)
        have a2 : 1 / (p₂ : ℝ) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hp₂ (by norm_num), one_mul, one_mul]
          exact_mod_cast (by omega : 2 ≤ p₂)
        linarith
      · have a1 : 1 / (p₁ : ℝ) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hp₁ (by norm_num), one_mul, one_mul]
          exact_mod_cast (by omega : 2 ≤ p₁)
        have a2 : 1 / (p₂ : ℝ) ≤ 1 / 3 := by
          rw [div_le_div_iff₀ hp₂ (by norm_num), one_mul, one_mul]
          exact_mod_cast (by omega : 3 ≤ p₂)
        linarith
    have : Real.pi / p₁ + Real.pi / p₂ = Real.pi * (1 / p₁ + 1 / p₂) := by ring
    rw [this]
    nlinarith [Real.pi_pos]

theorem shape_θ₁_mul (p₁ p₂ : ℕ) (h₁ : 2 ≤ p₁) (h₂ : 2 ≤ p₂) (hne : ¬(p₁ = 2 ∧ p₂ = 2)) :
    (shape p₁ p₂ h₁ h₂ hne).θ₁ * p₁ = Real.pi := by
  change Real.pi / p₁ * p₁ = Real.pi
  rw [div_mul_cancel₀ _ (by exact_mod_cast (by omega : p₁ ≠ 0))]

theorem shape_θ₂_mul (p₁ p₂ : ℕ) (h₁ : 2 ≤ p₁) (h₂ : 2 ≤ p₂) (hne : ¬(p₁ = 2 ∧ p₂ = 2)) :
    (shape p₁ p₂ h₁ h₂ hne).θ₂ * p₂ = Real.pi := by
  change Real.pi / p₂ * p₂ = Real.pi
  rw [div_mul_cancel₀ _ (by exact_mod_cast (by omega : p₂ ≠ 0))]

variable (σ : ConeShape)

theorem vertexOne_mem_triangle' : σ.vertexOne ∈ σ.triangle := by
  refine ⟨σ.vertexOne_im_pos, fun i => ?_⟩
  fin_cases i
  · change 0 ≤ σ.vertexOne.re
    rw [vertexOne_re]
    exact σ.width_pos.le
  · change 0 ≤ σ.width - σ.vertexOne.re
    rw [vertexOne_re, sub_self]
  · change 0 ≤ (σ.vertexOne.re - σ.centre) ^ 2 + σ.vertexOne.im ^ 2 - 1 / 16
    rw [vertexOne_re, vertexOne_im]
    unfold width centre
    nlinarith [Real.sin_sq_add_cos_sq σ.θ₁]

theorem wallSide_two_vertexOne' : σ.wallSide 2 σ.vertexOne = 0 := by
  change (σ.vertexOne.re - σ.centre) ^ 2 + σ.vertexOne.im ^ 2 - 1 / 16 = 0
  rw [vertexOne_re, vertexOne_im]
  unfold width centre
  nlinarith [Real.sin_sq_add_cos_sq σ.θ₁]

theorem preconnected_real_avoid {S : Set ℂ} (hS : IsPreconnected S) {g : ℂ → ℝ}
    (hg : ContinuousOn g S) {a b : ℝ} (ha : ∀ z ∈ S, g z ≠ a) (hb : ∀ z ∈ S, g z ≠ b)
    {z₀ : ℂ} (hz₀ : z₀ ∈ S) (h₀ : a < g z₀ ∧ g z₀ < b) : ∀ z ∈ S, a < g z ∧ g z < b := by
  have hI := hS.image g hg
  intro z hz
  constructor
  · by_contra h
    push Not at h
    have hsub := hI.Icc_subset (mem_image_of_mem g hz) (mem_image_of_mem g hz₀)
    obtain ⟨w, hw, hwa⟩ := hsub ⟨h, h₀.1.le⟩
    exact ha w hw hwa
  · by_contra h
    push Not at h
    have hsub := hI.Icc_subset (mem_image_of_mem g hz₀) (mem_image_of_mem g hz)
    obtain ⟨w, hw, hwb⟩ := hsub ⟨h₀.2.le, h⟩
    exact hb w hw hwb


theorem vertexTwo_mem_triangle' (hθ : 0 < σ.θ₂) : σ.vertexTwo ∈ σ.triangle := by
  have hs : 0 < Real.sin σ.θ₂ :=
    Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [σ.θ₂_le, Real.pi_pos])
  refine ⟨by rw [vertexTwo_im]; positivity, fun i => ?_⟩
  fin_cases i
  · change 0 ≤ σ.vertexTwo.re
    rw [vertexTwo_re]
  · change 0 ≤ σ.width - σ.vertexTwo.re
    rw [vertexTwo_re, sub_zero]
    exact σ.width_pos.le
  · change 0 ≤ (σ.vertexTwo.re - σ.centre) ^ 2 + σ.vertexTwo.im ^ 2 - 1 / 16
    rw [vertexTwo_re, vertexTwo_im]
    unfold centre
    nlinarith [Real.sin_sq_add_cos_sq σ.θ₂]

theorem coneDisc_vertical_point (v : ℂ) (y : ℝ) :
    coneDisc v ((v.re : ℂ) + y * I) = (((y - v.im) / (y + v.im) : ℝ) : ℂ) := by
  unfold coneDisc
  have hden : (v.re : ℂ) + y * I - conj v = ((y + v.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hnum : (v.re : ℂ) + y * I - v = ((y - v.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hden, hnum, mul_div_mul_right _ _ I_ne_zero]
  push_cast
  ring

namespace Fold

variable {σ} (D : σ.FoldData) {p₁ p₂ : ℕ} (hθ₁ : σ.θ₁ * p₁ = Real.pi)
  (hθ₂ : σ.θ₂ * p₂ = Real.pi)

include hθ₁ in
theorem p₁_ne_zero : p₁ ≠ 0 := by
  rintro rfl
  simp only [Nat.cast_zero, mul_zero] at hθ₁
  exact Real.pi_ne_zero hθ₁.symm

include hθ₂ in
theorem p₂_ne_zero : p₂ ≠ 0 := by
  rintro rfl
  simp only [Nat.cast_zero, mul_zero] at hθ₂
  exact Real.pi_ne_zero hθ₂.symm

include hθ₂ in
theorem θ₂_pos : 0 < σ.θ₂ := by
  rcases σ.θ₂_nonneg.lt_or_eq with h | h
  · exact h
  · rw [← h, zero_mul] at hθ₂
    exact absurd hθ₂.symm Real.pi_ne_zero

include hθ₁ in
theorem f_vertexOne : D.f σ.vertexOne = 3 / 2 := by
  rw [(D.f_apexOne p₁ hθ₁).self_of_nhds, σ.coneApexOne_vertexOne (p₁_ne_zero hθ₁)]

include hθ₂ in
theorem f_vertexTwo : D.f σ.vertexTwo = -(3 / 2) := by
  rw [(D.f_apexTwo p₂ hθ₂).self_of_nhds]
  simp [coneApexTwo, coneDisc_self, zero_pow (p₂_ne_zero hθ₂)]

theorem continuousOn_f : ContinuousOn D.f σ.triangle :=
  D.contDiffOn_f.continuousOn.mono D.triangle_subset_U

theorem f_eq_ofReal_re {i : Fin 3} {z : ℂ} (hz : z ∈ σ.foldWall i) :
    D.f z = (((D.f z).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [D.f_real_of_mem_foldWall hz])

theorem norm_f_lt_three {z : ℂ} (hz : z ∈ σ.triangle) : ‖D.f z‖ < 3 := (D.bijOn_f.mapsTo hz).1

theorem re_f_lt_three {z : ℂ} (hz : z ∈ σ.triangle) : |(D.f z).re| < 3 :=
  lt_of_le_of_lt (Complex.abs_re_le_norm _) (norm_f_lt_three D hz)

theorem re_f_ne_of_ne {i : Fin 3} {z w : ℂ} (hz : z ∈ σ.foldWall i) (hw : w ∈ σ.triangle)
    (hwr : (D.f w).im = 0) (hne : z ≠ w) : (D.f z).re ≠ (D.f w).re := by
  intro h
  apply hne
  apply D.bijOn_f.injOn hz.1 hw
  rw [f_eq_ofReal_re D hz, h]
  exact Complex.ext (by simp) (by simp [hwr])

def wallOneSet : Set ℂ := (fun y : ℝ => (σ.width : ℂ) + y * I) '' Ioi σ.vertexOne.im

theorem wallOneSet_eq : wallOneSet (σ := σ) = σ.foldWall 1 \ {σ.vertexOne} := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : σ.vertexOne.im < y := hy
    have hy0 : 0 < y := lt_trans σ.vertexOne_im_pos hy'
    refine ⟨⟨⟨by simpa using hy0, fun i => ?_⟩, ?_⟩, ?_⟩
    · fin_cases i
      · change 0 ≤ ((σ.width : ℂ) + y * I).re
        simpa using σ.width_pos.le
      · change 0 ≤ σ.width - ((σ.width : ℂ) + y * I).re
        simp
      · change 0 ≤ (((σ.width : ℂ) + y * I).re - σ.centre) ^ 2 + ((σ.width : ℂ) + y * I).im ^ 2
          - 1 / 16
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, add_im, mul_im, zero_add]
        rw [vertexOne_im] at hy'
        have := Real.sin_sq_add_cos_sq σ.θ₁
        have hs := σ.sin_θ₁_pos
        have hsq : (Real.sin σ.θ₁ / 4) ^ 2 < y ^ 2 := by nlinarith
        unfold width centre
        nlinarith
    · change σ.width - ((σ.width : ℂ) + y * I).re = 0
      simp
    · intro h
      have := congrArg Complex.im (h : (σ.width : ℂ) + y * I = σ.vertexOne)
      simp at this
      linarith [hy']
  · rintro ⟨⟨hT, h1⟩, hne⟩
    have hx : z.re = σ.width := by
      change σ.width - z.re = 0 at h1
      linarith
    have h2 := hT.2 2
    change 0 ≤ (z.re - σ.centre) ^ 2 + z.im ^ 2 - 1 / 16 at h2
    rw [hx] at h2
    have hs := σ.sin_θ₁_pos
    have hge : σ.vertexOne.im ≤ z.im := by
      rw [vertexOne_im]
      have := Real.sin_sq_add_cos_sq σ.θ₁
      unfold width centre at h2
      nlinarith [hT.1]
    have hlt : σ.vertexOne.im < z.im := by
      rcases hge.lt_or_eq with h | h
      · exact h
      · exact absurd (Complex.ext (by rw [hx, vertexOne_re]) h.symm) hne
    exact ⟨z.im, hlt, Complex.ext (by simp [hx]) (by simp)⟩

theorem isPreconnected_wallOneSet : IsPreconnected (wallOneSet (σ := σ)) :=
  isPreconnected_Ioi.image _
    (by fun_prop : Continuous fun y : ℝ => (σ.width : ℂ) + y * I).continuousOn

include hθ₁ in
theorem re_f_of_mem_foldWall_one {z : ℂ} (hz : z ∈ σ.foldWall 1) (hne : z ≠ σ.vertexOne) :
    3 / 2 < (D.f z).re ∧ (D.f z).re < 3 := by
  have hv1 : (D.f σ.vertexOne).im = 0 := by rw [f_vertexOne D hθ₁]; simp
  have hS := isPreconnected_wallOneSet (σ := σ)
  have hcont : ContinuousOn (fun w => (D.f w).re) (wallOneSet (σ := σ)) :=
    continuous_re.comp_continuousOn ((continuousOn_f D).mono (fun w hw => by
      rw [wallOneSet_eq] at hw; exact hw.1.1))
  have hmem : ∀ w ∈ wallOneSet (σ := σ), w ∈ σ.foldWall 1 ∧ w ≠ σ.vertexOne := fun w hw => by
    rw [wallOneSet_eq] at hw; exact ⟨hw.1, hw.2⟩
  obtain ⟨y₀, hy₀, hfy₀⟩ : ∃ y > σ.vertexOne.im,
      D.f ((σ.width : ℂ) + y * I) = σ.coneApexOne p₁ ((σ.width : ℂ) + y * I) := by
    have htend : Tendsto (fun y : ℝ => (σ.width : ℂ) + y * I) (𝓝[>] σ.vertexOne.im)
        (𝓝 σ.vertexOne) := by
      have hc : Continuous fun y : ℝ => (σ.width : ℂ) + y * I := by fun_prop
      have := hc.tendsto σ.vertexOne.im
      rw [show (σ.width : ℂ) + (σ.vertexOne.im : ℂ) * I = σ.vertexOne by
        apply Complex.ext <;> simp [vertexOne_re]] at this
      exact this.mono_left nhdsWithin_le_nhds
    obtain ⟨y, hy1, hy2⟩ := ((htend.eventually (D.f_apexOne p₁ hθ₁)).and
      self_mem_nhdsWithin).exists
    exact ⟨y, hy2, hy1⟩
  have hw₀ : (σ.width : ℂ) + y₀ * I ∈ wallOneSet (σ := σ) := ⟨y₀, hy₀, rfl⟩
  have hval : 3 / 2 < (D.f ((σ.width : ℂ) + y₀ * I)).re ∧
      (D.f ((σ.width : ℂ) + y₀ * I)).re < 3 := by
    rw [hfy₀, coneApexOne]
    have hy0 : 0 < y₀ := lt_trans σ.vertexOne_im_pos hy₀
    have hd := coneDisc_vertical_point σ.vertexOne y₀
    rw [vertexOne_re] at hd
    rw [hd]
    have hr0 : 0 < (y₀ - σ.vertexOne.im) / (y₀ + σ.vertexOne.im) := by
      apply div_pos <;> linarith [σ.vertexOne_im_pos]
    have hr1 : (y₀ - σ.vertexOne.im) / (y₀ + σ.vertexOne.im) < 1 := by
      rw [div_lt_one (by linarith [σ.vertexOne_im_pos])]
      linarith [σ.vertexOne_im_pos]
    have hp1 : ((y₀ - σ.vertexOne.im) / (y₀ + σ.vertexOne.im)) ^ p₁ ≤ 1 :=
      pow_le_one₀ hr0.le hr1.le
    have hp0 : 0 < ((y₀ - σ.vertexOne.im) / (y₀ + σ.vertexOne.im)) ^ p₁ := pow_pos hr0 _
    rw [← ofReal_pow]
    simp only [add_re, div_ofNat_re, ofReal_re]
    norm_num
    constructor <;> linarith
  have hres := TwoConeFold.preconnected_real_avoid hS (g := fun w => (D.f w).re) hcont
    (a := 3 / 2) (b := 3)
    (fun w hw => by
      obtain ⟨hw1, hw2⟩ := hmem w hw
      have := re_f_ne_of_ne D hw1 (vertexOne_mem_triangle' σ) hv1 hw2
      rwa [f_vertexOne D hθ₁, show ((3 / 2 : ℂ)).re = 3 / 2 by norm_num] at this)
    (fun w hw h => by
      have := re_f_lt_three D (hmem w hw).1.1
      rw [h] at this
      norm_num at this)
    hw₀ hval
  exact hres z (by rw [wallOneSet_eq]; exact ⟨hz, hne⟩)

def wallZeroSet : Set ℂ := (fun y : ℝ => (y : ℂ) * I) '' Ioi σ.vertexTwo.im

include hθ₂ in
theorem wallZeroSet_eq : wallZeroSet (σ := σ) = σ.foldWall 0 \ {σ.vertexTwo} := by
  have hs := Real.sin_pos_of_pos_of_lt_pi (θ₂_pos hθ₂) (by linarith [σ.θ₂_le, Real.pi_pos])
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : σ.vertexTwo.im < y := hy
    rw [vertexTwo_im] at hy'
    have hy0 : 0 < y := lt_trans (by positivity) hy'
    refine ⟨⟨⟨by simpa using hy0, fun i => ?_⟩, ?_⟩, ?_⟩
    · fin_cases i
      · change 0 ≤ ((y : ℂ) * I).re
        simp
      · change 0 ≤ σ.width - ((y : ℂ) * I).re
        simpa using σ.width_pos.le
      · change 0 ≤ (((y : ℂ) * I).re - σ.centre) ^ 2 + ((y : ℂ) * I).im ^ 2 - 1 / 16
        simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
          zero_sub, mul_im, add_zero]
        have := Real.sin_sq_add_cos_sq σ.θ₂
        have hsq : (Real.sin σ.θ₂ / 4) ^ 2 < y ^ 2 := by nlinarith
        unfold centre
        nlinarith
    · change ((y : ℂ) * I).re = 0
      simp
    · intro h
      have := congrArg Complex.im (h : (y : ℂ) * I = σ.vertexTwo)
      simp [vertexTwo_im] at this
      linarith
  · rintro ⟨⟨hT, h0⟩, hne⟩
    have hx : z.re = 0 := h0
    have h2 := hT.2 2
    change 0 ≤ (z.re - σ.centre) ^ 2 + z.im ^ 2 - 1 / 16 at h2
    rw [hx] at h2
    have hge : σ.vertexTwo.im ≤ z.im := by
      rw [vertexTwo_im]
      have := Real.sin_sq_add_cos_sq σ.θ₂
      unfold centre at h2
      nlinarith [hT.1]
    have hlt : σ.vertexTwo.im < z.im := by
      rcases hge.lt_or_eq with h | h
      · exact h
      · exact absurd (Complex.ext (by rw [hx, vertexTwo_re]) h.symm) hne
    exact ⟨z.im, hlt, Complex.ext (by simp [hx]) (by simp)⟩

theorem isPreconnected_wallZeroSet : IsPreconnected (wallZeroSet (σ := σ)) :=
  isPreconnected_Ioi.image _ (by fun_prop : Continuous fun y : ℝ => (y : ℂ) * I).continuousOn

include hθ₂ in
theorem re_f_of_mem_foldWall_zero {z : ℂ} (hz : z ∈ σ.foldWall 0) (hne : z ≠ σ.vertexTwo) :
    -3 < (D.f z).re ∧ (D.f z).re < -(3 / 2) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi (θ₂_pos hθ₂) (by linarith [σ.θ₂_le, Real.pi_pos])
  have hv2im : 0 < σ.vertexTwo.im := by rw [vertexTwo_im]; positivity
  have hv2 : (D.f σ.vertexTwo).im = 0 := by rw [f_vertexTwo D hθ₂]; simp
  have hS := isPreconnected_wallZeroSet (σ := σ)
  have hcont : ContinuousOn (fun w => (D.f w).re) (wallZeroSet (σ := σ)) :=
    continuous_re.comp_continuousOn ((continuousOn_f D).mono (fun w hw => by
      rw [wallZeroSet_eq hθ₂] at hw; exact hw.1.1))
  have hmem : ∀ w ∈ wallZeroSet (σ := σ), w ∈ σ.foldWall 0 ∧ w ≠ σ.vertexTwo := fun w hw => by
    rw [wallZeroSet_eq hθ₂] at hw; exact ⟨hw.1, hw.2⟩
  obtain ⟨y₀, hy₀, hfy₀⟩ : ∃ y > σ.vertexTwo.im,
      D.f ((y : ℂ) * I) = σ.coneApexTwo p₂ ((y : ℂ) * I) := by
    have htend : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝[>] σ.vertexTwo.im) (𝓝 σ.vertexTwo) := by
      have hc : Continuous fun y : ℝ => (y : ℂ) * I := by fun_prop
      have := hc.tendsto σ.vertexTwo.im
      rw [show (σ.vertexTwo.im : ℂ) * I = σ.vertexTwo by
        apply Complex.ext <;> simp [vertexTwo_re]] at this
      exact this.mono_left nhdsWithin_le_nhds
    obtain ⟨y, hy1, hy2⟩ := ((htend.eventually (D.f_apexTwo p₂ hθ₂)).and
      self_mem_nhdsWithin).exists
    exact ⟨y, hy2, hy1⟩
  have hw₀ : (y₀ : ℂ) * I ∈ wallZeroSet (σ := σ) := ⟨y₀, hy₀, rfl⟩
  have hval : -3 < (D.f ((y₀ : ℂ) * I)).re ∧ (D.f ((y₀ : ℂ) * I)).re < -(3 / 2) := by
    rw [hfy₀, coneApexTwo]
    have hd := coneDisc_vertical_point σ.vertexTwo y₀
    rw [vertexTwo_re, ofReal_zero, zero_add] at hd
    rw [hd]
    have hr0 : 0 < (y₀ - σ.vertexTwo.im) / (y₀ + σ.vertexTwo.im) := by
      apply div_pos <;> linarith
    have hr1 : (y₀ - σ.vertexTwo.im) / (y₀ + σ.vertexTwo.im) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    have hp1 : ((y₀ - σ.vertexTwo.im) / (y₀ + σ.vertexTwo.im)) ^ p₂ ≤ 1 :=
      pow_le_one₀ hr0.le hr1.le
    have hp0 : 0 < ((y₀ - σ.vertexTwo.im) / (y₀ + σ.vertexTwo.im)) ^ p₂ := pow_pos hr0 _
    rw [← ofReal_pow]
    simp only [sub_re, neg_re, div_ofNat_re, ofReal_re]
    norm_num
    constructor <;> linarith
  have hres := TwoConeFold.preconnected_real_avoid hS (g := fun w => (D.f w).re) hcont
    (a := -3) (b := -(3 / 2))
    (fun w hw h => by
      have := re_f_lt_three D (hmem w hw).1.1
      rw [h] at this
      norm_num at this)
    (fun w hw => by
      obtain ⟨hw1, hw2⟩ := hmem w hw
      have := re_f_ne_of_ne D hw1 (vertexTwo_mem_triangle' σ (θ₂_pos hθ₂)) hv2 hw2
      rwa [f_vertexTwo D hθ₂, show (-(3 / 2 : ℂ)).re = -(3 / 2) by norm_num] at this)
    hw₀ hval
  exact hres z (by rw [wallZeroSet_eq hθ₂]; exact ⟨hz, hne⟩)

def wallTwoSet : Set ℂ :=
  (fun φ : ℝ => (σ.centre : ℂ) + exp ((φ : ℂ) * I) / 4) '' Ioo σ.θ₁ (Real.pi - σ.θ₂)

include hθ₂ in
theorem wallTwoSet_eq :
    wallTwoSet (σ := σ) = σ.foldWall 2 \ {σ.vertexOne, σ.vertexTwo} := by
  have hθ₂0 := θ₂_pos hθ₂
  have hcosI : ∀ φ : ℝ, ((σ.centre : ℂ) + exp ((φ : ℂ) * I) / 4).re =
      σ.centre + Real.cos φ / 4 := fun φ => by
    simp [exp_ofReal_mul_I_re]
  have hsinI : ∀ φ : ℝ, ((σ.centre : ℂ) + exp ((φ : ℂ) * I) / 4).im = Real.sin φ / 4 :=
    fun φ => by simp [exp_ofReal_mul_I_im]
  have hanti := Real.strictAntiOn_cos
  have hθ₁mem : σ.θ₁ ∈ Icc 0 Real.pi := ⟨σ.θ₁_pos.le, by linarith [σ.θ₁_le, Real.pi_pos]⟩
  have hθ₂mem : Real.pi - σ.θ₂ ∈ Icc 0 Real.pi :=
    ⟨by linarith [σ.θ₂_le, Real.pi_pos], by linarith [σ.θ₂_nonneg]⟩
  ext z
  constructor
  · rintro ⟨φ, ⟨hφ1, hφ2⟩, rfl⟩
    have hφmem : φ ∈ Icc 0 Real.pi := ⟨by linarith [σ.θ₁_pos], by linarith⟩
    have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi (by linarith [σ.θ₁_pos])
      (by linarith)
    have hc1 : Real.cos φ < Real.cos σ.θ₁ := hanti hθ₁mem hφmem hφ1
    have hc2 : Real.cos (Real.pi - σ.θ₂) < Real.cos φ := hanti hφmem hθ₂mem hφ2
    rw [Real.cos_pi_sub] at hc2
    refine ⟨⟨⟨by rw [hsinI]; positivity, fun i => ?_⟩, ?_⟩, ?_⟩
    · fin_cases i
      · change 0 ≤ ((σ.centre : ℂ) + exp ((φ : ℂ) * I) / 4).re
        rw [hcosI]
        unfold centre
        linarith
      · change 0 ≤ σ.width - ((σ.centre : ℂ) + exp ((φ : ℂ) * I) / 4).re
        rw [hcosI]
        unfold width centre
        linarith
      · change 0 ≤ (((σ.centre : ℂ) + exp ((φ : ℂ) * I) / 4).re - σ.centre) ^ 2 +
          ((σ.centre : ℂ) + exp ((φ : ℂ) * I) / 4).im ^ 2 - 1 / 16
        rw [hcosI, hsinI]
        nlinarith [Real.sin_sq_add_cos_sq φ]
    · change (((σ.centre : ℂ) + exp ((φ : ℂ) * I) / 4).re - σ.centre) ^ 2 +
        ((σ.centre : ℂ) + exp ((φ : ℂ) * I) / 4).im ^ 2 - 1 / 16 = 0
      rw [hcosI, hsinI]
      nlinarith [Real.sin_sq_add_cos_sq φ]
    · rintro (h | h)
      · have := congrArg Complex.re h
        rw [hcosI, vertexOne_re] at this
        unfold width centre at this
        linarith
      · have := congrArg Complex.re h
        rw [hcosI, vertexTwo_re] at this
        unfold centre at this
        linarith
  · rintro ⟨⟨hT, h2⟩, hne⟩
    have hne1 : z ≠ σ.vertexOne := fun h => hne (Or.inl h)
    have hne2 : z ≠ σ.vertexTwo := fun h => hne (Or.inr h)
    have hn : normSq (z - σ.centre) = 1 / 16 := by
      have := σ.wallSide_two_eq z
      rw [h2] at this
      linarith
    have hnorm : ‖z - σ.centre‖ = 1 / 4 := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num), ← normSq_eq_norm_sq, hn]
      norm_num
    set φ := arg (z - σ.centre) with hφ
    have hrep : z = (σ.centre : ℂ) + exp ((φ : ℂ) * I) / 4 := by
      have := norm_mul_exp_arg_mul_I (z - σ.centre)
      rw [hnorm] at this
      rw [← hφ] at this
      push_cast at this
      linear_combination (-1 : ℂ) * this
    have him : 0 < (z - σ.centre).im := by simpa using hT.1
    have hφ0 : 0 < φ := lt_of_le_of_ne (arg_nonneg_iff.mpr him.le) (fun h => by
      have := (arg_eq_zero_iff.mp h.symm).2
      linarith)
    have hφπ : φ < Real.pi := by
      rcases (arg_le_pi (z - σ.centre)).lt_or_eq with h | h
      · exact h
      · have := arg_eq_pi_iff.mp h
        linarith [this.2]
    have hφmem : φ ∈ Icc 0 Real.pi := ⟨hφ0.le, hφπ.le⟩
    have hre : z.re = σ.centre + Real.cos φ / 4 := by
      conv_lhs => rw [hrep]
      exact hcosI φ
    have hw0 := hT.2 0
    have hw1 := hT.2 1
    change 0 ≤ z.re at hw0
    change 0 ≤ σ.width - z.re at hw1
    rw [hre] at hw0 hw1
    have hc1 : Real.cos φ ≤ Real.cos σ.θ₁ := by unfold width centre at hw1; linarith
    have hc2 : Real.cos (Real.pi - σ.θ₂) ≤ Real.cos φ := by
      rw [Real.cos_pi_sub]; unfold centre at hw0; linarith
    have hφ1 : σ.θ₁ ≤ φ := (hanti.le_iff_ge hφmem hθ₁mem).mp hc1
    have hφ2 : φ ≤ Real.pi - σ.θ₂ := (hanti.le_iff_ge hθ₂mem hφmem).mp hc2
    refine ⟨φ, ⟨lt_of_le_of_ne hφ1 fun h => hne1 ?_, lt_of_le_of_ne hφ2 fun h => hne2 ?_⟩,
      hrep.symm⟩
    · rw [hrep, ← h, vertexOne_eq]
    · rw [hrep, h, vertexTwo_eq]

theorem isPreconnected_wallTwoSet : IsPreconnected (wallTwoSet (σ := σ)) :=
  isPreconnected_Ioo.image _
    (by fun_prop : Continuous fun φ : ℝ => (σ.centre : ℂ) + exp ((φ : ℂ) * I) / 4).continuousOn

include hθ₁ in
theorem coneDisc_vertexOne_pow_of_wallTwo {z : ℂ} (hz : z ∈ σ.foldWall 2)
    (hx : z.re < σ.width) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ coneDisc σ.vertexOne z ^ p₁ = -((t ^ p₁ : ℝ) : ℂ) := by
  have hzim : 0 < z.im := hz.1.1
  have hc : z ≠ σ.centre := fun h => by
    have := congrArg Complex.im h
    simp at this
    linarith
  have hrefl : σ.refl 2 z = z := σ.refl_of_wallSide_eq_zero hzim hz.2
  have hη := σ.coneDisc_vertexOne_refl_two hc
  rw [hrefl] at hη
  set η := coneDisc σ.vertexOne z with hηdef
  set ρ := exp (-(σ.θ₁ * I)) * η with hρdef
  have hconj : conj ρ = ρ := by
    have e1 : conj ρ = exp (σ.θ₁ * I) * conj η := by
      rw [hρdef, map_mul, ← exp_conj]
      congr 2
      simp [conj_ofReal]
    rw [e1]
    conv_rhs => rw [hρdef, hη]
    rw [← mul_assoc, ← exp_add]
    congr 2
    ring
  have hρreal : ρ = (ρ.re : ℂ) := (conj_eq_iff_re.mp hconj).symm
  have hηρ : η = exp (σ.θ₁ * I) * ρ := by
    rw [hρdef, ← mul_assoc, ← exp_add]
    simp
  set t := ρ.re with ht
  have hηt : η = exp (σ.θ₁ * I) * (t : ℂ) := by rw [hηρ, ← hρreal]
  have hw1 : 0 < σ.wallSide 1 z := by
    change 0 < σ.width - z.re
    linarith
  have hnsq : 0 < normSq (z - conj σ.vertexOne) := normSq_sub_conj_pos σ.vertexOne_im_pos hzim
  have him : 0 < η.im := by
    have := σ.im_coneDisc_vertexOne_mul z
    rw [← hηdef] at this
    have hpos : 0 < 2 * σ.vertexOne.im * σ.wallSide 1 z := by
      have := σ.vertexOne_im_pos
      positivity
    rw [← this] at hpos
    exact pos_of_mul_pos_left hpos hnsq.le
  have hsin := σ.sin_θ₁_pos
  have htpos : 0 < t := by
    rw [hηt] at him
    have e : (exp ((σ.θ₁ : ℂ) * I) * (t : ℂ)).im = Real.sin σ.θ₁ * t := by
      simp [mul_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
    rw [e] at him
    exact pos_of_mul_pos_right him hsin.le
  have hnorm : ‖η‖ = t := by
    rw [hηt, norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_real, Real.norm_of_nonneg htpos.le]
  have ht1 : t < 1 := hnorm ▸ norm_coneDisc_lt_one σ.vertexOne_im_pos hzim
  refine ⟨t, htpos, ht1, ?_⟩
  rw [hηt, mul_pow, ← exp_nat_mul, ofReal_pow]
  have : (p₁ : ℂ) * ((σ.θ₁ : ℂ) * I) = ((σ.θ₁ * p₁ : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, hθ₁, exp_pi_mul_I]
  ring

include hθ₁ hθ₂ in
theorem re_f_of_mem_foldWall_two {z : ℂ} (hz : z ∈ σ.foldWall 2) (hne1 : z ≠ σ.vertexOne)
    (hne2 : z ≠ σ.vertexTwo) : -(3 / 2) < (D.f z).re ∧ (D.f z).re < 3 / 2 := by
  have hv1 : (D.f σ.vertexOne).im = 0 := by rw [f_vertexOne D hθ₁]; simp
  have hv2 : (D.f σ.vertexTwo).im = 0 := by rw [f_vertexTwo D hθ₂]; simp
  have hS := isPreconnected_wallTwoSet (σ := σ)
  have hmem : ∀ w ∈ wallTwoSet (σ := σ), w ∈ σ.foldWall 2 ∧ w ≠ σ.vertexOne ∧
      w ≠ σ.vertexTwo := fun w hw => by
    rw [wallTwoSet_eq hθ₂] at hw
    exact ⟨hw.1, fun h => hw.2 (Or.inl h), fun h => hw.2 (Or.inr h)⟩
  have hcont : ContinuousOn (fun w => (D.f w).re) (wallTwoSet (σ := σ)) :=
    continuous_re.comp_continuousOn ((continuousOn_f D).mono (fun w hw => (hmem w hw).1.1))
  have hlt : σ.θ₁ < Real.pi - σ.θ₂ := by linarith [σ.sum_lt]
  obtain ⟨φ₀, hφ₀, hfφ₀⟩ : ∃ φ ∈ Ioo σ.θ₁ (Real.pi - σ.θ₂),
      D.f ((σ.centre : ℂ) + exp ((φ : ℂ) * I) / 4) =
        σ.coneApexOne p₁ ((σ.centre : ℂ) + exp ((φ : ℂ) * I) / 4) := by
    have htend : Tendsto (fun φ : ℝ => (σ.centre : ℂ) + exp ((φ : ℂ) * I) / 4)
        (𝓝[>] σ.θ₁) (𝓝 σ.vertexOne) := by
      have hc : Continuous fun φ : ℝ => (σ.centre : ℂ) + exp ((φ : ℂ) * I) / 4 := by fun_prop
      have := hc.tendsto σ.θ₁
      rw [← vertexOne_eq] at this
      exact this.mono_left nhdsWithin_le_nhds
    obtain ⟨φ, hφ1, hφ2⟩ := ((htend.eventually (D.f_apexOne p₁ hθ₁)).and
      (Ioo_mem_nhdsGT hlt)).exists
    exact ⟨φ, hφ2, hφ1⟩
  have hw₀ : (σ.centre : ℂ) + exp ((φ₀ : ℂ) * I) / 4 ∈ wallTwoSet (σ := σ) := ⟨φ₀, hφ₀, rfl⟩
  have hval : -(3 / 2) < (D.f ((σ.centre : ℂ) + exp ((φ₀ : ℂ) * I) / 4)).re ∧
      (D.f ((σ.centre : ℂ) + exp ((φ₀ : ℂ) * I) / 4)).re < 3 / 2 := by
    obtain ⟨hw2, -, -⟩ := hmem _ hw₀
    have hx : ((σ.centre : ℂ) + exp ((φ₀ : ℂ) * I) / 4).re < σ.width := by
      have hre : ((σ.centre : ℂ) + exp ((φ₀ : ℂ) * I) / 4).re = σ.centre + Real.cos φ₀ / 4 := by
        simp [exp_ofReal_mul_I_re]
      have hc1 : Real.cos φ₀ < Real.cos σ.θ₁ :=
        Real.strictAntiOn_cos ⟨σ.θ₁_pos.le, by linarith [σ.θ₁_le, Real.pi_pos]⟩
          ⟨by linarith [σ.θ₁_pos, hφ₀.1], by linarith [hφ₀.2, σ.θ₂_nonneg]⟩ hφ₀.1
      rw [hre]
      unfold width centre
      linarith
    obtain ⟨t, ht0, ht1, hpow⟩ := coneDisc_vertexOne_pow_of_wallTwo hθ₁ hw2 hx
    rw [hfφ₀, coneApexOne, hpow]
    have htp : t ^ p₁ < 1 := pow_lt_one₀ ht0.le ht1 (p₁_ne_zero hθ₁)
    have htp0 : 0 < t ^ p₁ := pow_pos ht0 _
    simp only [add_re, div_ofNat_re, neg_re, ofReal_re]
    norm_num
    constructor <;> linarith
  have hres := TwoConeFold.preconnected_real_avoid hS (g := fun w => (D.f w).re) hcont
    (a := -(3 / 2)) (b := 3 / 2)
    (fun w hw => by
      obtain ⟨hw1, -, hw3⟩ := hmem w hw
      have := re_f_ne_of_ne D hw1 (vertexTwo_mem_triangle' σ (θ₂_pos hθ₂)) hv2 hw3
      rwa [f_vertexTwo D hθ₂, show (-(3 / 2 : ℂ)).re = -(3 / 2) by norm_num] at this)
    (fun w hw => by
      obtain ⟨hw1, hw2, -⟩ := hmem w hw
      have := re_f_ne_of_ne D hw1 (vertexOne_mem_triangle' σ) hv1 hw2
      rwa [f_vertexOne D hθ₁, show ((3 / 2 : ℂ)).re = 3 / 2 by norm_num] at this)
    hw₀ hval
  exact hres z (by rw [wallTwoSet_eq hθ₂]; exact ⟨hz, by rintro (h | h) <;> contradiction⟩)

theorem det_ne_zero {z : ℂ} (hz : z ∈ D.U) (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    (fderiv ℝ D.f z).det ≠ 0 :=
  (D.det_fderiv_pos z hz h1 h2).ne'

theorem exists_wall_of_im_f_eq_zero {z : ℂ} (hz : z ∈ σ.triangle) (him : (D.f z).im = 0) :
    ∃ i, σ.wallSide i z = 0 :=
  σ.exists_wall_of_im_eq_zero D.isOpen_U D.triangle_subset_U D.contDiffOn_f
    (fun _ hw h1 h2 => det_ne_zero D hw h1 h2) D.bijOn_f.mapsTo hz him

theorem im_f_pos_of_interior {z : ℂ} (hz : z ∈ σ.triangle) (hint : ∀ i, 0 < σ.wallSide i z) :
    0 < (D.f z).im := by
  have h0 : 0 ≤ (D.f z).im := (D.bijOn_f.mapsTo hz).2.1
  rcases h0.lt_or_eq with h | h
  · exact h
  · obtain ⟨i, hi⟩ := exists_wall_of_im_f_eq_zero D hz h.symm
    linarith [hint i]

end Fold

end TwoConeFold

end GC.Seifert
