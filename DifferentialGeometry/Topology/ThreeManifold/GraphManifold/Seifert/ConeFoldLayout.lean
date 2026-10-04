import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldFermi

/-!
# The layout of the cone fold: exact certificates

Lane A4, layout of the errata after review 15 to the design
`docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, in the Fermi chart
`ζ = fermiChart z` of the circle wall (`SF/ConeFoldFermi.lean`), `ζ = -ξ + iY`, `ξ ≥ 0` on the
triangle, `sinh n = ξ/Y`. Parameters: `λ = 21/20`, lens `0 < ξ < βY` with `β = 1/10`, switch windows
`βY ≤ ξ ≤ β'Y` with `β' = 7/50`, wall-2 band `ξ < βY/8`. The cone discs are
`regionOne t ζ < 0` (`1 + t|ζ|² < (1/λ + λt) Y`, the disc `η₁ < √K/λ`) and `regionTwo t ζ < 0`
(`|ζ|² + t < (1/λ + λt) Y`), for the uniform parameters `t ∈ [0, 2/3]` of all admissible shapes.
The Jordan core is the Euclidean disc of the chart centred at `coreCentre = -201/1000 + 993/1000 i`
with inner radius `33/200` and outer radius `9/50` (a hyperbolic disc; it replaces the Fermi
description of the errata, same position up to `10⁻³`).

Certificates (all exact, rational, uniform in `t₁, t₂ ∈ [0, 2/3]`):
* (J3) `lens_mem_core`: a point of the lens boundary `ξ = βY` in the triangle (so
  `t₁|ζ|² ≤ 1 ≤ |ζ|²/t₂`) outside both cone discs lies in the inner core;
* (J1/J2) `windowOne_mem_core`, `windowTwo_mem_core`: the switch windows of `∂R₁`, `∂R₂` lie in the
  inner core;
* (J4) `core_band`: the closed outer core lies in `βY/8 < ξ` (off the wall-2 band);
  `core_wallOne_pos`, `core_wallZero_pos`: for admissible shapes (`cos θᵢ = 0` or `≥ 1/2`, i.e.
  orders `pᵢ ≥ 2` or a cusp) the closed outer core lies strictly inside the triangle's walls 1, 0;
* (J5, windows before walls) `window_before_wallOne`, `window_before_wallTwo`:
  `2λβ'√t < sin θ (1 - λ²t)`, squared, i.e. `β' < sinh D sin θ` for the cone-disc radius `D`.

The method: monotonicity of the cone discs in `t` (they are nested, decreasing in `t`), a ray
argument (`regionOne_ray_le`, `regionTwo_ray_ge`) which bounds a point of the lens or of a window
on its ray by an explicit rational point inside the disc for `t = 2/3`, and convexity of the disc
condition along rays and horizontals (`quad_lt_of_endpoints`, `box_lt`).
-/

set_option autoImplicit false

noncomputable section

open Complex

namespace GC.Seifert

namespace ConeLayout

def coreCentre : ℂ := ⟨-(201 / 1000), 993 / 1000⟩

def coreInner : ℝ := 33 / 200

def coreOuter : ℝ := 9 / 50

def lensWidth : ℝ := 1 / 10

def windowEnd : ℝ := 7 / 50

def regionOne (t : ℝ) (ζ : ℂ) : ℝ := 1 + t * normSq ζ - (20 / 21 + 21 / 20 * t) * ζ.im

def regionTwo (t : ℝ) (ζ : ℂ) : ℝ := normSq ζ + t - (20 / 21 + 21 / 20 * t) * ζ.im

theorem quad_lt_of_endpoints {α β γ a b x M : ℝ} (hα : 0 ≤ α) (hax : a ≤ x) (hxb : x ≤ b)
    (ha : α * a ^ 2 + β * a + γ < M) (hb : α * b ^ 2 + β * b + γ < M) :
    α * x ^ 2 + β * x + γ < M := by
  rcases eq_or_lt_of_le (hax.trans hxb) with h | h
  · have : x = a := le_antisymm (h ▸ hxb) hax
    rw [this]
    exact ha
  · have h1 : 0 ≤ x - a := sub_nonneg.2 hax
    have h2 : 0 ≤ b - x := sub_nonneg.2 hxb
    have key : (b - a) * (α * x ^ 2 + β * x + γ - M) =
        (b - x) * (α * a ^ 2 + β * a + γ - M) + (x - a) * (α * b ^ 2 + β * b + γ - M) -
          α * (b - a) * ((x - a) * (b - x)) := by ring
    have h3 : (b - x) * (α * a ^ 2 + β * a + γ - M) +
        (x - a) * (α * b ^ 2 + β * b + γ - M) < 0 := by
      rcases eq_or_lt_of_le h1 with h4 | h4
      · have : b - x > 0 := by linarith
        nlinarith
      · nlinarith
    have h5 : 0 ≤ α * (b - a) * ((x - a) * (b - x)) := by
      apply mul_nonneg (mul_nonneg hα (by linarith)) (mul_nonneg h1 h2)
    have h6 : (b - a) * (α * x ^ 2 + β * x + γ - M) < 0 := by linarith
    have h7 : α * x ^ 2 + β * x + γ - M < 0 := by
      by_contra hc
      have : 0 ≤ (b - a) * (α * x ^ 2 + β * x + γ - M) :=
        mul_nonneg (by linarith) (not_lt.1 hc)
      linarith
    linarith

theorem ray_quad_lt {m ξ₀ y₀ M a b Y : ℝ} (hab : a ≤ Y) (hb : Y ≤ b)
    (ha : (m * a - ξ₀) ^ 2 + (a - y₀) ^ 2 < M) (hb' : (m * b - ξ₀) ^ 2 + (b - y₀) ^ 2 < M) :
    (m * Y - ξ₀) ^ 2 + (Y - y₀) ^ 2 < M := by
  have e : ∀ u : ℝ, (m * u - ξ₀) ^ 2 + (u - y₀) ^ 2 =
      (1 + m ^ 2) * u ^ 2 + (-2 * (m * ξ₀ + y₀)) * u + (ξ₀ ^ 2 + y₀ ^ 2) := fun u => by ring
  rw [e] at ha hb' ⊢
  exact quad_lt_of_endpoints (by positivity) hab hb ha hb'

theorem box_lt {m₀ m₁ Y₀ Y₁ ξ₀ y₀ M : ℝ}
    (h00 : (m₀ * Y₀ - ξ₀) ^ 2 + (Y₀ - y₀) ^ 2 < M) (h01 : (m₀ * Y₁ - ξ₀) ^ 2 + (Y₁ - y₀) ^ 2 < M)
    (h10 : (m₁ * Y₀ - ξ₀) ^ 2 + (Y₀ - y₀) ^ 2 < M) (h11 : (m₁ * Y₁ - ξ₀) ^ 2 + (Y₁ - y₀) ^ 2 < M)
    {m Y : ℝ} (hm0 : m₀ ≤ m) (hm1 : m ≤ m₁) (hY0 : Y₀ ≤ Y) (hY1 : Y ≤ Y₁) :
    (m * Y - ξ₀) ^ 2 + (Y - y₀) ^ 2 < M := by
  have hA := ray_quad_lt hY0 hY1 h00 h01
  have hB := ray_quad_lt hY0 hY1 h10 h11
  have e : ∀ u : ℝ, (u * Y - ξ₀) ^ 2 + (Y - y₀) ^ 2 =
      Y ^ 2 * u ^ 2 + (-2 * ξ₀ * Y) * u + (ξ₀ ^ 2 + (Y - y₀) ^ 2) := fun u => by ring
  rw [e] at hA hB ⊢
  exact quad_lt_of_endpoints (sq_nonneg Y) hm0 hm1 hA hB

theorem regionOne_ray_le {t m m₁ Yh Y : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 2 / 3) (hYh : 21 / 20 ≤ Yh)
    (hneg : 1 + 2 / 3 * (1 + m₁ ^ 2) * Yh ^ 2 - 347 / 210 * Yh < 0) (hm0 : 0 ≤ m) (hm : m ≤ m₁)
    (hY : 0 < Y) (hR : 0 ≤ 1 + t * (1 + m ^ 2) * Y ^ 2 - (20 / 21 + 21 / 20 * t) * Y)
    (h1 : t * (1 + m ^ 2) * Y ^ 2 ≤ 1) : Y ≤ Yh := by
  have hB : 1 ≤ 1 + m ^ 2 := by nlinarith
  have hq : 1 + t * (1 + m ^ 2) * Yh ^ 2 - (20 / 21 + 21 / 20 * t) * Yh < 0 := by
    have e1 : 0 ≤ (1 + m ^ 2) * Yh ^ 2 - 21 / 20 * Yh := by nlinarith
    have e2 : (1 + m ^ 2) * Yh ^ 2 ≤ (1 + m₁ ^ 2) * Yh ^ 2 := by
      have : m ^ 2 ≤ m₁ ^ 2 := by nlinarith
      nlinarith
    nlinarith
  by_contra hc
  have hlt : Yh < Y := not_le.1 hc
  have hYh0 : 0 < Yh := by linarith
  set B := 1 + m ^ 2 with hBdef
  set A := 20 / 21 + 21 / 20 * t with hA
  have k1 : Y + t * B * Yh ^ 2 * Y < A * Yh * Y := by nlinarith
  have k2 : A * Y * Yh ≤ Yh + t * B * Y ^ 2 * Yh := by nlinarith
  have k3 : (Y - Yh) * 1 < (Y - Yh) * (t * B * Y * Yh) := by nlinarith
  have k4 : 1 < t * B * Y * Yh := lt_of_mul_lt_mul_left k3 (by linarith)
  have k5 : t * B * Y * Yh ≤ t * B * Y * Y := by
    apply mul_le_mul_of_nonneg_left hlt.le
    have : 0 ≤ t * B := mul_nonneg ht0 (by linarith)
    positivity
  nlinarith

theorem regionTwo_ray_ge {t m m₁ Yh Y : ℝ} (ht : t ≤ 2 / 3) (hYh : Yh ≤ 20 / 21)
    (hYh0 : 0 < Yh) (hneg : (1 + m₁ ^ 2) * Yh ^ 2 + 2 / 3 - 347 / 210 * Yh < 0) (hm0 : 0 ≤ m)
    (hm : m ≤ m₁) (hY : 0 < Y) (hR : 0 ≤ (1 + m ^ 2) * Y ^ 2 + t - (20 / 21 + 21 / 20 * t) * Y)
    (h2 : t ≤ (1 + m ^ 2) * Y ^ 2) : Yh ≤ Y := by
  have hq : (1 + m ^ 2) * Yh ^ 2 + t - (20 / 21 + 21 / 20 * t) * Yh < 0 := by
    have e1 : 0 ≤ 1 - 21 / 20 * Yh := by linarith
    have e2 : (1 + m ^ 2) * Yh ^ 2 ≤ (1 + m₁ ^ 2) * Yh ^ 2 := by
      have : m ^ 2 ≤ m₁ ^ 2 := by nlinarith
      nlinarith
    nlinarith
  by_contra hc
  have hlt : Y < Yh := not_le.1 hc
  set B := 1 + m ^ 2 with hBdef
  set A := 20 / 21 + 21 / 20 * t with hA
  have hB : 1 ≤ B := by nlinarith
  have k1 : B * Yh ^ 2 * Y + t * Y < A * Yh * Y := by nlinarith
  have k2 : A * Y * Yh ≤ B * Y ^ 2 * Yh + t * Yh := by nlinarith
  have k3 : (Yh - Y) * (B * Y * Yh) < (Yh - Y) * t := by nlinarith
  have k4 : B * Y * Yh < t := lt_of_mul_lt_mul_left k3 (by linarith)
  have k5 : B * Y * Y ≤ B * Y * Yh := by
    apply mul_le_mul_of_nonneg_left hlt.le
    positivity
  nlinarith

theorem regionOne_boundary_ge {t m Y : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 2 / 3) (hY : 0 < Y)
    (hR : 1 + t * (1 + m ^ 2) * Y ^ 2 - (20 / 21 + 21 / 20 * t) * Y = 0) : 21 / 20 ≤ Y := by
  by_contra hc
  have hlt : Y < 21 / 20 := not_le.1 hc
  have e0 : (1 - 20 / 21 * Y) * (1 - 21 / 20 * t * Y) = -(t * m ^ 2 * Y ^ 2) := by
    linear_combination hR
  have e : (1 - 20 / 21 * Y) * (1 - 21 / 20 * t * Y) ≤ 0 := by
    rw [e0]
    have : 0 ≤ t * m ^ 2 * Y ^ 2 := by positivity
    linarith
  have h1 : 0 < 1 - 20 / 21 * Y := by linarith
  have h2 : 0 < 1 - 21 / 20 * t * Y := by nlinarith
  nlinarith

theorem regionTwo_boundary_le {t m Y : ℝ} (ht : t ≤ 2 / 3) (hY : 0 < Y)
    (hR : (1 + m ^ 2) * Y ^ 2 + t - (20 / 21 + 21 / 20 * t) * Y = 0) : Y ≤ 20 / 21 := by
  by_contra hc
  have hlt : 20 / 21 < Y := not_le.1 hc
  have e0 : (Y - 20 / 21) * (Y - 21 / 20 * t) = -(m ^ 2 * Y ^ 2) := by
    linear_combination hR
  have e : (Y - 20 / 21) * (Y - 21 / 20 * t) ≤ 0 := by
    rw [e0]
    have : 0 ≤ m ^ 2 * Y ^ 2 := by positivity
    linarith
  have h2 : 0 < Y - 21 / 20 * t := by linarith
  nlinarith

theorem normSq_sub_coreCentre (ζ : ℂ) :
    normSq (ζ - coreCentre) = (-ζ.re - 201 / 1000) ^ 2 + (ζ.im - 993 / 1000) ^ 2 := by
  simp [normSq_apply, coreCentre]
  ring

theorem chart_coords {ζ : ℂ} (hY : 0 < ζ.im) :
    -ζ.re = (-ζ.re / ζ.im) * ζ.im ∧ normSq ζ = (1 + (-ζ.re / ζ.im) ^ 2) * ζ.im ^ 2 := by
  constructor
  · field_simp
  · rw [normSq_apply]
    field_simp
    ring

theorem lens_mem_core {t₁ t₂ : ℝ} (ht₁0 : 0 ≤ t₁) (ht₁ : t₁ ≤ 2 / 3) (ht₂ : t₂ ≤ 2 / 3) {ζ : ℂ}
    (hY : 0 < ζ.im) (hL : -ζ.re = lensWidth * ζ.im)
    (h1 : t₁ * normSq ζ ≤ 1) (h2 : t₂ ≤ normSq ζ) (hR1 : 0 ≤ regionOne t₁ ζ)
    (hR2 : 0 ≤ regionTwo t₂ ζ) : normSq (ζ - coreCentre) < coreInner ^ 2 := by
  have hn : normSq ζ = (1 + (1 / 10) ^ 2) * ζ.im ^ 2 := by
    rw [normSq_apply]
    have : ζ.re = -(1 / 10 * ζ.im) := by rw [lensWidth] at hL; linarith
    rw [this]
    ring
  rw [regionOne, hn] at hR1
  rw [regionTwo, hn] at hR2
  rw [hn] at h1 h2
  have hup : ζ.im ≤ 109 / 100 :=
    regionOne_ray_le (m := 1 / 10) (m₁ := 1 / 10) ht₁0 ht₁ (by norm_num) (by norm_num)
      (by norm_num) le_rfl hY (by linarith) (by linarith)
  have hlo : 91 / 100 ≤ ζ.im :=
    regionTwo_ray_ge (m := 1 / 10) (m₁ := 1 / 10) ht₂ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) le_rfl hY (by linarith) (by linarith)
  rw [normSq_sub_coreCentre, hL, coreInner, lensWidth]
  exact ray_quad_lt hlo hup (by norm_num) (by norm_num)

theorem windowOne_mem_core {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 2 / 3) {ζ : ℂ} (hY : 0 < ζ.im)
    (hm0 : lensWidth * ζ.im ≤ -ζ.re) (hm1 : -ζ.re ≤ windowEnd * ζ.im)
    (hR : regionOne t ζ = 0) (h1 : t * normSq ζ ≤ 1) :
    normSq (ζ - coreCentre) < coreInner ^ 2 := by
  obtain ⟨hx, hn⟩ := chart_coords hY
  set m := -ζ.re / ζ.im with hm
  have hmlo : 1 / 10 ≤ m := by
    rw [hm, le_div_iff₀ hY]
    rw [lensWidth] at hm0
    linarith
  have hmhi : m ≤ 7 / 50 := by
    rw [hm, div_le_iff₀ hY]
    rw [windowEnd] at hm1
    linarith
  rw [regionOne, hn] at hR
  rw [hn] at h1
  have hR' : 0 ≤ 1 + t * (1 + m ^ 2) * ζ.im ^ 2 - (20 / 21 + 21 / 20 * t) * ζ.im := by
    linarith
  have hlow : 21 / 20 ≤ ζ.im := regionOne_boundary_ge (m := m) ht0 ht hY (by linarith)
  rw [normSq_sub_coreCentre, hx, coreInner]
  rcases le_total m (11 / 100) with h11 | h11
  · have hup : ζ.im ≤ 1094 / 1000 :=
      regionOne_ray_le ht0 ht (by norm_num) (by norm_num) (by linarith) h11 hY hR' (by linarith)
    exact box_lt (m₀ := 1 / 10) (m₁ := 11 / 100) (Y₀ := 21 / 20) (Y₁ := 1094 / 1000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hmlo h11 hlow hup
  rcases le_total m (12 / 100) with h12 | h12
  · have hup : ζ.im ≤ 1105 / 1000 :=
      regionOne_ray_le ht0 ht (by norm_num) (by norm_num) (by linarith) h12 hY hR' (by linarith)
    exact box_lt (m₀ := 11 / 100) (m₁ := 12 / 100) (Y₀ := 21 / 20) (Y₁ := 1105 / 1000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) h11 h12 hlow hup
  rcases le_total m (13 / 100) with h13 | h13
  · have hup : ζ.im ≤ 1119 / 1000 :=
      regionOne_ray_le ht0 ht (by norm_num) (by norm_num) (by linarith) h13 hY hR' (by linarith)
    exact box_lt (m₀ := 12 / 100) (m₁ := 13 / 100) (Y₀ := 21 / 20) (Y₁ := 1119 / 1000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) h12 h13 hlow hup
  · have hup : ζ.im ≤ 1138 / 1000 :=
      regionOne_ray_le ht0 ht (by norm_num) (by norm_num) (by linarith) hmhi hY hR' (by linarith)
    exact box_lt (m₀ := 13 / 100) (m₁ := 7 / 50) (Y₀ := 21 / 20) (Y₁ := 1138 / 1000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) h13 hmhi hlow hup

theorem windowTwo_mem_core {t : ℝ} (ht : t ≤ 2 / 3) {ζ : ℂ} (hY : 0 < ζ.im)
    (hm0 : lensWidth * ζ.im ≤ -ζ.re) (hm1 : -ζ.re ≤ windowEnd * ζ.im)
    (hR : regionTwo t ζ = 0) (h2 : t ≤ normSq ζ) :
    normSq (ζ - coreCentre) < coreInner ^ 2 := by
  obtain ⟨hx, hn⟩ := chart_coords hY
  set m := -ζ.re / ζ.im with hm
  have hmlo : 1 / 10 ≤ m := by
    rw [hm, le_div_iff₀ hY]
    rw [lensWidth] at hm0
    linarith
  have hmhi : m ≤ 7 / 50 := by
    rw [hm, div_le_iff₀ hY]
    rw [windowEnd] at hm1
    linarith
  rw [regionTwo, hn] at hR
  rw [hn] at h2
  have hR' : 0 ≤ (1 + m ^ 2) * ζ.im ^ 2 + t - (20 / 21 + 21 / 20 * t) * ζ.im := by linarith
  have hhigh : ζ.im ≤ 20 / 21 := regionTwo_boundary_le (m := m) ht hY (by linarith)
  rw [normSq_sub_coreCentre, hx, coreInner]
  rcases le_total m (11 / 100) with h11 | h11
  · have hlo : 903 / 1000 ≤ ζ.im :=
      regionTwo_ray_ge ht (by norm_num) (by norm_num) (by norm_num) (by linarith) h11 hY hR'
        (by linarith)
    exact box_lt (m₀ := 1 / 10) (m₁ := 11 / 100) (Y₀ := 903 / 1000) (Y₁ := 20 / 21)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hmlo h11 hlo hhigh
  rcases le_total m (12 / 100) with h12 | h12
  · have hlo : 892 / 1000 ≤ ζ.im :=
      regionTwo_ray_ge ht (by norm_num) (by norm_num) (by norm_num) (by linarith) h12 hY hR'
        (by linarith)
    exact box_lt (m₀ := 11 / 100) (m₁ := 12 / 100) (Y₀ := 892 / 1000) (Y₁ := 20 / 21)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) h11 h12 hlo hhigh
  rcases le_total m (13 / 100) with h13 | h13
  · have hlo : 879 / 1000 ≤ ζ.im :=
      regionTwo_ray_ge ht (by norm_num) (by norm_num) (by norm_num) (by linarith) h13 hY hR'
        (by linarith)
    exact box_lt (m₀ := 12 / 100) (m₁ := 13 / 100) (Y₀ := 879 / 1000) (Y₁ := 20 / 21)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) h12 h13 hlo hhigh
  · have hlo : 862 / 1000 ≤ ζ.im :=
      regionTwo_ray_ge ht (by norm_num) (by norm_num) (by norm_num) (by linarith) hmhi hY
        hR' (by linarith)
    exact box_lt (m₀ := 13 / 100) (m₁ := 7 / 50) (Y₀ := 862 / 1000) (Y₁ := 20 / 21)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) h13 hmhi hlo hhigh

theorem core_band {ζ : ℂ} (h : normSq (ζ - coreCentre) ≤ coreOuter ^ 2) :
    lensWidth / 8 * ζ.im < -ζ.re := by
  rw [normSq_sub_coreCentre, coreOuter] at h
  rw [lensWidth]
  nlinarith [sq_nonneg (ζ.im - 993 / 1000 + (-ζ.re - 201 / 1000) / 80)]

theorem core_facts {ζ : ℂ} (h : normSq (ζ - coreCentre) ≤ coreOuter ^ 2) :
    normSq ζ < 1425 / 1000 ∧ 694 / 1000 < normSq ζ ∧ normSq ζ - 18 / 11 * -ζ.re > 3 / 10 ∧
      normSq ζ + 18 / 11 * -ζ.re < 1901 / 1000 ∧ normSq ζ - 9 / 11 * -ζ.re > 52 / 100 ∧
      -ζ.re ≤ 2 / 5 ∧ 0 ≤ -ζ.re := by
  rw [normSq_sub_coreCentre, coreOuter] at h
  have hN : normSq ζ = (-ζ.re) ^ 2 + ζ.im ^ 2 := by
    rw [normSq_apply]
    ring
  rw [hN]
  set ξ := -ζ.re
  set Y := ζ.im
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [sq_nonneg (45 / 8 * (ξ - 201 / 1000) - 201 / 1000),
      sq_nonneg (45 / 8 * (Y - 993 / 1000) - 993 / 1000)]
  · nlinarith [sq_nonneg (8 / 45 * (201 / 1000) + (ξ - 201 / 1000)),
      sq_nonneg (8 / 45 * (993 / 1000) + (Y - 993 / 1000))]
  · nlinarith [sq_nonneg (2 / 13 * (201 / 1000 - 9 / 11) + (ξ - 201 / 1000)),
      sq_nonneg (2 / 13 * (993 / 1000) + (Y - 993 / 1000))]
  · nlinarith [sq_nonneg (79 / 10 * (ξ - 201 / 1000) - (201 / 1000 + 9 / 11)),
      sq_nonneg (79 / 10 * (Y - 993 / 1000) - 993 / 1000)]
  · nlinarith [sq_nonneg (8 / 45 * (201 / 1000 - 9 / 22) + (ξ - 201 / 1000)),
      sq_nonneg (8 / 45 * (993 / 1000) + (Y - 993 / 1000))]
  · nlinarith [sq_nonneg (Y - 993 / 1000)]
  · nlinarith [sq_nonneg (Y - 993 / 1000)]

theorem half_le_of_add_pos {c₁ c₂ : ℝ} (h₂ : c₂ = 0 ∨ 1 / 2 ≤ c₂) (hsum : 0 < c₁ + c₂)
    (h1 : c₁ = 0) : 1 / 2 ≤ c₂ := by
  rcases h₂ with h | h
  · rw [h1, h] at hsum
    norm_num at hsum
  · exact h

theorem core_wallOne_pos (σ : ConeShape) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
    (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂) {ζ : ℂ}
    (h : normSq (ζ - coreCentre) ≤ coreOuter ^ 2) : 0 < σ.wallOneChart ζ := by
  obtain ⟨hN1, -, hN3, hN4, -, hξ, hξ0⟩ := core_facts h
  have hk := σ.chartScale_pos
  have hkk := σ.chartScale_sq_mul
  have hc1 := σ.cos_θ₁_nonneg
  have hc1' := σ.cos_θ₁_lt_one
  have hc2 := σ.cos_θ₂_nonneg
  have hsum := σ.cos_add_cos_pos
  rw [ConeShape.wallOneChart]
  set c₁ := Real.cos σ.θ₁
  set c₂ := Real.cos σ.θ₂
  set k := σ.chartScale
  set ξ := -ζ.re
  have hre : ζ.re = -ξ := by simp [ξ]
  rw [hre]
  rcases h₁ with h0 | hhalf
  · have := half_le_of_add_pos h₂ hsum h0
    rw [h0]
    nlinarith
  · have hA : 2 * k * c₁ * ξ ≤ c₂ + 18 / 11 * c₁ * ξ := by
      rcases le_total k (9 / 11) with hk9 | hk9
      · have : 0 ≤ c₁ * ξ := mul_nonneg hc1 hξ0
        nlinarith
      · have hd : 0 ≤ k - 9 / 11 := by linarith
        have e1 : c₁ * ξ * (2 * k - 18 / 11) ≤ 2 / 5 * c₁ * (2 * k - 18 / 11) := by
          have : 0 ≤ c₁ * (2 * k - 18 / 11) := mul_nonneg hc1 (by linarith)
          nlinarith
        have e2 : 2 / 5 * c₁ * (2 * k - 18 / 11) ≤ c₂ := by
          have : c₂ = k ^ 2 * (1 + c₁) - 1 := by linarith
          rw [this]
          nlinarith [mul_nonneg hd hd, mul_nonneg hd hc1]
        nlinarith
    have hB : 0 ≤ normSq ζ - 18 / 11 * ξ := by linarith
    nlinarith [mul_nonneg (sub_nonneg.2 hhalf) hB]

theorem core_wallZero_pos (σ : ConeShape) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
    (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂) {ζ : ℂ}
    (h : normSq (ζ - coreCentre) ≤ coreOuter ^ 2) : 0 < σ.wallZeroChart ζ := by
  obtain ⟨-, hN2, -, -, hN5, hξ, hξ0⟩ := core_facts h
  have hk := σ.chartScale_pos
  have hkk := σ.chartScale_sq_mul
  have hc1 := σ.cos_θ₁_nonneg
  have hc2 := σ.cos_θ₂_nonneg
  have hc2' := σ.cos_θ₂_le_one
  have hsum := σ.cos_add_cos_pos
  rw [ConeShape.wallZeroChart]
  set c₁ := Real.cos σ.θ₁
  set c₂ := Real.cos σ.θ₂
  set k := σ.chartScale
  set ξ := -ζ.re
  have hre : ζ.re = -ξ := by simp [ξ]
  rw [hre]
  rcases h₂ with h0 | hhalf
  · have hc1h : 1 / 2 ≤ c₁ := by
      rcases h₁ with h | h
      · rw [h, h0] at hsum
        norm_num at hsum
      · exact h
    rw [h0] at hkk ⊢
    have : k ^ 2 ≤ 2 / 3 := by nlinarith
    nlinarith
  · have hk2 : k ^ 2 ≤ 1 + c₂ := by nlinarith
    have hk9 : k ≤ 9 / 11 * (1 + c₂) := by
      have : k ^ 2 ≤ (9 / 11 * (1 + c₂)) ^ 2 := by nlinarith
      nlinarith
    have e1 : 2 * k * c₂ * ξ ≤ 18 / 11 * (1 + c₂) * c₂ * ξ := by
      have : 0 ≤ c₂ * ξ := mul_nonneg hc2 hξ0
      nlinarith
    have e2 : k ^ 2 * (1 - c₂) ≤ (1 + c₂) * (1 - c₂) := by
      apply mul_le_mul_of_nonneg_right hk2 (by linarith)
    have e3 : 0 < normSq ζ - 18 / 11 * c₂ * ξ - (1 - c₂) := by
      have : 0 ≤ 1 - 18 / 11 * ξ := by linarith
      nlinarith [mul_nonneg (sub_nonneg.2 hhalf) this]
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 + c₂) e3]

theorem window_before_wall_aux {c t s2 : ℝ} (hc : c = 0 ∨ 1 / 2 ≤ c) (hc1 : c < 1)
    (hs : s2 = 1 - c ^ 2) (ht0 : 0 < t) (hcase0 : c = 0 → t ≤ 2 / 3) (hcase1 : t ≤ 1 - c) :
    (21 / 20) ^ 2 * t < 1 ∧
      4 * (21 / 20) ^ 2 * (7 / 50) ^ 2 * t < s2 * (1 - (21 / 20) ^ 2 * t) ^ 2 := by
  rcases hc with h0 | hh
  · have ht := hcase0 h0
    rw [hs, h0]
    constructor
    · nlinarith
    · nlinarith
  · have ht : t ≤ 1 / 2 := by linarith
    have hpos : 0 < 1 - c := by linarith
    have hlow : 1 - (21 / 20) ^ 2 / 2 ≤ 1 - (21 / 20) ^ 2 * t := by nlinarith
    constructor
    · nlinarith
    · rw [hs]
      have e : (1 - c ^ 2) = (1 - c) * (1 + c) := by ring
      rw [e]
      have h1 : (1 - (21 / 20) ^ 2 / 2) ^ 2 ≤ (1 - (21 / 20) ^ 2 * t) ^ 2 := by
        have : 0 ≤ 1 - (21 / 20) ^ 2 / 2 := by norm_num
        nlinarith
      have h2 : 3 / 2 * (1 - c) ≤ (1 - c) * (1 + c) := by nlinarith
      have h3 : 4 * (21 / 20) ^ 2 * (7 / 50) ^ 2 * t ≤
          4 * (21 / 20) ^ 2 * (7 / 50) ^ 2 * (1 - c) := by
        nlinarith
      have h4 : 0 ≤ (1 - c) * (1 + c) := by nlinarith
      nlinarith [mul_le_mul h2 h1 (by positivity) h4]

theorem window_before_wallOne (σ : ConeShape) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
    (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂) :
    (21 / 20) ^ 2 * σ.tOne < 1 ∧
      4 * (21 / 20) ^ 2 * (7 / 50) ^ 2 * σ.tOne <
        Real.sin σ.θ₁ ^ 2 * (1 - (21 / 20) ^ 2 * σ.tOne) ^ 2 := by
  have hc2 := σ.cos_θ₂_nonneg
  have hc1 := σ.cos_θ₁_lt_one
  have hsum := σ.cos_add_cos_pos
  have h2pos := σ.one_add_cos_θ₂_pos
  refine window_before_wall_aux h₁ hc1 (by linarith [Real.sin_sq_add_cos_sq σ.θ₁]) σ.tOne_pos
    (fun h0 => ?_) ?_
  · have := half_le_of_add_pos h₂ hsum h0
    rw [ConeShape.tOne, h0, div_le_iff₀ h2pos]
    linarith
  · rw [ConeShape.tOne, div_le_iff₀ h2pos]
    nlinarith

theorem window_before_wallTwo (σ : ConeShape) (hθ : 0 < σ.θ₂)
    (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
    (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂) :
    (21 / 20) ^ 2 * σ.tTwo < 1 ∧
      4 * (21 / 20) ^ 2 * (7 / 50) ^ 2 * σ.tTwo <
        Real.sin σ.θ₂ ^ 2 * (1 - (21 / 20) ^ 2 * σ.tTwo) ^ 2 := by
  have hc1 := σ.cos_θ₁_nonneg
  have hc2 : Real.cos σ.θ₂ < 1 := by
    have hs := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [σ.θ₂_le, Real.pi_pos])
    have h := Real.sin_sq_add_cos_sq σ.θ₂
    by_contra hh
    have : Real.cos σ.θ₂ = 1 := le_antisymm (Real.cos_le_one _) (not_lt.1 hh)
    rw [this] at h
    nlinarith
  have hsum := σ.cos_add_cos_pos
  have h1pos := σ.one_add_cos_θ₁_pos
  have ht0 : 0 < σ.tTwo := by
    rw [ConeShape.tTwo]
    apply div_pos <;> linarith
  refine window_before_wall_aux h₂ hc2 (by linarith [Real.sin_sq_add_cos_sq σ.θ₂]) ht0
    (fun h0 => ?_) ?_
  · have : 1 / 2 ≤ Real.cos σ.θ₁ := by
      rcases h₁ with h | h
      · rw [h, h0] at hsum
        norm_num at hsum
      · exact h
    rw [ConeShape.tTwo, h0, div_le_iff₀ h1pos]
    linarith
  · rw [ConeShape.tTwo, div_le_iff₀ h1pos]
    nlinarith

end ConeLayout

end GC.Seifert
