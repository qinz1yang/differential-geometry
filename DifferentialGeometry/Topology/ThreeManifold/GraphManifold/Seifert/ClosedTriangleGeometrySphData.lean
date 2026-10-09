import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryData
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSpec

/-!
# Closed triangle blocks with positive orbifold Euler characteristic

Lane B3d (design `docs/geometrization/handoffs/20261004-design-b3d-spherical-row.md`, §0–§1).
For a closed triangle block with `0 < orbChi` the model is `.spherical`
(`closedConnectionModel_of_sph`) and the hole orders give CF's spherical shape `closedSphShape`
(cone `j` at hole `j`, the outer cone third). The signed fibre step is
`sphStep = π orbChi / e` (`e = euler ≠ 0`), so the closing equation `sphStep · e = π orbChi` holds
(`sphStep_mul_euler`). The spherical triples are, up to order, `(2, 2, n)`, `(2, 3, 3)`,
`(2, 3, 4)`, `(2, 3, 5)`; in each case `D = p₂p₃ + p₁p₃ + p₁p₂ - p₁p₂p₃` divides `2 pᵢ pⱼ`
(`sph_dvd`), hence `2e/orbChi` is an integer and the Hopf fibre length is an integer multiple of the
step:
`2π = n · sphStep` with `n ≠ 0` (`exists_two_pi_eq_mul_sphStep`).
-/

set_option autoImplicit false

noncomputable section

open GC.Geometry GC.Endpoint

universe u

namespace GC.Seifert

namespace SeifertData

variable (d : SeifertData)

theorem closedConnectionModel_of_sph (hχ : 0 < d.orbChi) :
    d.closedConnectionModel = .spherical := by
  simp [closedConnectionModel, hχ]

end SeifertData

namespace SeifertBlockCharts

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)

theorem one_lt_sum_inv_holeOrder_of_sph (hχ : 0 < d.orbChi) :
    1 < (1 / (C.holeOrder hc h3 1 : ℝ) + 1 / C.holeOrder hc h3 2 + 1 / C.holeOrder hc h3 0) := by
  have h := C.orbChi_eq_holes hc h3
  rw [Fin.sum_univ_three] at h
  have hq : 1 < (1 / (C.holeOrder hc h3 1 : ℚ) + 1 / C.holeOrder hc h3 2 +
      1 / C.holeOrder hc h3 0) := by linarith
  have := (Rat.cast_lt (K := ℝ)).2 hq
  push_cast at this
  exact this

def closedSphShape (hχ : 0 < d.orbChi) : CompactShape where
  curv := .spherical
  p₁ := C.holeOrder hc h3 1
  p₂ := C.holeOrder hc h3 2
  p₃ := C.holeOrder hc h3 0
  two_le_p₁ := C.two_le_holeOrder hc h3 1
  two_le_p₂ := C.two_le_holeOrder hc h3 2
  two_le_p₃ := C.two_le_holeOrder hc h3 0
  angle_cond := Or.inr (Or.inr ⟨rfl, C.one_lt_sum_inv_holeOrder_of_sph hc h3 hχ⟩)

theorem closedSphShape_curv (hχ : 0 < d.orbChi) :
    (C.closedSphShape hc h3 hχ).curv = .spherical := rfl

end SeifertBlockCharts

namespace ClosedTriangle

namespace Sph

theorem sph_dvd_aux {b c : ℤ} (hb : 2 ≤ b) (hc : 2 ≤ c) (h : b * c < 2 * b + 2 * c) :
    (2 * b + 2 * c - b * c) ∣ 2 * b * c ∧ (2 * b + 2 * c - b * c) ∣ 4 * c ∧
      (2 * b + 2 * c - b * c) ∣ 4 * b := by
  rcases eq_or_lt_of_le hb with rfl | hb3
  · refine ⟨⟨c, by ring⟩, ⟨c, by ring⟩, ⟨2, by ring⟩⟩
  rcases eq_or_lt_of_le hc with rfl | hc3
  · refine ⟨⟨b, by ring⟩, ⟨2, by ring⟩, ⟨b, by ring⟩⟩
  have hb5 : b ≤ 5 := by nlinarith
  have hc5 : c ≤ 5 := by nlinarith
  interval_cases b <;> interval_cases c <;> omega

theorem sph_dvd {a b c : ℤ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (h : a * b * c < b * c + a * c + a * b) :
    (b * c + a * c + a * b - a * b * c) ∣ 2 * b * c ∧
      (b * c + a * c + a * b - a * b * c) ∣ 2 * a * c ∧
        (b * c + a * c + a * b - a * b * c) ∣ 2 * a * b := by
  have htwo : a = 2 ∨ b = 2 ∨ c = 2 := by
    by_cases ha2 : a = 2
    · exact Or.inl ha2
    by_cases hb2 : b = 2
    · exact Or.inr (Or.inl hb2)
    by_cases hc2 : c = 2
    · exact Or.inr (Or.inr hc2)
    exfalso
    have ha3 : 3 ≤ a := by omega
    have hb3 : 3 ≤ b := by omega
    have hc3 : 3 ≤ c := by omega
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 ha3) (by omega : (0 : ℤ) ≤ b))
        (by omega : (0 : ℤ) ≤ c),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hb3) (by omega : (0 : ℤ) ≤ a))
        (by omega : (0 : ℤ) ≤ c),
      mul_nonneg (mul_nonneg (sub_nonneg.2 hc3) (by omega : (0 : ℤ) ≤ a))
        (by omega : (0 : ℤ) ≤ b)]
  rcases htwo with rfl | rfl | rfl
  · obtain ⟨h1, h2, h3⟩ := sph_dvd_aux hb hc (by linarith)
    have e : b * c + 2 * c + 2 * b - 2 * b * c = 2 * b + 2 * c - b * c := by ring
    rw [e]
    exact ⟨h1, by rw [show 2 * 2 * c = 4 * c by ring]; exact h2,
      by rw [show 2 * 2 * b = 4 * b by ring]; exact h3⟩
  · obtain ⟨h1, h2, h3⟩ := sph_dvd_aux ha hc (by linarith)
    have e : 2 * c + a * c + a * 2 - a * 2 * c = 2 * a + 2 * c - a * c := by ring
    rw [e]
    exact ⟨by rw [show 2 * 2 * c = 4 * c by ring]; exact h2, h1,
      by rw [show 2 * a * 2 = 4 * a by ring]; exact h3⟩
  · obtain ⟨h1, h2, h3⟩ := sph_dvd_aux ha hb (by linarith)
    have e : b * 2 + a * 2 + a * b - a * b * 2 = 2 * a + 2 * b - a * b := by ring
    rw [e]
    exact ⟨by rw [show 2 * b * 2 = 4 * b by ring]; exact h2,
      by rw [show 2 * a * 2 = 4 * a by ring]; exact h3, h1⟩

variable (d : SeifertData)

def sphStep : ℝ := Real.pi * (d.orbChi : ℝ) / (d.euler : ℝ)

variable {d}

theorem euler_ne_zero_of_sph (hc : d.ports = 0) (h3 : d.cones.length = 3) (hχ : 0 < d.orbChi) :
    (d.euler : ℝ) ≠ 0 :=
  Rat.cast_ne_zero.2 (d.euler_ne_zero_of_three_cones hc h3 hχ)

theorem sphStep_mul_euler (hc : d.ports = 0) (h3 : d.cones.length = 3) (hχ : 0 < d.orbChi) :
    sphStep d * d.euler = Real.pi * d.orbChi := by
  rw [sphStep, div_mul_cancel₀ _ (euler_ne_zero_of_sph hc h3 hχ)]

theorem sphStep_ne_zero (hc : d.ports = 0) (h3 : d.cones.length = 3) (hχ : 0 < d.orbChi) :
    sphStep d ≠ 0 := by
  have hχ' : (0 : ℝ) < d.orbChi := Rat.cast_pos.2 hχ
  rw [sphStep]
  exact div_ne_zero (mul_ne_zero Real.pi_pos.ne' hχ'.ne') (euler_ne_zero_of_sph hc h3 hχ)

theorem exists_two_pi_eq_mul_sphStep {W : CompactCarrier.{u}} (C : SeifertBlockCharts W d)
    (hc : d.ports = 0) (h3 : d.cones.length = 3) (hχ : 0 < d.orbChi) :
    ∃ n : ℤ, n ≠ 0 ∧ 2 * Real.pi = n * sphStep d := by
  set a : ℕ := C.holeOrder hc h3 0
  set b : ℕ := C.holeOrder hc h3 1
  set c : ℕ := C.holeOrder hc h3 2
  have ha := C.two_le_holeOrder hc h3 0
  have hb := C.two_le_holeOrder hc h3 1
  have hcc := C.two_le_holeOrder hc h3 2
  have hO := C.orbChi_eq_holes hc h3
  have hE := C.euler_eq_holes hc h3
  rw [Fin.sum_univ_three] at hO hE
  have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hcR : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have hOR : (d.orbChi : ℝ) = 1 / a + 1 / b + 1 / c - 1 := by
    rw [hO]
    push_cast
    rfl
  have hER : (d.euler : ℝ) = -((C.holeTwist hc h3 0 : ℝ) / a + (C.holeTwist hc h3 1 : ℝ) / b +
      (C.holeTwist hc h3 2 : ℝ) / c) := by
    rw [hE]
    push_cast
    rfl
  have hχR : (0 : ℝ) < d.orbChi := Rat.cast_pos.2 hχ
  have hlt : (a : ℤ) * b * c < b * c + a * c + a * b := by
    rw [hOR] at hχR
    have h1 : (0 : ℝ) < (b * c + a * c + a * b - a * b * c) / (a * b * c) := by
      rw [show ((b : ℝ) * c + a * c + a * b - a * b * c) / (a * b * c) =
        1 / a + 1 / b + 1 / c - 1 by field_simp]
      exact hχR
    have h2 : (0 : ℝ) < b * c + a * c + a * b - a * b * c :=
      (div_pos_iff_of_pos_right (by positivity)).1 h1
    have h3 : ((a : ℤ) : ℝ) * b * c < b * c + a * c + a * b := by push_cast; linarith
    exact_mod_cast h3
  obtain ⟨⟨k₀, hk₀⟩, ⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩⟩ := sph_dvd (by omega : (2 : ℤ) ≤ a)
    (by omega : (2 : ℤ) ≤ b) (by omega : (2 : ℤ) ≤ c) hlt
  set Dz : ℤ := b * c + a * c + a * b - a * b * c with hDz
  refine ⟨-(C.holeTwist hc h3 0 * k₀ + C.holeTwist hc h3 1 * k₁ + C.holeTwist hc h3 2 * k₂),
    ?_, ?_⟩
  · intro hn
    have he := euler_ne_zero_of_sph hc h3 hχ
    apply he
    rw [hER]
    have hD : (Dz : ℝ) ≠ 0 := by
      have : (0 : ℤ) < Dz := by rw [hDz]; linarith
      exact_mod_cast this.ne'
    have hk₀R : (2 : ℝ) * b * c = Dz * k₀ := by exact_mod_cast hk₀
    have hk₁R : (2 : ℝ) * a * c = Dz * k₁ := by exact_mod_cast hk₁
    have hk₂R : (2 : ℝ) * a * b = Dz * k₂ := by exact_mod_cast hk₂
    have hnR : ((C.holeTwist hc h3 0 : ℝ) * k₀ + (C.holeTwist hc h3 1 : ℝ) * k₁ +
        (C.holeTwist hc h3 2 : ℝ) * k₂) = 0 := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hn
      push_cast at this
      linarith
    field_simp
    have e : (Dz : ℝ) * ((C.holeTwist hc h3 0 : ℝ) * k₀ + (C.holeTwist hc h3 1 : ℝ) * k₁ +
        (C.holeTwist hc h3 2 : ℝ) * k₂) = 2 * ((C.holeTwist hc h3 0 : ℝ) * b * c +
          (C.holeTwist hc h3 1 : ℝ) * a * c + (C.holeTwist hc h3 2 : ℝ) * a * b) := by
      linear_combination (C.holeTwist hc h3 0 : ℝ) * hk₀R.symm +
        (C.holeTwist hc h3 1 : ℝ) * hk₁R.symm + (C.holeTwist hc h3 2 : ℝ) * hk₂R.symm
    rw [hnR, mul_zero] at e
    linear_combination e / 2
  · have he := euler_ne_zero_of_sph hc h3 hχ
    have hk₀R : (2 : ℝ) * b * c = Dz * k₀ := by exact_mod_cast hk₀
    have hk₁R : (2 : ℝ) * a * c = Dz * k₁ := by exact_mod_cast hk₁
    have hk₂R : (2 : ℝ) * a * b = Dz * k₂ := by exact_mod_cast hk₂
    have hDR : (Dz : ℝ) = b * c + a * c + a * b - a * b * c := by rw [hDz]; push_cast; ring
    set q₀ : ℝ := (C.holeTwist hc h3 0 : ℝ)
    set q₁ : ℝ := (C.holeTwist hc h3 1 : ℝ)
    set q₂ : ℝ := (C.holeTwist hc h3 2 : ℝ)
    set S : ℝ := q₀ * k₀ + q₁ * k₁ + q₂ * k₂ with hS
    have hO'' : (d.orbChi : ℝ) * (a * b * c) = Dz := by
      rw [hOR, hDR]
      field_simp
    have hE'' : (d.euler : ℝ) * (a * b * c) = -(q₀ * b * c + q₁ * a * c + q₂ * a * b) := by
      rw [hER]
      field_simp
    have hkey : ((d.orbChi : ℝ) * S + 2 * d.euler) * (a * b * c) = 0 := by
      linear_combination S * hO'' + 2 * hE'' - (q₀ * hk₀R + q₁ * hk₁R + q₂ * hk₂R)
    have habc : (a : ℝ) * b * c ≠ 0 := by positivity
    have hkey' : (d.orbChi : ℝ) * S + 2 * d.euler = 0 :=
      (mul_eq_zero.1 hkey).resolve_right habc
    rw [sphStep, mul_div_assoc', eq_div_iff he]
    push_cast
    linear_combination Real.pi * hkey'

end Sph

end ClosedTriangle

end GC.Seifert
