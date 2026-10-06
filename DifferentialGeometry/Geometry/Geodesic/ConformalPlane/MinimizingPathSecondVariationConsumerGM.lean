import DifferentialGeometry.Geometry.Geodesic.ConformalPlane.MinimizingPathSecondVariationGM

/-!
# G2 consumer（O-W-GEO-MIN，后缀 `_GM`）

把 G1（`exists_minimizing_path_to_sphere_GM`）与 G2（`second_variation_nonneg_of_minimizing_GM`、
`variation_mem_ball_GM`）接起来：内蕴球面的极小路径 `c` 对**每个** `C¹` 固定端点变分 `c + εX`，
`ε ↦ ℓ_ĝ(c + εX)` 在 `0` 取局部极小、二阶变分 `≥ 0`，且支撑在 `[0, a]`（`a < L`）的变分在 `[0, L)`
上不碰 `S_r`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry

theorem exists_sphere_minimizer_second_variation_GM {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {lam u d : ℂ → ℝ} (hlam : ContDiffOn ℝ ∞ lam Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hlam0 : ∀ z ∈ Ω, 0 < lam z) (hu0 : ∀ z ∈ Ω, 0 < u z) (hd : ContinuousOn d Ω)
    (hseg : ∀ x y : ℂ, segment ℝ x y ⊆ Ω →
      d y ≤ d x + ∫ t in (0 : ℝ)..1, Real.sqrt (lam (x + t • (y - x))) * ‖y - x‖)
    {p : ℂ} (hp : p ∈ Ω) (hdp : d p = 0) {r : ℝ} (hr : 0 < r)
    (hK : IsCompact {z | z ∈ Ω ∧ d z ≤ r}) :
    ∃ (c : ℝ → ℂ) (L : ℝ), c 0 = p ∧ d (c L) = r ∧ r ≤ L ∧
      ∀ X : ℝ → ℂ, ContDiff ℝ 1 X → X 0 = 0 → X L = 0 →
        IsLocalMin (fun ε : ℝ => ∫ s in (0 : ℝ)..L,
          u (c s + ε • X s) * Real.sqrt (lam (c s + ε • X s)) *
            ‖deriv c s + ε • deriv X s‖) 0 ∧
        0 ≤ ∫ s in (0 : ℝ)..L,
          (fderiv ℝ (fderiv ℝ (fun z => u z * Real.sqrt (lam z))) (c s) (X s) (X s) *
              ‖deriv c s‖ +
            2 * fderiv ℝ (fun z => u z * Real.sqrt (lam z)) (c s) (X s) *
              (inner ℝ (deriv c s) (deriv X s) / ‖deriv c s‖) +
            u (c s) * Real.sqrt (lam (c s)) *
              ((‖deriv X s‖ ^ 2 - (inner ℝ (deriv c s) (deriv X s) / ‖deriv c s‖) ^ 2) /
                ‖deriv c s‖)) ∧
        ∀ a < L, (∀ s ∈ Icc a L, X s = 0) → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Icc (-ε₀) ε₀,
          ∀ s ∈ Ico 0 L, c s + ε • X s ∈ Ω ∧ d (c s + ε • X s) < r := by
  obtain ⟨c, L, ρt, V, hV, hKV, hVΩ, -, -, hρtV, -, hc, hreg, hc0, hcL, hrL, hcK, hfirst,
    -, hmin⟩ := exists_minimizing_path_to_sphere_GM hΩ hlam hu hlam0 hu0 hd hseg hp hdp hr hK
  have hL : 0 ≤ L := hr.le.trans hrL
  have hc1 : ContDiff ℝ 1 c := hc.of_le (by simp)
  have hcV : ∀ s ∈ Icc 0 L, c s ∈ V := fun s hs => hKV (hcK s hs)
  have hloc := weightedLength_le_local_GM hρtV hL hcV hmin
  refine ⟨c, L, hc0, hcL, hrL, fun X hX hX0 hXL => ?_⟩
  obtain ⟨-, hlm, -, h2⟩ := second_variation_nonneg_of_minimizing_GM (ρ := fun z =>
    u z * Real.sqrt (lam z)) hV (fun _ => rfl) ((hu.mono hVΩ).of_le (by simp))
    ((hlam.mono hVΩ).of_le (by simp)) (fun z hz => hlam0 z (hVΩ hz)) hL hc1 hcV
    (fun s _ => hreg s) hloc hX hX0 hXL
  refine ⟨hlm, h2, fun a haL hXa => ?_⟩
  exact variation_mem_ball_GM hΩ hd haL hc1 hX (fun s _ => hreg s)
    (fun s hs => ⟨(hcK s (Ico_subset_Icc_self hs)).1, hfirst s hs⟩) hXa |>.imp
    fun ε₀ h => ⟨h.1, fun ε hε => (h.2 ε hε).1⟩

end DifferentialGeometry.Geometry
