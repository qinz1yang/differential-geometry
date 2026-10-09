import DifferentialGeometry.Geometry.Geodesic.ConformalPlane.StabilityRadiusSphereGM

/-!
# G3 consumer（O-W-GEO-MIN，后缀 `_GM`）：`σ = 1/2`（IMS06′ 的 neck band，`R ≥ 1/2`）

`radius_le_of_sphere_GM` 在 `σ = 1/2` 时的结论逐字是 S-W-NECK G4 `hIMS05` 的结论
`r ≤ 2 * π * √(2 / (3 * (1 / 2)))`，再经 O-IFACE G3 的数值事实 ⇒ `r < 8`
（IMS06′：半径 8 的内蕴球不能满足 IMS05′ 的全部前提）。
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff

namespace DifferentialGeometry.Geometry

/-- `σ = 1/2`：IMS05′ 的半径界，S-W-NECK `hIMS05` 的结论形状，并且 `< 8`。 -/
theorem radius_lt_eight_of_sphere_GM {Ω : Set ℂ} (hΩ : IsOpen Ω) {lam u q d : ℂ → ℝ}
    {μ : ℝ} (hlam : ContDiffOn ℝ ∞ lam Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hlam0 : ∀ z ∈ Ω, 0 < lam z) (hu0 : ∀ z ∈ Ω, 0 < u z) (hq : ContinuousOn q Ω)
    (hμ : 0 ≤ μ) (hd : ContinuousOn d Ω)
    (hseg : ∀ x y : ℂ, segment ℝ x y ⊆ Ω →
      d y ≤ d x + ∫ t in (0 : ℝ)..1, Real.sqrt (lam (x + t • (y - x))) * ‖y - x‖)
    {p : ℂ} (hp : p ∈ Ω) (hdp : d p = 0) {r : ℝ} (hr : 0 < r)
    (hK : IsCompact {z | z ∈ Ω ∧ d z ≤ r})
    (hqσ : ∀ z ∈ Ω, d z ≤ r → (1 / 2 : ℝ) / 2 ≤ q z)
    (hpde : ∀ z ∈ Ω, d z ≤ r → Laplacian.laplacian u z = lam z *
      (-Laplacian.laplacian (fun p => Real.log (lam p)) z / (2 * lam z) - q z - μ) * u z) :
    r ≤ 2 * Real.pi * Real.sqrt (2 / (3 * (1 / 2))) ∧ r < 8 := by
  have h := radius_le_of_sphere_GM (σ := 1 / 2) hΩ hlam hu hlam0 hu0 hq (by norm_num) hμ hd hseg
    hp hdp hr hK hqσ hpde
  exact ⟨h, h.trans_lt DifferentialGeometry.Analysis.two_pi_sqrt_two_div_three_half_lt_eight_IF⟩

end DifferentialGeometry.Geometry
