import DifferentialGeometry.Analysis.Elliptic.Planar.AnalyticNodalArcsR3AW

/-!
# R3a-ω（`_R3AW`）F4d：合同本体 `two_sheet_nodal_structure_analytic_R3AW`（G4）

平面实解析两片差 `w` 满足 smooth 系数齐次一致椭圆方程、在 `p` 处为零且芽非零 ⇒ `2k` 条 embedded
`C¹` half-arcs 的零点结构（含中心外 regular zeros）。证明 = G1 有限阶 + G2 主部调和（正规化坐标
`T Tᵀ = A(p)` 由 Cholesky 给出）+ G3 极坐标 IFT。不需要 SUCP；系数只要 `C^∞`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- G4（合同本体，R3a-ω）：平面实解析两片差 `w` 满足 smooth 系数齐次一致椭圆方程、在 `p` 处为零且芽非零 ⇒
`2k` 条 embedded `C¹` half-arcs 的零点结构（`IsNodalHalfArcsAt_R3AW`，已含中心外 regular zeros）。 -/
theorem two_sheet_nodal_structure_analytic_R3AW {O : Set ℂ} (hO : IsOpen O) {w : ℂ → ℝ}
    {a : Fin 2 → Fin 2 → ℂ → ℝ} {β : Fin 2 → ℂ → ℝ} {c : ℂ → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ ∞ (a i j) O) (hβ : ∀ i, ContDiffOn ℝ ∞ (β i) O)
    (hc : ContDiffOn ℝ ∞ c O) (hsymm : ∀ i j y, a i j y = a j i y)
    (hell : ∀ y ∈ O, ∀ ξ : Fin 2 → ℝ, ξ ≠ 0 → 0 < ∑ i, ∑ j, a i j y * ξ i * ξ j)
    (hwa : AnalyticOnNhd ℝ w O)
    (heq : ∀ y ∈ O, ∑ i, ∑ j, a i j y *
        iteratedFDeriv ℝ 2 w y ![planeBasisR3AW i, planeBasisR3AW j] +
      ∑ i, β i y * fderiv ℝ w y (planeBasisR3AW i) + c y * w y = 0)
    {p : ℂ} (hp : p ∈ O) (hz : w p = 0) (hnz : ¬ (w =ᶠ[𝓝 p] 0)) :
    IsNodalHalfArcsAt_R3AW O a w p := by
  obtain ⟨k, hk, hjet, hjk⟩ := analytic_finite_order_R3AW (hwa p hp) hz hnz
  have hA : ∀ i j, ContDiffAt ℝ ∞ (a i j) p := fun i j => (ha i j).contDiffAt (hO.mem_nhds hp)
  have hβ' : ∀ i, ContDiffAt ℝ ∞ (β i) p := fun i => (hβ i).contDiffAt (hO.mem_nhds hp)
  have hc' : ContDiffAt ℝ ∞ c p := hc.contDiffAt (hO.mem_nhds hp)
  have heq' := Filter.eventually_of_mem (hO.mem_nhds hp) heq
  -- `A(p)` 正定对称
  have h00 : 0 < a 0 0 p := by
    have := hell p hp ![1, 0] (by
      intro h
      have := congrFun h 0
      simp at this)
    simpa [Fin.sum_univ_two] using this
  have hdet : 0 < a 0 0 p * a 1 1 p - a 0 1 p ^ 2 := by
    have hξ : (![-(a 0 1 p), a 0 0 p] : Fin 2 → ℝ) ≠ 0 := by
      intro h
      exact h00.ne' (by simpa using congrFun h 1)
    have h1 := hell p hp _ hξ
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    rw [hsymm 1 0 p] at h1
    have h2 : a 0 0 p * (a 0 0 p * a 1 1 p - a 0 1 p ^ 2) > 0 := by nlinarith [h1]
    exact (mul_pos_iff_of_pos_left h00).mp h2
  obtain ⟨T, hT1, hT2⟩ := exists_normalizing_equiv_R3AW (fun i j => a i j p) (hsymm 1 0 p) h00 hdet
  obtain ⟨θ₀, A₀, hA₀, hsin⟩ := principal_part_harmonic_R3AW hk (hwa p hp) hA hβ' hc' heq' hjet
    hjk T hT1
  exact nodal_half_arcs_R3AW hO hwa hp hk hjet hjk T hT2 hA₀ hsin

end DifferentialGeometry.Analysis

end
