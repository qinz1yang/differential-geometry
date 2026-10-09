import DifferentialGeometry.Geometry.Geodesic.ConformalPlane.MinimizingPathSphereGM

/-!
# G1 consumer（O-W-GEO-MIN，后缀 `_GM`）：平坦情形的实例化

`lam = u = 1`、`Ω = ball p R`、`d = ‖· − p‖`（Euclidean 距离，线段 Lipschitz 即三角不等式）：
`exists_minimizing_path_to_sphere_local_GM`（从而主定理 `exists_minimizing_path_to_sphere_GM`）
的全部前提可满足（非空洞），结论给出从 `p` 到半径 `r` 的 Euclidean 球面的单位速度光滑路径，长度 `L ≥ r`，且在 `U₀` 内同端点的 `C¹` 曲线中最短。
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff

namespace DifferentialGeometry.Geometry

theorem exists_minimizing_path_euclidean_GM {p : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ (c : ℝ → ℂ) (L : ℝ) (U₀ : Set ℂ), IsOpen U₀ ∧ closedBall p r ⊆ U₀ ∧
      ContDiff ℝ ∞ c ∧ c 0 = p ∧ ‖c L - p‖ = r ∧ r ≤ L ∧
      (∀ s ∈ Icc 0 L, ‖deriv c s‖ = 1) ∧
      (∀ η : ℝ → ℂ, ContDiff ℝ 1 η → (∀ s ∈ Icc 0 L, η s ∈ U₀) → η 0 = c 0 → η L = c L →
        ∫ s in (0 : ℝ)..L, ‖deriv c s‖ ≤ ∫ s in (0 : ℝ)..L, ‖deriv η s‖) := by
  have hball : {z | z ∈ ball p R ∧ ‖z - p‖ ≤ r} = closedBall p r := by
    ext z
    simp only [mem_ofPred_eq, mem_ball, mem_closedBall, dist_eq_norm]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.trans_lt hrR, h⟩
  have hK : IsCompact {z | z ∈ ball p R ∧ ‖z - p‖ ≤ r} := by
    rw [hball]
    exact isCompact_closedBall p r
  have hseg : ∀ x y : ℂ, segment ℝ x y ⊆ ball p R →
      ‖y - p‖ ≤ ‖x - p‖ + ∫ t in (0 : ℝ)..1,
        Real.sqrt ((fun _ : ℂ => (1 : ℝ)) (x + t • (y - x))) * ‖y - x‖ := by
    intro x y _
    simp only [Real.sqrt_one, one_mul, intervalIntegral.integral_const, sub_zero, one_smul]
    linarith [norm_sub_le_norm_sub_add_norm_sub y x p]
  obtain ⟨c, L, U₀, hU, hKU, -, hc, hc0, hcL, hrL, -, -, harc, hmin⟩ :=
    exists_minimizing_path_to_sphere_local_GM (Ω := ball p R) isOpen_ball
      (lam := fun _ => 1) (u := fun _ => 1) (d := fun z => ‖z - p‖)
      contDiffOn_const contDiffOn_const (fun _ _ => one_pos) (fun _ _ => one_pos)
      (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
      hseg (mem_ball_self (hr.trans hrR)) (by simp) hr hK
  refine ⟨c, L, U₀, hU, hball ▸ hKU, hc, hc0, hcL, hrL, fun s hs => ?_, fun η hη hηU h0 hL => ?_⟩
  · have h := harc s hs
    simp only [one_mul] at h
    have h0 : 0 ≤ ‖deriv c s‖ := norm_nonneg _
    nlinarith
  · have h := hmin η hη hηU h0 hL
    simpa only [Real.sqrt_one, mul_one, one_mul] using h

end DifferentialGeometry.Geometry
