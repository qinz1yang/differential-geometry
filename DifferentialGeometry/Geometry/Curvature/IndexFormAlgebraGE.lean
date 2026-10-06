import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# 指标形式的逐点代数恒等式（S-W-GEO G2）

曲线 `c`（速度 `a = (a₁, a₂) = c′`，加速度 `b = (b₁, b₂) = c″`，`r = ‖a‖`，`r² = a₁² + a₂²`），
`ρ > 0`（`R = ρ(c)`，`g = Dρ(c)`，`h = D²ρ(c)` 的坐标），单位法向 `ν = (−a₂, a₁)/r`，
欧氏法向位移 `f`（`f₁ = f′`）。三个量：

* `d2`：变分场 `X = f ν` 的二阶变分被积函数（向量场形式，见 `WeightedLengthVariationGE`）；
* `d1`：变分场 `Y ν`（`Y = f² ρ_ν/ρ`）的一阶变分被积函数；
* `zp`：`(ρ_T f²)′`（`ρ_T = Dρ(c)(a)/r`）；
* `I`：指标形式被积函数 `ψ′²/(ρ r) + (r/ρ) Δ log ρ ψ²`，`ψ = ρ f`。

恒等式 `I = d2 + zp − d1`（模 `r² = a₁² + a₂²`）。证明：两边之差乘以 `R r⁹` 等于
`Q · (r² − a₁² − a₂²)`（纯 `ring` 恒等式，`Q` 为多项式）。
-/

set_option autoImplicit false

namespace DifferentialGeometry.Geometry

theorem index_identity_GE {a1 a2 b1 b2 r R g1 g2 h11 h12 h21 h22 f f1 Yp : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hr2 : r ^ 2 = a1 ^ 2 + a2 ^ 2) {d2 d1 zp I : ℝ}
    (hd2 : d2 = (f * (-a2 / r)) * (f * (-a2 / r)) * h11 * r +
      (f * (-a2 / r)) * (f * (a1 / r)) * h12 * r +
      (f * (a1 / r)) * (f * (-a2 / r)) * h21 * r + (f * (a1 / r)) * (f * (a1 / r)) * h22 * r +
      2 * (g1 * (f * (-a2 / r)) + g2 * (f * (a1 / r))) *
        ((a1 * (f1 * (-a2 / r) + f * (-b2 / r + (a1 * b1 + a2 * b2) / r * a2 / r ^ 2)) +
          a2 * (f1 * (a1 / r) + f * (b1 / r - (a1 * b1 + a2 * b2) / r * a1 / r ^ 2))) / r) +
      R * (((f1 * (-a2 / r) + f * (-b2 / r + (a1 * b1 + a2 * b2) / r * a2 / r ^ 2)) ^ 2 +
        (f1 * (a1 / r) + f * (b1 / r - (a1 * b1 + a2 * b2) / r * a1 / r ^ 2)) ^ 2) -
        ((a1 * (f1 * (-a2 / r) + f * (-b2 / r + (a1 * b1 + a2 * b2) / r * a2 / r ^ 2)) +
          a2 * (f1 * (a1 / r) + f * (b1 / r - (a1 * b1 + a2 * b2) / r * a1 / r ^ 2))) / r) ^ 2) /
        r)
    (hd1 : d1 = (g1 * (f ^ 2 * (g1 * (-a2 / r) + g2 * (a1 / r)) / R * (-a2 / r)) +
      g2 * (f ^ 2 * (g1 * (-a2 / r) + g2 * (a1 / r)) / R * (a1 / r))) * r +
      R * ((a1 * (Yp * (-a2 / r) + f ^ 2 * (g1 * (-a2 / r) + g2 * (a1 / r)) / R *
          (-b2 / r + (a1 * b1 + a2 * b2) / r * a2 / r ^ 2)) +
        a2 * (Yp * (a1 / r) + f ^ 2 * (g1 * (-a2 / r) + g2 * (a1 / r)) / R *
          (b1 / r - (a1 * b1 + a2 * b2) / r * a1 / r ^ 2))) / r))
    (hzp : zp = (h11 * a1 ^ 2 + (h12 + h21) * a1 * a2 + h22 * a2 ^ 2 + g1 * b1 + g2 * b2) *
        f ^ 2 / r + (g1 * a1 + g2 * a2) * (2 * f * f1) / r -
      (g1 * a1 + g2 * a2) * f ^ 2 * ((a1 * b1 + a2 * b2) / r) / r ^ 2)
    (hI : I = ((g1 * a1 + g2 * a2) * f + R * f1) ^ 2 / (R * r) +
      ((h11 + h22) / R - (g1 ^ 2 + g2 ^ 2) / R ^ 2) * R * r * f ^ 2) :
    I = d2 + zp - d1 := by
  have hr0 : r ≠ 0 := hr.ne'
  have hR0 : R ≠ 0 := hR.ne'
  have key : I - (d2 + zp - d1) =
      (r ^ 8 * (R * f ^ 2 * h11 + R * f ^ 2 * h22 - f ^ 2 * g1 ^ 2 - f ^ 2 * g2 ^ 2) +
        r ^ 6 * (R ^ 2 * f1 ^ 2 - R * b1 * f ^ 2 * g1 - R * b2 * f ^ 2 * g2) +
        r ^ 4 * (-2 * R ^ 2 * a1 * b1 * f * f1 - 2 * R ^ 2 * a2 * b2 * f * f1 -
          R ^ 2 * b1 ^ 2 * f ^ 2 - R ^ 2 * b2 ^ 2 * f ^ 2) +
        r ^ 2 * (R ^ 2 * a1 ^ 2 * b1 ^ 2 * f ^ 2 + 2 * R ^ 2 * a1 * a2 * b1 * b2 * f ^ 2 +
          R ^ 2 * a2 ^ 2 * b2 ^ 2 * f ^ 2)) * (r ^ 2 - a1 ^ 2 - a2 ^ 2) / (R * r ^ 9) := by
    rw [hI, hd2, hzp, hd1]
    field_simp
    ring
  have h0 : r ^ 2 - a1 ^ 2 - a2 ^ 2 = 0 := by linarith
  rw [h0, mul_zero, zero_div] at key
  linarith

end DifferentialGeometry.Geometry
