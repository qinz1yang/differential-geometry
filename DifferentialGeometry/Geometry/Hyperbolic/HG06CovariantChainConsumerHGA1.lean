import DifferentialGeometry.Geometry.Hyperbolic.HG06CovariantChainHGA1
import DifferentialGeometry.Geometry.Hyperbolic.HG06AdapterHGA

/-!
# HG-A1 consumer（S-HG-A1，后缀 `_HGA1`）

四个 `example`：

1. ch12 当前 `hHG06` binder **逐字**（从 dg-ch12 `Comparison_O46.lean` 机械抽取；
   `StepCore_O54` / `StepWrap_O54`（两处）/ `HAnchor_O60` / `HPS02CkIsometry_O19` /
   `RiemannianEDistIsometry_O26` 的同一 binder 空白归一后 md5 相同），只把 `ckErr_O19`
   换成同体的 `ckErr_HGA` ← `hg06_S0_HGA.{u, u}`。
2. 链的使用：ch12 的假设 `ckErr_HGA … k p < ξ / 3`（`k ≤ n + 1`）经**公开** chain
   `isMetricApproximationOnBall_of_ckErr_chain_HGA1`（`ε a = ξ / 3`，`S_N < 3`）得到 donor 的
   `isMetricApproximationOnBall … ξ⁻¹ (n + 1) ξ`（即 adapter 里 donor 假设的来源）。
3. 逐阶容差的使用：`ε a = ξ * a! / (2 * 2 ^ a)`（每阶不同的 `C_a`，`Σ (a!)⁻¹ ε a < ξ`）
   同样落到 `isMetricApproximationOn`。
4. 反向 `C_0 = 0! = 1`：donor 的 `isMetricApproximationOn` ⇒ `C^0` 逐点界
   `ckErr_HGA … 0 p ≤ ξ`。
-/

set_option autoImplicit false

noncomputable section

open Manifold
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u v

/-- ch12 `hHG06` binder 逐字（`ckErr_O19` ↦ `ckErr_HGA`）← `hg06_S0_HGA`。 -/
example :
    ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier) (η : ℝ), 0 < η →
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ n : ℕ, ξ = 1 / ((n : ℝ) + 1) ∧ η⁻¹ < ξ⁻¹ ∧
      ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (Tr : HyperbolicTruncation H)
        (Tr' : HyperbolicTruncation H'), Tr.count ≤ Tr'.count →
      ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
        riemannianClosedBallOf H.metric o ξ⁻¹ ⊆ U →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
        (∀ k : ℕ, k ≤ n + 1 → ∀ p ∈ riemannianClosedBallOf H.metric o ξ⁻¹,
          ckErr_HGA H H'.metric 1 f k p < ξ / 3) →
        ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
          ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
          (∀ p, localPullInner H'.metric e p = H.metric.inner p) ∧
          ∀ p ∈ riemannianClosedBallOf H.metric o η⁻¹,
            riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal η :=
  hg06_S0_HGA.{u, u}

/-- 链的使用（2）：ch12 假设 ⇒ donor 的 `isMetricApproximationOnBall`。 -/
example (H : FiniteVolumeHyperbolicModel.{u}) (H' : FiniteVolumeHyperbolicModel.{v})
    (o : H.Carrier) {ξ : ℝ} (hξ : 0 < ξ) (n : ℕ) (U : TopologicalSpace.Opens H.Carrier)
    (f : H.Carrier → H'.Carrier) (hball : riemannianClosedBallOf H.metric o ξ⁻¹ ⊆ U)
    (hcm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hemb : IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x))
    (herr : ∀ k : ℕ, k ≤ n + 1 → ∀ p ∈ riemannianClosedBallOf H.metric o ξ⁻¹,
      ckErr_HGA H H'.metric 1 f k p < ξ / 3) :
    isMetricApproximationOnBall (fun y : (U : Set H.Carrier) => f y) H.metric H'.metric o ξ⁻¹
      (n + 1) ξ := by
  refine isMetricApproximationOnBall_of_ckErr_chain_HGA1 H H' o (inv_pos.mpr hξ) (n + 1)
    (fun _ => ξ / 3) (fun _ _ => by positivity) ?_ U f hball hcm hemb
    (fun a ha p hp => (herr a ha p hp).le)
  rw [← Finset.sum_mul]
  calc (∑ a ∈ Finset.range (n + 1 + 1), ((a.factorial : ℝ))⁻¹) * (ξ / 3)
      < 3 * (ξ / 3) := mul_lt_mul_of_pos_right (sum_inv_factorial_lt_three_HGA (n + 1))
        (by positivity)
    _ = ξ := by ring

/-- 逐阶容差的使用（3）：`ε a = ξ / (2 * (a! * 2 ^ a))`（每阶不同的 `C_a`），
`Σ_{a ≤ N} 1 / (2 * 2 ^ a) < ξ`。 -/
example (H : FiniteVolumeHyperbolicModel.{u}) (H' : FiniteVolumeHyperbolicModel.{v})
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier H'.Carrier ∞)
    (f : H.Carrier → H'.Carrier) (hΦf : (Φ : H.Carrier → H'.Carrier) = f)
    (K : Set H.Carrier) (hK : K ⊆ Φ.source) (N : ℕ) {ξ : ℝ} (hξ : 0 < ξ)
    (herr : ∀ a : ℕ, a ≤ N → ∀ p ∈ K,
      ckErr_HGA H H'.metric 1 f a p ≤ ξ * (a.factorial : ℝ) / (2 * 2 ^ a)) :
    PartialDiffeomorph.isMetricApproximationOn Φ K N ξ H.metric H'.metric := by
  refine isMetricApproximationOn_of_ckErr_chain_HGA1 H H' Φ f hΦf K hK N
    (fun a => ξ * (a.factorial : ℝ) / (2 * 2 ^ a)) (fun a _ => by positivity) ?_ herr
  have hterm : ∀ a ∈ Finset.range (N + 1),
      ((a.factorial : ℝ))⁻¹ * (ξ * (a.factorial : ℝ) / (2 * 2 ^ a)) =
        ξ * (1 / 2) * (1 / 2) ^ a := by
    intro a _
    have : (a.factorial : ℝ) ≠ 0 := by positivity
    rw [one_div_pow]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hgeo : ∑ a ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ a < 2 := by
    rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
    have : (0 : ℝ) < (1 / 2) ^ (N + 1) := by positivity
    have h2 : (((1 : ℝ) / 2) ^ (N + 1) - 1) / ((1 : ℝ) / 2 - 1) =
        2 * (1 - (1 / 2) ^ (N + 1)) := by
      field_simp
      ring
    rw [h2]
    linarith
  nlinarith

/-- 反向（4）：`C_0 = 0! = 1`，donor 的 `isMetricApproximationOn` ⇒ `C^0` 逐点界。 -/
example (H : FiniteVolumeHyperbolicModel.{u}) (H' : FiniteVolumeHyperbolicModel.{v})
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier H'.Carrier ∞)
    (f : H.Carrier → H'.Carrier) (hΦf : (Φ : H.Carrier → H'.Carrier) = f)
    (K : Set H.Carrier) (N : ℕ) {ξ : ℝ}
    (h : PartialDiffeomorph.isMetricApproximationOn Φ K N ξ H.metric H'.metric)
    (p : H.Carrier) (hp : p ∈ K) :
    ckErr_HGA H H'.metric 1 f 0 p ≤ ξ := by
  simpa using ckErr_le_of_isMetricApproximationOn_HGA1 H H' Φ f hΦf K N h 0 (Nat.zero_le _) p hp

end DifferentialGeometry.Geometry.Hyperbolic
