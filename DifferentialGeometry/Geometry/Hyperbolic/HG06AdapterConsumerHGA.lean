import DifferentialGeometry.Geometry.Hyperbolic.HG06AdapterHGA

/-!
# HG06 adapter 的 consumer（S-HG-ADAPT，后缀 `_HGA`）

三个 `example`：
1. `hg06_S0_HGA` 与 ch12 `hps02_Ck_isometry_O19` 的 `hHG06` binder（sheet S0）**逐字**对齐
   （只把 `ckErr_O19` 换成同体的 `ckErr_HGA`，`H' : FiniteVolumeHyperbolicModel.{u}` 同宇宙）。
2. `hg06_adapter_HGA` 与 R3 §Q5 提议的 all-small-δ `hHG06`（`∃ δ₀` 在 `H'` 与近似之前）对齐
   （`ckApproximation` 占位换成 `ckErr_HGA` 逐点估计）。
3. G1：`Tr.count = endCount` 的实际使用（`Tr.count ≤ Tr'.count` ↔ `endCount ≤ endCount`）。
-/

set_option autoImplicit false

noncomputable section

open Manifold
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u

/-- ch12 `hHG06`（S0）逐字形状 ← `hg06_S0_HGA`。 -/
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

/-- R3 §Q5 提议的 all-small-δ `hHG06` 形状 ← `hg06_adapter_HGA`（D-R3-19）。 -/
example :
    ∀ (H : FiniteVolumeHyperbolicModel.{u}) (o : H.Carrier) (η : ℝ), 0 < η →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ (H' : FiniteVolumeHyperbolicModel.{u}) (Tr : HyperbolicTruncation H)
        (Tr' : HyperbolicTruncation H'), Tr.count ≤ Tr'.count →
        ∀ (δ : ℝ) (k : ℕ), 0 < δ → δ ≤ δ₀ → ⌈δ⁻¹⌉₊ ≤ k →
        ∀ (U : TopologicalSpace.Opens H.Carrier) (f : H.Carrier → H'.Carrier),
          riemannianClosedBallOf H.metric o δ⁻¹ ⊆ U →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ j : ℕ, j ≤ k → ∀ p ∈ riemannianClosedBallOf H.metric o δ⁻¹,
            ckErr_HGA H H'.metric 1 f j p < δ) →
          ∃ e : H.Carrier ≃ H'.Carrier, ContMDiff (𝓡 3) (𝓡 3) ∞ e ∧
            ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm ∧
            (∀ p, localPullInner H'.metric e p = H.metric.inner p) ∧
            ∀ p ∈ riemannianClosedBallOf H.metric o η⁻¹,
              riemannianEDistOf H'.metric (e p) (f p) < ENNReal.ofReal η :=
  hg06_adapter_HGA.{u, u}

/-- G1 的使用：两个截断的 `count` 比较就是 `endCount` 比较（`HG06` 的 `endCount` 形式不需要 HG03）。 -/
example (H H' : FiniteVolumeHyperbolicModel.{u}) (Tr : HyperbolicTruncation H)
    (Tr' : HyperbolicTruncation H') (h : Tr.count ≤ Tr'.count) :
    Geometry.Topology.endCount H.Carrier ≤ Geometry.Topology.endCount H'.Carrier :=
  (truncation_count_le_iff_endCount_le_HGA Tr Tr').1 h

end DifferentialGeometry.Geometry.Hyperbolic
