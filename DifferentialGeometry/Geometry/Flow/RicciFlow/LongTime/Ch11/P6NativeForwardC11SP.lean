import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6RegularBadSequenceCXSP

set_option autoImplicit false

/-!
# native 分支的 forward 归约（O-CH11-SPINE-B G1，后缀 `_C11SP`；CODEX-C §3.4 B2）

输入 = CODEX-C §3.4 `native_regime_false_CXSP` 的序列前提（**不含** native 前提 `r < nr(t)`，
也不含 δ 窗 / `hw`）。先由 `R r² → ∞` 抽子列付 G65 的 `hbad`，再调用 G65
`exists_regularized_scalar_bad_sequence_CXSP`（同 F、RegularSlice `τ`、`ρ = r/2`、
`A' = 32768·e³·A`），最后对**新**的 `(τ, ρ)` 做无穷鸽巢：
`(∀ i, nr(τ i) ≤ ρ i) ∨ (∀ i, ρ i < nr(τ i))`。不假设 `nr` 连续，不用 antitone，
不用 G65 末项的 Λ 分割；不运输 κ 窗 / 旧 α 窗（F9）。

guard 支的输出逐项 = CODEX-C §3.3 T1 的序列前提（`A := A'`）；native 支额外带 RegularSlice
`s i` 与 `(s i).time = τ i`。所以 birth / horizon / activation 右跳在此一次付清，
native 支不再 forward（无循环，(B-2) 不发生）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch11

universe u

/-- **G1（PROVED 目标）**：T2 的序列前提 ⇒ 同 F 的 RegularSlice 坏序列，并在新时刻二分。 -/
theorem native_forward_split_C11SP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (q : CutoffParameters) (A : ℝ) (hA : 0 < A)
    (idx : ℕ → ℕ) :
    let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
    ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon)
      (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
      (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
      (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
      (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
        ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
      (∀ i, x i ∈ riemannianBallOf
        ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
      Tendsto (fun i => (t i : ℝ)) atTop atTop →
      Tendsto (fun i => metricScalarAt
        ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
      Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
    ∃ N : ℕ → ℕ,
    let H' : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (N i)).toHistory
    ∃ (τ : ∀ i, Icc (0 : ℝ) (H' i).horizon) (s : ℕ → RegularSlice F.observation)
      (p' x' : ∀ i, ((H' i).stageAt (τ i)).Carrier) (ρ : ℕ → ℝ),
      (∀ i, (s i).time = (τ i : ℝ)) ∧
      (∀ i, 2 * ρ i ^ 2 < (τ i : ℝ)) ∧
      (∀ i, hasSmallParabolicCurvature (H' i) (τ i) (p' i) (ρ i)) ∧
      (∀ i, ENNReal.ofReal ((32768 * Real.exp 3 * A)⁻¹ * ρ i ^ 3) ≤
        ballVolume ((H' i).stageMetric ((H' i).activeStage (τ i)) (τ i)) (p' i) (ρ i)) ∧
      (∀ i, x' i ∈ riemannianBallOf
        ((H' i).stageMetric ((H' i).activeStage (τ i)) (τ i)) (p' i)
          ((32768 * Real.exp 3 * A) * ρ i)) ∧
      Tendsto (fun i => (τ i : ℝ)) atTop atTop ∧
      Tendsto (fun i => metricScalarAt
        ((H' i).stageMetric ((H' i).activeStage (τ i)) (τ i)) (x' i) * ρ i ^ 2)
          atTop atTop ∧
      Tendsto (fun i => ρ i / Real.sqrt (τ i : ℝ)) atTop (𝓝 0) ∧
      ((∀ i, q.neckRadius (τ i) ≤ ρ i) ∨ (∀ i, ρ i < q.neckRadius (τ i))) := by
  intro H t p x r htime hsmall hvol hx hlate hescape hratio
  obtain ⟨φ, hφ, hbad⟩ := Filter.extraction_forall_of_eventually
    (fun n : ℕ => hescape.eventually_gt_atTop ((n : ℝ) + 1))
  have hφt := hφ.tendsto_atTop
  obtain ⟨N, τ, s, p', x', ρ, -, -, -, -, hs, -, -, -, -, -, -, htime', hsmall', hvol', hx',
      -, -, -, hRlim, hρlim, hτlim, -, -⟩ :=
    exists_regularized_scalar_bad_sequence_CXSP F hA (fun i => idx (φ i))
      (fun i => t (φ i)) (fun i => p (φ i)) (fun i => x (φ i)) (fun i => r (φ i))
      (fun i => htime (φ i)) (fun i => hsmall (φ i)) (fun i => hvol (φ i))
      (fun i => hx (φ i)) hbad (hratio.comp hφt) (hescape.comp hφt) (hlate.comp hφt)
  have hor : (∃ᶠ i in atTop, q.neckRadius (τ i) ≤ ρ i) ∨
      (∃ᶠ i in atTop, ρ i < q.neckRadius (τ i)) :=
    Filter.frequently_or_distrib.mp
      (Filter.Eventually.frequently (Filter.Eventually.of_forall fun i => le_or_gt _ _))
  have key : ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ((∀ i, q.neckRadius (τ (ψ i)) ≤ ρ (ψ i)) ∨
        (∀ i, ρ (ψ i) < q.neckRadius (τ (ψ i)))) := by
    rcases hor with h | h
    · obtain ⟨ψ, hψ, hP⟩ := Filter.extraction_of_frequently_atTop h
      exact ⟨ψ, hψ, Or.inl hP⟩
    · obtain ⟨ψ, hψ, hP⟩ := Filter.extraction_of_frequently_atTop h
      exact ⟨ψ, hψ, Or.inr hP⟩
  obtain ⟨ψ, hψ, hsplit⟩ := key
  have hψt := hψ.tendsto_atTop
  exact ⟨fun i => N (ψ i), fun i => τ (ψ i), fun i => s (ψ i), fun i => p' (ψ i),
    fun i => x' (ψ i), fun i => ρ (ψ i), fun i => hs (ψ i), fun i => htime' (ψ i),
    fun i => hsmall' (ψ i), fun i => hvol' (ψ i), fun i => hx' (ψ i), hτlim.comp hψt,
    hRlim.comp hψt, hρlim.comp hψt, hsplit⟩

end GC.LongTime.Ch11
