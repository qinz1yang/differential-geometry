import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeExcludePBC11SP

set_option autoImplicit false

/-!
# supply-threaded fn twin（O-CH11-XSUP2 层 X10，后缀 `_P6XS`）

孪生对象 `native_regime_false_PB_C11SP`。
生成器 `build-logs/scratch/O-CH11-XSUP2/gen/fnlib.py`；
源 `P6NativeExcludePBC11SP.lean`（tracked，不改）。
记 SUP := `TimeDerivativeSupply_C11E F q.neckRadius Γf.Ctime`：由 v8 collar 引擎孪生
在同一 `T.toChain / F / q` 处用 `hTD` 付，不是对任意链的总前提。
`Rn mn : ClosedBirthConstants → _`：请求依赖 `Γf`，provider 先取 `Γ Γf` 再请求，不交换量词。
`ε₀ : ClosedBirthConstants → ℝ`：Dt 常数为 `Γf.Ctime`，精度门槛随 `Γf`。
INTEGRATION-ONLY（无新 def / Prop）。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace GC.LongTime.Ch11

universe u

/-- **XSUP2 supply-threaded fn twin** of `native_regime_false_PB_C11SP`：
PB 透传 binder 与结论经 (a) `hdiag` 后加供给前提 (b) `ε₀` 函数化 (c) `Rn Γf / mn Γf`；
冻结 binder 不动；证明逐字 + `hSUP` 透传。 -/
theorem native_regime_false_SupFn_P6XS
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (Rn : ClosedBirthConstants → ℝ) (mn : ClosedBirthConstants → ℕ)
    (hguardT1 :
        ∃ ε₀ : ℝ, 0 < ε₀ ∧
          ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
            {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
            (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
            (q : CutoffParameters), F.tower = S.tower →
            (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
              q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
            pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
            2 ≤ pBase.modelOrder → CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
            ε ≤ coneAccuracy →
          ∀ A : ℝ, 0 < A →
          ∀ idx : ℕ → ℕ,
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
            (∀ i, q.neckRadius (t i) ≤ r i) →
            Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
          False)
    (hnreg :
        ∃ ε₀ : ClosedBirthConstants → ℝ, (∀ Γf, 0 < ε₀ Γf) ∧
          ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
            {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
            (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
            (q : CutoffParameters), F.tower = S.tower →
            (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
              q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
            TimeDerivativeSupply_C11E F q.neckRadius Γf.Ctime →
            pBase.modelAccuracy ≤ ε₀ Γf → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
            2 ≤ pBase.modelOrder → (Rn Γf ≤ pBase.modelRadius ∧ mn Γf ≤ pBase.modelOrder) →
            CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
            ε ≤ coneAccuracy →
            C1ceil_C11SC.{u} Γf ≤ C1 → C2ceil_C11SC.{u} Γf ≤ C2 →
          ∀ A : ℝ, 0 < A →
          ∀ idx : ℕ → ℕ,
          let H : ℕ → ObservedHistory.{u} := fun i => (F.tower.history (idx i)).toHistory
          ∀ (t : ∀ i, Icc (0 : ℝ) (H i).horizon) (s : ℕ → RegularSlice F.observation),
            (∀ i, (s i).time = (t i : ℝ)) →
          ∀ (p x : ∀ i, ((H i).stageAt (t i)).Carrier) (r : ℕ → ℝ),
            (∀ i, 2 * r i ^ 2 < (t i : ℝ)) →
            (∀ i, hasSmallParabolicCurvature (H i) (t i) (p i) (r i)) →
            (∀ i, ENNReal.ofReal (A⁻¹ * r i ^ 3) ≤
              ballVolume ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (r i)) →
            (∀ i, x i ∈ riemannianBallOf
              ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (p i) (A * r i)) →
            Tendsto (fun i => (t i : ℝ)) atTop atTop →
            Tendsto (fun i => metricScalarAt
              ((H i).stageMetric ((H i).activeStage (t i)) (t i)) (x i) * r i ^ 2) atTop atTop →
            (∀ i, r i < q.neckRadius (t i)) →
            Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
          False) :
    ∃ ε₀ : ClosedBirthConstants → ℝ, (∀ Γf, 0 < ε₀ Γf) ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        TimeDerivativeSupply_C11E F q.neckRadius Γf.Ctime →
        pBase.modelAccuracy ≤ ε₀ Γf → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder → (Rn Γf ≤ pBase.modelRadius ∧ mn Γf ≤ pBase.modelOrder) →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
        ε ≤ coneAccuracy →
        C1ceil_C11SC.{u} Γf ≤ C1 → C2ceil_C11SC.{u} Γf ≤ C2 →
      ∀ A : ℝ, 0 < A →
      ∀ idx : ℕ → ℕ,
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
        (∀ i, r i < q.neckRadius (t i)) →
        Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
      False := by
  obtain ⟨ε₁, hε₁, hg⟩ := hguardT1
  obtain ⟨ε₂, hε₂, hn⟩ := hnreg
  refine ⟨fun Γf => min ε₁ (ε₂ Γf), fun Γf => lt_min hε₁ (hε₂ Γf), ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hSUP hacc hrad hord hPB hcore hε hC1 hC2 A hA idx
    H
    t p x r htime hsmall hvol hx hlate hescape _hnative hratio
  obtain ⟨N, τ, s, p', x', ρ, hs, htime', hsmall', hvol', hx', hτ, hR, hρ, hsplit⟩ :=
    native_forward_split_C11SP F q A hA idx t p x r htime hsmall hvol hx hlate hescape hratio
  have hA' : 0 < 32768 * Real.exp 3 * A := by positivity
  rcases hsplit with hgd | hnt
  · exact hg S F q hTower hdiag (hacc.trans (min_le_left _ _)) hrad hord hcore hε _ hA' N τ
      p' x' ρ htime' hsmall' hvol' hx' hτ hR hgd hρ
  · exact hn S F q hTower hdiag hSUP (hacc.trans (min_le_right _ _)) hrad hord hPB hcore hε hC1 hC2
        _
      hA' N τ s hs p' x' ρ htime' hsmall' hvol' hx' hτ hR hnt hρ

end GC.LongTime.Ch11
