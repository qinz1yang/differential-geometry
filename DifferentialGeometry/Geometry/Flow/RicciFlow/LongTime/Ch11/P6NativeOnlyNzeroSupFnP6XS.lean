import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeOnlyNzeroPBC11SP

set_option autoImplicit false

/-!
# supply-threaded fn twin（O-CH11-XSUP2 层 X9，后缀 `_P6XS`）

孪生对象 `native_hnreg_of_hnzero_PB_C11SP`。
生成器 `build-logs/scratch/O-CH11-XSUP2/gen/fnlib.py`；
源 `P6NativeOnlyNzeroPBC11SP.lean`（tracked，不改）。
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

/-- **XSUP2 supply-threaded fn twin** of `native_hnreg_of_hnzero_PB_C11SP`：
PB 透传 binder 与结论经 (a) `hdiag` 后加供给前提 (b) `ε₀` 函数化 (c) `Rn Γf / mn Γf`；
冻结 binder 不动；证明逐字 + `hSUP` 透传。 -/
theorem native_hnreg_of_hnzero_SupFn_P6XS
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (Rn : ClosedBirthConstants → ℝ) (mn : ClosedBirthConstants → ℕ)
    (hnzero :
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
            Tendsto (fun i => r i / q.neckRadius (t i)) atTop (𝓝 0) →
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
      False := by
  obtain ⟨ε₁, hε₁, hg⟩ := guard_regime_false_final_bdd_C11SP P g
  obtain ⟨ε₂, hε₂, hz⟩ := hnzero
  refine ⟨fun Γf => min ε₁ (ε₂ Γf), fun Γf => lt_min hε₁ (hε₂ Γf), ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hSUP hacc hrad hord hPB hcore hε hC1 hC2 A hA idx
    H
    t s hs p x r htime hsmall hvol hx hlate hescape hnat hratio
  by_cases hb : ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ᶠ i in atTop, q.neckRadius (t i) ≤ Λ * r i
  · obtain ⟨Λ, hΛ, hfr⟩ := hb
    obtain ⟨φ, hφ, hP⟩ := Filter.extraction_of_frequently_atTop hfr
    have hφt := hφ.tendsto_atTop
    exact hg S F q hTower hdiag (hacc.trans (min_le_left _ _)) hrad hord hcore hε A hA Λ hΛ
      (fun i => idx (φ i)) (fun i => t (φ i)) (fun i => p (φ i)) (fun i => x (φ i))
      (fun i => r (φ i)) (fun i => htime (φ i)) (fun i => hsmall (φ i)) (fun i => hvol (φ i))
      (fun i => hx (φ i)) (hlate.comp hφt) (hescape.comp hφt) hP (hratio.comp hφt)
  · push Not at hb
    have hz0 : Tendsto (fun i => r i / q.neckRadius (t i)) atTop (𝓝 0) := by
      refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun i => ?_, fun a ha => ?_⟩
      · exact ha.trans (div_pos (hsmall i).1 (q.neckRadius_pos _ (t i).2.1))
      · filter_upwards [hb (max 1 (1 / a)) (le_max_left _ _)] with i hi
        have hnr : 0 < q.neckRadius (t i) := q.neckRadius_pos _ (t i).2.1
        have hr : 0 < r i := (hsmall i).1
        rw [div_lt_iff₀ hnr]
        have h1 : (1 / a) * r i ≤ max 1 (1 / a) * r i :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hr.le
        have h2 : (1 / a) * r i < q.neckRadius (t i) := h1.trans_lt hi
        calc r i = a * ((1 / a) * r i) := by field_simp
          _ < a * q.neckRadius (t i) := mul_lt_mul_of_pos_left h2 ha
    exact hz S F q hTower hdiag hSUP (hacc.trans (min_le_right _ _)) hrad hord hPB hcore hε hC1 hC2
      A hA
      idx t s hs p x r htime hsmall hvol hx hlate hescape hnat hz0 hratio

end GC.LongTime.Ch11
