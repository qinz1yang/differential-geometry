import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeExcludeC11SP

set_option autoImplicit false

/-!
# native 分支的 ratio 二分：残余 binder 收窄到 `ρ/nr → 0`（O-CH11-SPINE-B G5，后缀 `_C11SP`）

**`native_regime_false_of_ratio_C11SP`**：结论逐字 = CODEX-C §3.4 `native_regime_false_CXSP`（同 G2）。
块标 **PROVISIONAL[hguardΛ, hnzero]**，比 G2 的 `[hguardT1, hnreg]` 更窄：
* `hguardΛ` = §3.3 T1 陈述体，仅在 `∀ A` 后插 `∀ Λ : ℝ, 1 ≤ Λ →`、guard 条件换成 `nr(t i) ≤ Λ * r i`
  （`Λ = 1` 即 T1）；repair target = guard 链的 Λ 机械穿线（G4a `exists_late_seed_record_scale_of_ratio_C11SP`
  已给唯一真实消费点；SPINE-A1 在做 `P6NativeSurgeryDistC11SP`）；
* `hnzero` = G2 的 `hnreg` 再加一行 `Tendsto (fun i => r i / q.neckRadius (t i)) atTop (𝓝 0)`——
  即只剩 **regular 时刻、`ρ/nr → 0`** 的 native 子情形；repair target = G4b（(D4′) buffer no-shortcut
  + 大 cap crossing 计数）+ SL2-b + NJ 装配（`native-route.md` §N1/§G4）。
证明：`hguardΛ` 取 `Λ = 1` 给 T1；对 regular native 坏序列做 `∃ Λ ≥ 1, ∃ᶠ i, nr ≤ Λ r` 二分——是则抽子列喂
`hguardΛ`，否则 `ρ/nr → 0` 喂 `hnzero`；最后调 G2 `native_regime_false_C11SP`。无新数学、无新具名 Prop。
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

/-- **G5（PROVISIONAL[hguardΛ, hnzero]）**：native 到 `False`，残余只剩 `ρ/nr → 0`。 -/
theorem native_regime_false_of_ratio_C11SP
    (P : OrientedThreeStage.{u}) (g : P.Metric)
    (hguardΛ :
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
          ∀ Λ : ℝ, 1 ≤ Λ →
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
            (∀ i, q.neckRadius (t i) ≤ Λ * r i) →
            Tendsto (fun i => r i / Real.sqrt (t i : ℝ)) atTop (𝓝 0) →
          False)
    (hnzero :
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
  have hguardT1 :
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
        False := by
    obtain ⟨ε₀, hε₀, h⟩ := hguardΛ
    refine ⟨ε₀, hε₀, ?_⟩
    intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hcore hε A hA idx H
      t p x r htime hsmall hvol hx hlate hescape hguard hratio
    exact h S F q hTower hdiag hacc hrad hord hcore hε A hA 1 le_rfl idx t p x r htime hsmall
      hvol hx hlate hescape (fun i => (one_mul (r i)).symm ▸ hguard i) hratio
  have hnreg :
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
    obtain ⟨ε₁, hε₁, hg⟩ := hguardΛ
    obtain ⟨ε₂, hε₂, hz⟩ := hnzero
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
    intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hcore hε hC1 hC2 A hA idx H
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
      exact hz S F q hTower hdiag (hacc.trans (min_le_right _ _)) hrad hord hcore hε hC1 hC2 A hA
        idx t s hs p x r htime hsmall hvol hx hlate hescape hnat hz0 hratio
  exact native_regime_false_C11SP P g hguardT1 hnreg

end GC.LongTime.Ch11
