import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceDichotomyP6M2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BoundedCurvatureAtDistanceAnchor_P6L
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTimeWindowContinuity

/-!
# `hbcad` ⇐ `hsliceR`（开 slab 切片二分 + event 时刻切片右移；O-CH11-P6ANCH2 G3b，后缀 `_P6L2`）

`hbcad_of_slice_dichotomy_P6L`（O-CH11-P6ANCH G2）吃 Kdata 形 `hslice`（所有切片 `v = σ + σ'/R`，含 event 时刻）；
SLT 窗口版要正年龄（`time last < t`），故 G3 只在**开 slab** 切片产生二分（`hsliceR`，且 `σ'` 取区间一致形）。
本文件（R-C11-5 D-11 / O3）：
* 开 slab 切片（`time (activeStage v) < v`）：`hsliceR`（区间 `[σ', σ']`）+ rebase 二分
  `scalar_le_of_rebase_capWindow_dichotomy_P6L`，常数 `max A 1 · (QB₁ + 2Cup + 1)`；
* event 时刻切片（`v = time (activeStage v)`，`activeStage v = i.castSucc`，`σ < time last` 保证非末 stage）：
  incoming slab `S := (event i).incoming` 上右移 `scalar_le_of_right_shift_P6L2`（树内 private
  `ST/BoundedCurvatureAtDistanceAnchor:325` 的局部化副本，`hbound` 只在基点 `z` 处要求），右移切片
  `τ ∈ (v, v + e)`、`e = −σ'/(2R)` ⇒ `τ ≤ σ + σ'/(2R)`，落在 `hsliceR` 的区间 `[σ', σ'/2]` 内（开 slab），
  其上 cap / non-cap 二分（rebase）给统一上界 `(A'+1)(QB₂ + 2Cup + 1)`（`A' = max A 1`、半径 `Dd + 1`）；
  stage 指标与 slab 度量的对齐 = `scalar_stage_eq_P6L2` / `edist_stage_eq_P6L2`（`subst` + `HEq`）。
结论与 `hbcad_of_slice_dichotomy_P6L` 的 `hbcad` 逐字（`η₃ Cup Lc` 同取自
`exists_scalar_metric_comparison_of_standard_close (1/2)`）。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

universe u

/-- slab 内 stage 指标对齐：`m = i.castSucc`、`HEq` 点 ⇒ stage 度量标量 = incoming slab 标量。 -/
theorem scalar_stage_eq_P6L2 {H : ObservedHistory.{u}} (i : Fin H.eventCount)
    {m : Fin (H.eventCount + 1)} (hm : m = i.castSucc) (τ : ℝ) (pm : (H.stage m).Carrier)
    (pS : (H.stage i.castSucc).Carrier) (hp : HEq pm pS) :
    metricScalarAt (H.stageMetric m τ) pm = (H.event i).incoming.flow.scalar τ pS := by
  subst hm
  obtain rfl := eq_of_heq hp
  rw [ObservedHistory.stageMetric_castSucc_apply]
  rfl

/-- slab 内 stage 指标对齐：距离版。 -/
theorem edist_stage_eq_P6L2 {H : ObservedHistory.{u}} (i : Fin H.eventCount)
    {m : Fin (H.eventCount + 1)} (hm : m = i.castSucc) (τ : ℝ) (pm qm : (H.stage m).Carrier)
    (pS qS : (H.stage i.castSucc).Carrier) (hp : HEq pm pS) (hq : HEq qm qS) :
    riemannianEDistOf (H.stageMetric m τ) pm qm =
      riemannianEDistOf ((H.event i).incoming.flow.base.metric τ) pS qS := by
  subst hm
  obtain rfl := eq_of_heq hp
  obtain rfl := eq_of_heq hq
  rw [ObservedHistory.stageMetric_castSucc_apply]

/-- 树内 private `scalar_le_of_right_shift`（`ST/BoundedCurvatureAtDistanceAnchor:325`）的局部化副本：
`hbound` 只在固定基点 `z` 处要求（证明里本来只用这一处）。 -/
theorem scalar_le_of_right_shift_P6L2 {P : OrientedThreeStage.{u}} {a b : ℝ}
    (S : P.IncomingSlab a b) {v Rn A A' Dd D' C₁ e : ℝ} (hv : v ∈ Ico a b) (hRn : 1 ≤ Rn)
    (hA : A + 1 ≤ A') (hD : 0 < Dd) (hD' : Dd + 1 ≤ D') (he : 0 < e) (z : P.Carrier)
    (hbound : ∀ τ, v < τ → τ < v + e → τ < b → S.flow.scalar τ z ≤ A' * Rn → ∀ x : P.Carrier,
      riemannianEDistOf (S.flow.base.metric τ) z x < ENNReal.ofReal (D' / Real.sqrt Rn) →
      S.flow.scalar τ x ≤ C₁ * Rn)
    (x : P.Carrier) (hz : S.flow.scalar v z ≤ A * Rn)
    (hzx : riemannianEDistOf (S.flow.base.metric v) z x < ENNReal.ofReal (Dd / Real.sqrt Rn)) :
    S.flow.scalar v x ≤ (C₁ + 1) * Rn := by
  set ζ : ℝ := min 1 (1 / Dd) with hζdef
  have hζ : 0 < ζ := lt_min one_pos (by positivity)
  have hζ1 : ζ ≤ 1 := min_le_left _ _
  obtain ⟨δ, hδ, hδb, hclose⟩ := S.exists_forall_Icc_scalar_riemannNorm_metric_close hv hζ
  have hm : 0 < min δ e := lt_min hδ he
  set τ : ℝ := v + min δ e / 2 with hτdef
  have hvτ : v < τ := by linarith
  have hτe : τ < v + e := by linarith [min_le_right δ e]
  have hτδ : τ ≤ v + δ := by linarith [min_le_left δ e]
  have hτb : τ < b := by linarith
  have hvmem : v ∈ Icc (max a (v - δ)) (v + δ) := ⟨max_le hv.1 (by linarith), by linarith⟩
  have hτmem : τ ∈ Icc (max a (v - δ)) (v + δ) :=
    ⟨(max_le hv.1 (by linarith)).trans hvτ.le, hτδ⟩
  have hz' : S.flow.scalar τ z ≤ A' * Rn := by
    have h := (hclose τ hτmem v hvmem z).1
    rw [abs_le] at h
    nlinarith
  have hball := DifferentialGeometry.riemannianBallOf_subset_of_inner_le_mul
    (S.flow.base.metric v) (S.flow.base.metric τ) z (r := Dd / Real.sqrt Rn)
    (by linarith : (0 : ℝ) < 1 + ζ) (fun q _ w => (hclose τ hτmem v hvmem q).2.2 w)
  have hx : x ∈ riemannianBallOf (S.flow.base.metric τ) z
      (Real.sqrt (1 + ζ) * (Dd / Real.sqrt Rn)) := hball hzx
  have hrad : Real.sqrt (1 + ζ) * (Dd / Real.sqrt Rn) ≤ D' / Real.sqrt Rn := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have h1 : Real.sqrt (1 + ζ) * Dd = Real.sqrt ((1 + ζ) * Dd ^ 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hD.le]
    have hζD : ζ * Dd ≤ 1 := by
      calc ζ * Dd ≤ 1 / Dd * Dd := mul_le_mul_of_nonneg_right (min_le_right _ _) hD.le
        _ = 1 := by field_simp
    have h2 : (1 + ζ) * Dd ^ 2 ≤ (Dd + 1) ^ 2 := by nlinarith
    rw [h1]
    calc Real.sqrt ((1 + ζ) * Dd ^ 2) ≤ Real.sqrt ((Dd + 1) ^ 2) := Real.sqrt_le_sqrt h2
      _ = Dd + 1 := Real.sqrt_sq (by linarith)
      _ ≤ D' := hD'
  have hxτ := hbound τ hvτ hτe hτb hz' x (lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal hrad))
  have h := (hclose v hvmem τ hτmem x).1
  rw [abs_le] at h
  nlinarith

/-- **`hbcad` ⇐ `hsliceR`（开 slab 二分 + event 时刻右移，`_P6L2`）**：前提多 `R ≥ 1`（eventually）与
`σ < time last`（K-route：`σ = t < time (j n).succ`）。 -/
theorem ObservedHistory.hbcad_of_slice_dichotomy_open_P6L2 :
    ∃ η₃ Cup Lc : ℝ, 0 < η₃ ∧ 0 < Cup ∧ 0 < Lc ∧
    ∀ (Kh : ℕ → ObservedHistory.{u}) (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
      (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R : ℕ → ℝ), (∀ n, 0 < R n) →
      (∀ᶠ n in atTop, 1 ≤ R n) →
      (∀ n, (σ n : ℝ) < (Kh n).time (Fin.last (Kh n).eventCount)) →
    (∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
        Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
        ∀ σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ᶠ n in atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) + σ₁ / R n ≤ v →
          (v : ℝ) ≤ σ n + σ₂ / R n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁,
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          ∃ CWP : ((Kh n).stage ((Kh n).activeStage v)).Carrier → Prop,
            (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
                (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
                ENNReal.ofReal (Dd / Real.sqrt (R n)) → ¬ CWP w →
              R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w → ∀ x,
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v) w x <
                ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
                  Real.sqrt (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w)) →
              metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) x ≤
                QB * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w) ∧
            (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
                (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
                ENNReal.ofReal (Dd / Real.sqrt (R n)) → CWP w →
              ∃ (Ξ : standardCapWindow D₂ → ((Kh n).stage ((Kh n).activeStage v)).Carrier)
                (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
                Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
                ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                  τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                  ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                    metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                        ((Kh n).stageMetric ((Kh n).activeStage v) v)) Ξ hΞ)
                      ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                      (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃)) →
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw →
      ∀ᶠ n in atTop,
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
      ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₁)
        (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₂),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤
          C * R n := by
  obtain ⟨η₃, Cup, Lc, hη₃, hCup, hLc, hP3⟩ :=
    exists_scalar_metric_comparison_of_standard_close (1 / 2) (by norm_num) (by norm_num)
  refine ⟨η₃, Cup, Lc, hη₃, hCup, hLc, ?_⟩
  intro Kh σ y R hR hR1 hlastσ hslice A Dd hA hDd
  have hA' : (1 : ℝ) ≤ max A 1 := le_max_right _ _
  have hA'' : (1 : ℝ) ≤ max A 1 + 1 := by linarith
  have hD' : (0 : ℝ) < Dd + 1 := by linarith
  obtain ⟨QB₁, Dcap₁, D₂₁, hQB₁, hD₂₁, hsl₁⟩ := hslice (max A 1) Dd hA' hDd
  obtain ⟨QB₂, Dcap₂, D₂₂, hQB₂, hD₂₂, hsl₂⟩ := hslice (max A 1 + 1) (Dd + 1) hA'' hD'
  refine ⟨max (max A 1 * (QB₁ + 2 * Cup + 1)) ((max A 1 + 1) * (QB₂ + 2 * Cup + 1) + 1),
    fun σ' hσ' Dw hDw => ?_⟩
  filter_upwards [hsl₁ σ' σ' le_rfl hσ' Dw hDw,
    hsl₂ σ' (σ' / 2) (by linarith) (by linarith) Dw hDw, hR1] with n hn₁ hn₂ hRn1
  intro x₁ hx₁ x₂ _ v hvt hv tr₁ tr₂ hA1 hD
  have hA1' : metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
      (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ max A 1 * R n :=
    hA1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hR n).le)
  have hsA : 0 ≤ 2 * Dd * Real.sqrt (max A 1) := by positivity
  have hsL : 0 ≤ 2 * Dd * Lc * Real.sqrt (2 * max A 1) := by positivity
  have hsA' : 0 ≤ 2 * (Dd + 1) * Real.sqrt (max A 1 + 1) := by positivity
  have hsL' : 0 ≤ 2 * (Dd + 1) * Lc * Real.sqrt (2 * (max A 1 + 1)) := by positivity
  rcases lt_or_eq_of_le (ObservedHistory.activeStage_time_le (Kh n) v) with hopen | hevent
  · -- 开 slab：直接用 `hsliceR`（区间 `[σ', σ']`）+ rebase 二分
    obtain ⟨CWP, hB3e, hP1⟩ := hn₁ x₁ hx₁ v hvt hv.ge hv.le hopen tr₁ hA1'
    have h := scalar_le_of_rebase_capWindow_dichotomy_P6L _ CWP _ (hR n) hA' hDd hQB₁ hCup hLc
      (by linarith) (by linarith) hD₂₁ hB3e hP1 hP3 _ hA1' hD
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hR n).le)
  · -- event 时刻：`v = time (activeStage v)`，在 incoming slab 上右移
    have hne : (Kh n).activeStage v ≠ Fin.last (Kh n).eventCount := by
      intro h
      rw [h] at hevent
      have h1 := hlastσ n
      have h2 : (v : ℝ) ≤ σ n := hvt
      linarith
    obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hne
    have hva : (Kh n).time i.castSucc = v := by rw [hi]; exact hevent
    have hvb : (v : ℝ) < (Kh n).time i.succ := by
      have hlt : ((Kh n).activeStage v : ℕ) < (Kh n).eventCount := by
        rw [← hi]
        exact i.isLt
      have h := (Kh n).activeStage_before_next v hlt
      have heq : (⟨((Kh n).activeStage v : ℕ) + 1, by omega⟩ :
          Fin ((Kh n).eventCount + 1)) = i.succ := by
        apply Fin.ext
        simp only [← hi, Fin.val_castSucc, Fin.val_succ]
      rwa [heq] at h
    have hvIco : (v : ℝ) ∈ Ico ((Kh n).time i.castSucc) ((Kh n).time i.succ) := ⟨hva.le, hvb⟩
    let zS : ((Kh n).stage i.castSucc).Carrier :=
      cast (congrArg (fun m => ((Kh n).stage m).Carrier) hi.symm)
        (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
    have hzS : HEq (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) zS :=
      (cast_heq _ _).symm
    let xS : ((Kh n).stage i.castSucc).Carrier :=
      cast (congrArg (fun m => ((Kh n).stage m).Carrier) hi.symm)
        (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
    have hxS : HEq (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) xS :=
      (cast_heq _ _).symm
    have hzA : ((Kh n).event i).incoming.flow.scalar v zS ≤ max A 1 * R n :=
      (scalar_stage_eq_P6L2 i hi.symm v _ zS hzS).symm.trans_le hA1'
    have hzx : riemannianEDistOf (((Kh n).event i).incoming.flow.base.metric v) zS xS <
        ENNReal.ofReal (Dd / Real.sqrt (R n)) :=
      (edist_stage_eq_P6L2 i hi.symm v _ _ zS xS hzS hxS).symm.trans_lt hD
    have hRn0 := hR n
    have he : 0 < -σ' / (2 * R n) := div_pos (by linarith) (by positivity)
    have key := scalar_le_of_right_shift_P6L2 ((Kh n).event i).incoming (v := v) (Rn := R n)
      (A := max A 1) (A' := max A 1 + 1) (Dd := Dd) (D' := Dd + 1)
      (C₁ := (max A 1 + 1) * (QB₂ + 2 * Cup + 1)) (e := -σ' / (2 * R n)) hvIco hRn1 le_rfl hDd
      le_rfl he zS ?_ xS hzA hzx
    · exact (scalar_stage_eq_P6L2 i hi.symm v _ xS hxS).trans_le
        (key.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hRn0.le))
    -- 右移切片 `τ ∈ (v, v + e)` 上的统一界（hsliceR 区间 `[σ', σ'/2]` + rebase）
    intro τ hvτ hτe hτb hzτ x hx
    have hvσ : (v : ℝ) = σ n + σ' / R n := hv
    have hτσ2 : τ ≤ σ n + σ' / 2 / R n := by
      have : σ' / 2 / R n = σ' / R n + -σ' / (2 * R n) := by
        field_simp
        ring
      rw [this]
      linarith
    have hτσ : τ ≤ σ n := by
      have : σ' / 2 / R n < 0 := div_neg_of_neg_of_pos (by linarith) hRn0
      linarith
    let τI : Icc (0 : ℝ) (Kh n).horizon :=
      ⟨τ, (v.2.1).trans hvτ.le, hτσ.trans (σ n).2.2⟩
    have hτact : (Kh n).activeStage τI = i.castSucc :=
      ((Kh n).mem_stageDomain_iff τI i.castSucc).mp (by
        simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
          (show τ ∈ Ico ((Kh n).time i.castSucc) ((Kh n).time i.succ) from
            ⟨hva.le.trans hvτ.le, hτb⟩))
    have hvτI : v ≤ τI := hvτ.le
    have hτIσ : τI ≤ σ n := hτσ
    let tr₁' := tr₁.restrictFirst ((Kh n).activeStage_mono hvτI) ((Kh n).activeStage_mono hτIσ)
    have hz' : HEq (tr₁'.point ((Kh n).activeStage τI) le_rfl ((Kh n).activeStage_mono hτIσ))
        zS := (point_heq_of_eq_P6M2 tr₁ (hτact.trans hi) _ _ le_rfl _).trans hzS
    let xm : ((Kh n).stage ((Kh n).activeStage τI)).Carrier :=
      cast (congrArg (fun m => ((Kh n).stage m).Carrier) hτact.symm) x
    have hxm : HEq xm x := cast_heq _ _
    have hzτm : metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage τI) τI)
        (tr₁'.point ((Kh n).activeStage τI) le_rfl ((Kh n).activeStage_mono hτIσ)) ≤
        (max A 1 + 1) * R n :=
      (scalar_stage_eq_P6L2 i hτact τ _ zS hz').trans_le hzτ
    have hxτm : riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τI) τI)
        (tr₁'.point ((Kh n).activeStage τI) le_rfl ((Kh n).activeStage_mono hτIσ)) xm <
        ENNReal.ofReal ((Dd + 1) / Real.sqrt (R n)) :=
      (edist_stage_eq_P6L2 i hτact τ _ _ zS x hz' hxm).trans_lt hx
    have hopenτ : (Kh n).time ((Kh n).activeStage τI) < τI := by
      rw [hτact, hva]
      exact hvτ
    obtain ⟨CWP, hB3e, hP1⟩ := hn₂ x₁ hx₁ τI hτIσ (show σ n + σ' / R n ≤ τ by linarith) hτσ2
      hopenτ tr₁' hzτm
    have h := scalar_le_of_rebase_capWindow_dichotomy_P6L _ CWP _ hRn0 hA'' hD' hQB₂ hCup hLc
      (by linarith) (by linarith) hD₂₂ hB3e hP1 hP3 xm hzτm hxτm
    exact (scalar_stage_eq_P6L2 i hτact τ xm x hxm).symm.trans_le h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
