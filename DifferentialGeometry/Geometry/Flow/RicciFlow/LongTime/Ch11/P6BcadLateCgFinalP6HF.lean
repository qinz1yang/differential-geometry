import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceLateCgFinalP6HF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HUVFinalP6HF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BcadLateCgP6S3

/-!
# `hbcad` ⇐ late 切片数据的 final 孪生（O-CH11-HCLOSEF G3b，后缀 `_P6HF`）

* `hbcad_of_slice_dichotomy_open_final_P6HF`：`Local/BoundedCurvatureAtDistanceAnchorOpen_P6L2` 的
  final 版（去 `σ < time last`；`v = time last` 的切片在 final slab 上右移）。
* `hbcad_lateHI_of_slice_data_final_P6HF`：`P6BcadLateCgP6S3.hbcad_lateHI_of_slice_data_P6S3` 的
  final 版（G2 `hsliceR_lateHI_of_slice_data_final_P6HF` + 上式）。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

/-- **`hbcad` ⇐ `hsliceR`（final 孪生，`_P6HF`）**：`hbcad_of_slice_dichotomy_open_P6L2` 去掉
`σ < time last`：stage 时刻切片 `v = time m` 若 `m = last`（`σ` 在 final slab 内）则在限制 final slab
`((K n).finalSlab _).restrictIncoming …` 上右移（`scalar_le_of_right_shift_P6L2` 复用），否则同原证明。
`Kh := (K n).toHistory`。 -/
theorem ObservedHistory.hbcad_of_slice_dichotomy_open_final_P6HF :
    ∃ η₃ Cup Lc : ℝ, 0 < η₃ ∧ 0 < Cup ∧ 0 < Lc ∧
    ∀ (K : ℕ → RetainedCoreHistory.{u}) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier) (R : ℕ → ℝ), (∀ n, 0 < R n) →
      (∀ᶠ n in atTop, 1 ≤ R n) →
    (∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
        Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
        ∀ σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ᶠ n in atTop,
        ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
          n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) + σ₁ / R n ≤ v →
          (v : ℝ) ≤ σ n + σ₂ / R n → (K n).toHistory.time ((K n).toHistory.activeStage v) < v →
        ∀ tr₁ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v) ((K
          n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono hvt) x₁,
          metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
              hvt)) ≤ A * R n →
          ∃ CWP : ((K n).toHistory.stage ((K n).toHistory.activeStage v)).Carrier → Prop,
            (∀ w, riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
                (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
                  hvt)) w <
                ENNReal.ofReal (Dd / Real.sqrt (R n)) → ¬ CWP w →
              R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) w
                → ∀ x,
              riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) w x
                <
                ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
                  Real.sqrt (metricScalarAt ((K n).toHistory.stageMetric ((K
                    n).toHistory.activeStage v) v) w)) →
              metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) x ≤
                QB * metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
                  w) ∧
            (∀ w, riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
                (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
                  hvt)) w <
                ENNReal.ofReal (Dd / Real.sqrt (R n)) → CWP w →
              ∃ (Ξ : standardCapWindow D₂ → ((K n).toHistory.stage ((K n).toHistory.activeStage
                v)).Carrier)
                (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
                Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
                ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                  τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                  ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                    metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                        ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)) Ξ hΞ)
                      ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                      (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃)) →
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw →
      ∀ᶠ n in atTop,
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ x₂ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
      ∀ (tr₁ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v) ((K
        n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x₁)
        (tr₂ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v) ((K
          n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x₂),
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
              hvt)) ≤ A * R n →
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
              hvt))
            (tr₂.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
              hvt)) <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr₂.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
              hvt)) ≤
          C * R n := by
  obtain ⟨η₃, Cup, Lc, hη₃, hCup, hLc, hP3⟩ :=
    exists_scalar_metric_comparison_of_standard_close (1 / 2) (by norm_num) (by norm_num)
  refine ⟨η₃, Cup, Lc, hη₃, hCup, hLc, ?_⟩
  intro K σ y R hR hR1 hslice A Dd hA hDd
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
  have hA1' : metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
      (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono hvt)) ≤
        max A 1 * R n :=
    hA1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hR n).le)
  have hsA : 0 ≤ 2 * Dd * Real.sqrt (max A 1) := by positivity
  have hsL : 0 ≤ 2 * Dd * Lc * Real.sqrt (2 * max A 1) := by positivity
  have hsA' : 0 ≤ 2 * (Dd + 1) * Real.sqrt (max A 1 + 1) := by positivity
  have hsL' : 0 ≤ 2 * (Dd + 1) * Lc * Real.sqrt (2 * (max A 1 + 1)) := by positivity
  rcases lt_or_eq_of_le (ObservedHistory.activeStage_time_le (K n).toHistory v) with hopen | hevent
  · -- 开 slab：直接用 `hsliceR`（区间 `[σ', σ']`）+ rebase 二分
    obtain ⟨CWP, hB3e, hP1⟩ := hn₁ x₁ hx₁ v hvt hv.ge hv.le hopen tr₁ hA1'
    have h := scalar_le_of_rebase_capWindow_dichotomy_P6L _ CWP _ (hR n) hA' hDd hQB₁ hCup hLc
      (by linarith) (by linarith) hD₂₁ hB3e hP1 hP3 _ hA1' hD
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hR n).le)
  · -- event 时刻：`v = time (activeStage v)`，在 incoming slab 上右移
    by_cases hlF : (K n).toHistory.activeStage v = Fin.last (K n).eventCount
    · -- final 时刻 `v = time last`（`σ` 在 final slab 内）：在 final slab 上右移
      have hva : (K n).toHistory.time (Fin.last (K n).eventCount) = v := by
        have h := hevent
        rw [hlF] at h
        exact h
      have hRn0 := hR n
      have hvσlt : (v : ℝ) < σ n := by
        have : σ' / R n < 0 := div_neg_of_neg_of_pos hσ' hRn0
        have hv' : (v : ℝ) = σ n + σ' / R n := hv
        linarith
      have hσh : (σ n : ℝ) ≤ (K n).toHistory.horizon := (σ n).2.2
      have hfn : (K n).time (Fin.last (K n).eventCount) < (K n).horizon := by
        change (K n).toHistory.time (Fin.last (K n).eventCount) < (K n).toHistory.horizon
        rw [hva]
        linarith
      have hvIco : (v : ℝ) ∈ Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon := by
        refine ⟨hva.le, ?_⟩
        change (v : ℝ) < (K n).toHistory.horizon
        linarith
      let zS : ((K n).stage (Fin.last (K n).eventCount)).Carrier :=
        cast (congrArg (fun m => ((K n).toHistory.stage m).Carrier) hlF)
          (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono hvt))
      have hzS : HEq (tr₁.point ((K n).toHistory.activeStage v) le_rfl
          ((K n).toHistory.activeStage_mono hvt)) zS := (cast_heq _ _).symm
      let xS : ((K n).stage (Fin.last (K n).eventCount)).Carrier :=
        cast (congrArg (fun m => ((K n).toHistory.stage m).Carrier) hlF)
          (tr₂.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono hvt))
      have hxS : HEq (tr₂.point ((K n).toHistory.activeStage v) le_rfl
          ((K n).toHistory.activeStage_mono hvt)) xS := (cast_heq _ _).symm
      have hzA : (((K n).finalSlab hfn).restrictIncoming le_rfl hfn le_rfl).flow.scalar v zS ≤ max A
        1 * R n :=
        ((K n).scalar_stage_eq_last_P6HF hfn hlF v _ zS hzS).symm.trans_le hA1'
      have hzx : riemannianEDistOf ((((K n).finalSlab hfn).restrictIncoming le_rfl hfn
        le_rfl).flow.base.metric v) zS xS <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) :=
        ((K n).edist_stage_eq_last_P6HF hfn hlF v _ _ zS xS hzS hxS).symm.trans_lt hD
      have he : 0 < -σ' / (2 * R n) := div_pos (by linarith) (by positivity)
      have key := scalar_le_of_right_shift_P6L2 (((K n).finalSlab hfn).restrictIncoming le_rfl hfn
        le_rfl) (v := v) (Rn := R n)
        (A := max A 1) (A' := max A 1 + 1) (Dd := Dd) (D' := Dd + 1)
        (C₁ := (max A 1 + 1) * (QB₂ + 2 * Cup + 1)) (e := -σ' / (2 * R n)) hvIco hRn1 le_rfl hDd
        le_rfl he zS ?_ xS hzA hzx
      · exact ((K n).scalar_stage_eq_last_P6HF hfn hlF v _ xS hxS).trans_le
          (key.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hRn0.le))
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
      let τI : Icc (0 : ℝ) (K n).toHistory.horizon :=
        ⟨τ, (v.2.1).trans hvτ.le, hτσ.trans (σ n).2.2⟩
      have hτact : (K n).toHistory.activeStage τI = Fin.last (K n).eventCount :=
        (K n).toHistory.activeStage_eq_last_of_time_last_le τI (hva.le.trans hvτ.le)
      have hvτI : v ≤ τI := hvτ.le
      have hτIσ : τI ≤ σ n := hτσ
      let tr₁' := tr₁.restrictFirst ((K n).toHistory.activeStage_mono hvτI)
        ((K n).toHistory.activeStage_mono hτIσ)
      have hz' : HEq (tr₁'.point ((K n).toHistory.activeStage τI) le_rfl
          ((K n).toHistory.activeStage_mono hτIσ)) zS :=
        (point_heq_of_eq_P6M2 tr₁ (hτact.trans hlF.symm) _ _ le_rfl _).trans hzS
      let xm : ((K n).toHistory.stage ((K n).toHistory.activeStage τI)).Carrier :=
        cast (congrArg (fun m => ((K n).toHistory.stage m).Carrier) hτact.symm) x
      have hxm : HEq xm x := cast_heq _ _
      have hzτm : metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τI) τI)
          (tr₁'.point ((K n).toHistory.activeStage τI) le_rfl
            ((K n).toHistory.activeStage_mono hτIσ)) ≤ (max A 1 + 1) * R n :=
        ((K n).scalar_stage_eq_last_P6HF hfn hτact τ _ zS hz').trans_le hzτ
      have hxτm : riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τI)
        τI)
          (tr₁'.point ((K n).toHistory.activeStage τI) le_rfl
            ((K n).toHistory.activeStage_mono hτIσ)) xm <
          ENNReal.ofReal ((Dd + 1) / Real.sqrt (R n)) :=
        ((K n).edist_stage_eq_last_P6HF hfn hτact τ _ _ zS x hz' hxm).trans_lt hx
      have hopenτ : (K n).toHistory.time ((K n).toHistory.activeStage τI) < τI := by
        rw [hτact, hva]
        exact hvτ
      obtain ⟨CWP, hB3e, hP1⟩ := hn₂ x₁ hx₁ τI hτIσ (show σ n + σ' / R n ≤ τ by linarith) hτσ2
        hopenτ tr₁' hzτm
      have h := scalar_le_of_rebase_capWindow_dichotomy_P6L _ CWP _ hRn0 hA'' hD' hQB₂ hCup hLc
        (by linarith) (by linarith) hD₂₂ hB3e hP1 hP3 xm hzτm hxτm
      exact ((K n).scalar_stage_eq_last_P6HF hfn hτact τ xm x hxm).symm.trans_le h
    have hne : (K n).toHistory.activeStage v ≠ Fin.last (K n).toHistory.eventCount := hlF
    obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hne
    have hva : (K n).toHistory.time i.castSucc = v := by rw [hi]; exact hevent
    have hvb : (v : ℝ) < (K n).toHistory.time i.succ := by
      have hlt : ((K n).toHistory.activeStage v : ℕ) < (K n).toHistory.eventCount := by
        rw [← hi]
        exact i.isLt
      have h := (K n).toHistory.activeStage_before_next v hlt
      have heq : (⟨((K n).toHistory.activeStage v : ℕ) + 1, by omega⟩ :
          Fin ((K n).toHistory.eventCount + 1)) = i.succ := by
        apply Fin.ext
        simp only [← hi, Fin.val_castSucc, Fin.val_succ]
      rwa [heq] at h
    have hvIco : (v : ℝ) ∈ Ico ((K n).toHistory.time i.castSucc) ((K n).toHistory.time i.succ) :=
      ⟨hva.le, hvb⟩
    let zS : ((K n).toHistory.stage i.castSucc).Carrier :=
      cast (congrArg (fun m => ((K n).toHistory.stage m).Carrier) hi.symm)
        (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono hvt))
    have hzS : HEq (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K
      n).toHistory.activeStage_mono hvt)) zS :=
      (cast_heq _ _).symm
    let xS : ((K n).toHistory.stage i.castSucc).Carrier :=
      cast (congrArg (fun m => ((K n).toHistory.stage m).Carrier) hi.symm)
        (tr₂.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono hvt))
    have hxS : HEq (tr₂.point ((K n).toHistory.activeStage v) le_rfl ((K
      n).toHistory.activeStage_mono hvt)) xS :=
      (cast_heq _ _).symm
    have hzA : ((K n).toHistory.event i).incoming.flow.scalar v zS ≤ max A 1 * R n :=
      (scalar_stage_eq_P6L2 i hi.symm v _ zS hzS).symm.trans_le hA1'
    have hzx : riemannianEDistOf (((K n).toHistory.event i).incoming.flow.base.metric v) zS xS <
        ENNReal.ofReal (Dd / Real.sqrt (R n)) :=
      (edist_stage_eq_P6L2 i hi.symm v _ _ zS xS hzS hxS).symm.trans_lt hD
    have hRn0 := hR n
    have he : 0 < -σ' / (2 * R n) := div_pos (by linarith) (by positivity)
    have key := scalar_le_of_right_shift_P6L2 ((K n).toHistory.event i).incoming (v := v) (Rn := R
      n)
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
    let τI : Icc (0 : ℝ) (K n).toHistory.horizon :=
      ⟨τ, (v.2.1).trans hvτ.le, hτσ.trans (σ n).2.2⟩
    have hτact : (K n).toHistory.activeStage τI = i.castSucc :=
      ((K n).toHistory.mem_stageDomain_iff τI i.castSucc).mp (by
        simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
          (show τ ∈ Ico ((K n).toHistory.time i.castSucc) ((K n).toHistory.time i.succ) from
            ⟨hva.le.trans hvτ.le, hτb⟩))
    have hvτI : v ≤ τI := hvτ.le
    have hτIσ : τI ≤ σ n := hτσ
    let tr₁' := tr₁.restrictFirst ((K n).toHistory.activeStage_mono hvτI) ((K
      n).toHistory.activeStage_mono hτIσ)
    have hz' : HEq (tr₁'.point ((K n).toHistory.activeStage τI) le_rfl ((K
      n).toHistory.activeStage_mono hτIσ))
        zS := (point_heq_of_eq_P6M2 tr₁ (hτact.trans hi) _ _ le_rfl _).trans hzS
    let xm : ((K n).toHistory.stage ((K n).toHistory.activeStage τI)).Carrier :=
      cast (congrArg (fun m => ((K n).toHistory.stage m).Carrier) hτact.symm) x
    have hxm : HEq xm x := cast_heq _ _
    have hzτm : metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τI) τI)
        (tr₁'.point ((K n).toHistory.activeStage τI) le_rfl ((K n).toHistory.activeStage_mono hτIσ))
          ≤
        (max A 1 + 1) * R n :=
      (scalar_stage_eq_P6L2 i hτact τ _ zS hz').trans_le hzτ
    have hxτm : riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τI) τI)
        (tr₁'.point ((K n).toHistory.activeStage τI) le_rfl ((K n).toHistory.activeStage_mono hτIσ))
          xm <
        ENNReal.ofReal ((Dd + 1) / Real.sqrt (R n)) :=
      (edist_stage_eq_P6L2 i hτact τ _ _ zS x hz' hxm).trans_lt hx
    have hopenτ : (K n).toHistory.time ((K n).toHistory.activeStage τI) < τI := by
      rw [hτact, hva]
      exact hvτ
    obtain ⟨CWP, hB3e, hP1⟩ := hn₂ x₁ hx₁ τI hτIσ (show σ n + σ' / R n ≤ τ by linarith) hτσ2
      hopenτ tr₁' hzτm
    have h := scalar_le_of_rebase_capWindow_dichotomy_P6L _ CWP _ hRn0 hA'' hD' hQB₂ hCup hLc
      (by linarith) (by linarith) hD₂₂ hB3e hP1 hP3 xm hzτm hxτm
    exact (scalar_stage_eq_P6L2 i hτact τ xm x hxm).symm.trans_le h

/-- **`hbcad` ⇐ late 切片数据（final 孪生，`_P6HF`）**：`hbcad_lateHI_of_slice_data_P6S3` 的 final 版；
U 侧 = event 块 `hUVG` + final slab 块 `hUVGF`；结论 = G1
`false_of_selection_finalSlab_lateHI_prefix_P6HF` 的 `hbcad` binder（`Kh := (K n).toHistory`）。 -/
theorem ObservedHistory.hbcad_lateHI_of_slice_data_final_P6HF
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Cg : ℝ} (hCg : 1 ≤ Cg)
    {K : ℕ → RetainedCoreHistory.{u}}
    (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl)
    {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (Q n) (Fin.last (K n).eventCount))
    (hpinchF : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi)
    (hderF : ∀ n, (G n).DerivativeBoundBefore Ctime (Q n) (K n).horizon)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt (σ
      n)).Carrier)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hqR : ∀ n : ℕ, max ((n : ℝ) + 1) (Q n) ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hdistQ : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
        (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v) ((K
        n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v) ((K n).toHistory.activeStage_mono
              hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono hvs))
              ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (hUVG : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∀ᶠ n in atTop,
      ∀ (j' : Fin (K n).toHistory.eventCount) (v : ℝ), (K n).toHistory.time j'.castSucc < v →
        v < (K n).toHistory.time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory j'.castSucc ((K n).toHistory.activeStage (σ n)) hjσ
          x₁),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)) (w : ((K n).toHistory.stage
          j'.castSucc).Carrier),
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((K n).toHistory.event j').incoming.flow.scalar v w →
          (∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            Cg * R n < ((K n).toHistory.event j').incoming.flow.scalar v x →
            ∃ W : SpatialCanonicalWitness (((K n).toHistory.event j').incoming.flow.base.metric v)
              ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
          (∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).toHistory.time j'.castSucc) v,
            v - B / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((K n).toHistory.event j').incoming.flow.scalar v' x →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential ((K n).toHistory.event j').incoming.flow v' x ξ| ≤
                Cgrad * ((K n).toHistory.event j').incoming.flow.scalar v' x *
                  Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v' x) *
                  Real.sqrt ((((K n).toHistory.event j').incoming.flow.base.metric v').inner x ξ ξ))
                    ∧
          (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon),
            v - B / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (K n).toHistory.time j'.castSucc < τ → (τ : ℝ) < (K n).toHistory.time j'.succ →
            ∀ z ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                  (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
                  ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                  (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                    zz b)))
    (hUVGF : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∀ᶠ n in atTop,
      ∀ (v : ℝ), (K n).time (Fin.last (K n).eventCount) < v →
        v < (K n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : (Fin.last (K n).eventCount) ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory (Fin.last (K n).eventCount) ((K
          n).toHistory.activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ (Fin.last (K n).eventCount))
        (h2 : (Fin.last (K n).eventCount) ≤ (K n).toHistory.activeStage (Tn n)) (w : ((K
          n).toHistory.stage (Fin.last (K n).eventCount)).Carrier),
        riemannianEDistOf ((G n).flow.base.metric v)
            ((seedTrace n).point (Fin.last (K n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((G n).flow.base.metric v)
            (tr.point (Fin.last (K n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R
              n)) →
        R n ≤ (G n).flow.scalar v w →
          (∀ x ∈ riemannianBallOf ((G n).flow.base.metric v) w
                (Rad / Real.sqrt ((G n).flow.scalar v w)),
            Cg * R n < (G n).flow.scalar v x →
            ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric v)
              ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
          (∀ x ∈ riemannianBallOf ((G n).flow.base.metric v) w
                (Rad / Real.sqrt ((G n).flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) v,
            v - B / (G n).flow.scalar v w ≤ v' →
            Cg * R n < (G n).flow.scalar v' x →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential (G n).flow v' x ξ| ≤
                Cgrad * (G n).flow.scalar v' x *
                  Real.sqrt ((G n).flow.scalar v' x) *
                  Real.sqrt (((G n).flow.base.metric v').inner x ξ ξ)) ∧
          (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon),
            v - B / (G n).flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (K n).time (Fin.last (K n).eventCount) < τ → (τ : ℝ) < (K n).horizon →
            ∀ z ∈ riemannianBallOf ((G n).flow.base.metric v) w
                  (Rad / Real.sqrt ((G n).flow.scalar v w)),
            ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
                  ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                  (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                    zz b))) :
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw →
      ∀ᶠ n in atTop,
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ x₂ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
      ∀ (tr₁ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v) ((K
        n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x₁)
        (tr₂ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v) ((K
          n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x₂),
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
              hvt)) ≤ A * R n →
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
              hvt))
            (tr₂.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
              hvt)) <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            (tr₂.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
              hvt)) ≤
          C * R n := by
  obtain ⟨η₃, Cup, Lc, hη₃, hCup, hLc, hB⟩ :=
    ObservedHistory.hbcad_of_slice_dichotomy_open_final_P6HF.{u}
  have hsl := ObservedHistory.hsliceR_lateHI_of_slice_data_final_P6HF hεle hκ hphi hCg hη₃ hLc hfin
    hG recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK hpinchF hderF σ y R
    hRpos hqR hT₀ Tn aSeed haT hsT has pT seedTrace L hL hwin ρV hρV hdistQ hUVG hUVGF
  have hR1 : ∀ᶠ n in atTop, 1 ≤ R n := Eventually.of_forall fun n => by
    have h1 := hqR n
    have h2 := le_max_left ((n : ℝ) + 1) (Q n)
    have h3 : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  exact hB K σ y R hRpos hR1 hsl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
