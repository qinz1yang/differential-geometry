import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J11HgapJ11S

/-!
# hgap J11 binder 级 producer（O-CH11-J11STAY G3c，后缀 `_J11S`）

KT2c event producer `hgapJ_loc_of_producers_P6KT2c` 的 OPEN binder `hJ11` **逐字**（生成器从
`P6GapProducersLocP6KT2c.lean` 抽取 `(hJ11 : …)` 块，assert）⇐
* FRESH 家族 `hfresh`（同 J15 G1 `hJ15_loc_of_fresh_P6HA`）+ `hanti`（producer 原有前提）；
* crossing 孪生 `hkappaC_tower_of_fresh_P6KA` / `hstopE_deep_tower_pc_P6KA` 的同一前提块
  （`hC2 / hDm / hacc ≤ ε₀ / hm / hδlim` + `hfamT`，`qp` 为 records 参数）；
* `hDextJ`：J11 binder 前缀（到 `hlt` 为止，逐字）⇒ hPN 中心 driver 输出 `hDext`
  （J14 G4 `j14_of_depthExt_P6HA` 的同一输入；producer = DEPTH4C2 anyPos / HARNACK guarded driver，
  其 `hkappaC` 槽由 G2 `hkappaC_driver_interior_J11S` 付）。
证明：G1 interior stay（塔层实例）+ `hDext` ⇒ `hfpL_hPN`（G3b）；FRESH(A + 3) K 帧准备
（`freshK_prep_J11S` = `freshK_prep_P6HA` 逐字副本，后者未入 SNAP）⇒ G3b `hJ11_of_fresh_fpL_J11S`。
* **`hJ11_loc_of_depthExt_J11S`**：PROVISIONAL[`hfamT`（= `hfamT_slot_of_residual_DLW` 的输出形，其剩余
  `hfamR`）、`hDextJ`（driver 输出）]；无新 binder 形状。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **FRESH 前提的 K 帧准备（`_J11S`）**：`freshK_prep_P6HA`（J8KAPPA G1）逐字副本。 -/
theorem freshK_prep_J11S {q : CutoffParameters} (hanti : AntitoneOn q.neckRadius (Ici 0))
    (Ho : RetainedCoreHistory.{u}) (Tno : Icc (0 : ℝ) Ho.toHistory.horizon)
    (pTo : (Ho.toHistory.stageAt Tno).Carrier) {r : ℝ} (hr : 0 < r) {A Tf R : ℝ} (hA : 0 < A)
    (hTf : Tf ≤ (Tno : ℝ)) (h2r : 2 * r ^ 2 < (Tno : ℝ))
    (hvolo : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (Ho.toHistory.stageMetric
      (Ho.toHistory.activeStage Tno) Tno) pTo r)
    (hR1 : 1 ≤ R)
    (hRρ : R ≤ ((q.rescale_P6N (r ^ 2) (pow_pos hr 2)).neckRadius
      (Ho.rescaleTime_P6X (pow_pos hr 2) Tno) ^ 2)⁻¹) :
    Tf / r ^ 2 ≤ (Ho.rescaleTime_P6X (pow_pos hr 2) Tno : ℝ) ∧
    2 * (1 : ℝ) ^ 2 < (Ho.rescaleTime_P6X (pow_pos hr 2) Tno : ℝ) ∧
    ENNReal.ofReal ((A + 3)⁻¹ * (1 : ℝ) ^ 3) ≤
      ballVolume ((Ho.rescale_P6N (r ^ 2) (pow_pos hr 2)).toHistory.stageMetric
        ((Ho.rescale_P6N (r ^ 2) (pow_pos hr 2)).toHistory.activeStage
          (Ho.rescaleTime_P6X (pow_pos hr 2) Tno)) (Ho.rescaleTime_P6X (pow_pos hr 2) Tno))
        (Ho.castRescale_P6X (pow_pos hr 2) Tno pTo) 1 ∧
    ∀ w : ℝ, (Ho.rescaleTime_P6X (pow_pos hr 2) Tno : ℝ) - 1 ^ 2 / 2 ≤ w →
      w ≤ (Ho.rescaleTime_P6X (pow_pos hr 2) Tno : ℝ) →
      (fun w => (fun w => q.neckRadius (4 * w / 3)) (r ^ 2 * w) / Real.sqrt (r ^ 2)) w ≤ 1 := by
  have hc : 0 < r ^ 2 := pow_pos hr 2
  have hTnv : (Ho.rescaleTime_P6X hc Tno : ℝ) = (Tno : ℝ) / r ^ 2 := rfl
  have hcT : r ^ 2 * ((Tno : ℝ) / r ^ 2) = Tno := mul_div_cancel₀ _ hc.ne'
  have hTno0 : (0 : ℝ) ≤ (Tno : ℝ) := Tno.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hTnv]
    exact div_le_div_of_nonneg_right hTf hc.le
  · rw [hTnv, lt_div_iff₀ hc]
    linarith
  · have hr1 : r / Real.sqrt (r ^ 2) = 1 := by
      rw [Real.sqrt_sq hr.le, div_self hr.ne']
    have hvolK := (RetainedCoreHistory.le_ballVolume_castRescale_iff_CXSP hc
      (v := Tno) (p := pTo) (κ := A⁻¹) (r := r)).mpr hvolo
    rw [hr1] at hvolK
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hvolK
    have : (A + 3)⁻¹ ≤ A⁻¹ := inv_anti₀ hA (by linarith)
    nlinarith
  · have hρT : q.neckRadius Tno ≤ Real.sqrt (r ^ 2) := by
      have hρ0 : 0 < q.neckRadius Tno := q.neckRadius_pos _ hTno0
      have hR := hRρ
      rw [RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X hc q, hTnv, hcT] at hR
      have hq2 : 0 < q.neckRadius Tno ^ 2 := by positivity
      have h1c : 1 ≤ r ^ 2 * (q.neckRadius Tno ^ 2)⁻¹ := hR1.trans hR
      have hsq : q.neckRadius Tno ^ 2 ≤ r ^ 2 := by
        have := mul_le_mul_of_nonneg_right h1c hq2.le
        rwa [one_mul, mul_assoc, inv_mul_cancel₀ hq2.ne', mul_one] at this
      exact Real.le_sqrt_of_sq_le hsq
    intro w hw1 _
    change q.neckRadius (4 * (r ^ 2 * w) / 3) / Real.sqrt (r ^ 2) ≤ 1
    have hcw : (Tno : ℝ) - r ^ 2 / 2 ≤ r ^ 2 * w := by
      rw [hTnv] at hw1
      have := mul_le_mul_of_nonneg_left hw1 hc.le
      rw [mul_sub, hcT] at this
      linarith
    have hle : (Tno : ℝ) ≤ 4 * (r ^ 2 * w) / 3 := by linarith
    have hanti' := hanti (show (Tno : ℝ) ∈ Ici 0 from hTno0)
      (show 4 * (r ^ 2 * w) / 3 ∈ Ici (0 : ℝ) from le_trans hTno0 hle) hle
    rw [div_le_one (Real.sqrt_pos.mpr hc)]
    exact hanti'.trans hρT

end ObservedHistory

open ObservedHistory

/-- **hgap J11 binder（`_J11S`，PROVISIONAL[`hfamT`, `hDextJ`]）**：结论 = KT2c `hJ11` 逐字。 -/
theorem hJ11_loc_of_depthExt_J11S :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric}
      {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
      (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ) {Ctime₀ : ℝ≥0} {a₀ : ℝ}
      {T₀ Qt : ℕ → ℝ} {qp : CutoffParameters},
    AntitoneOn q.neckRadius (Ici 0) →
    (∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory) →
    0 ≤ C2 → StandardCap.transitionEnd + 10 < qp.modelRadius → qp.modelAccuracy ≤ ε₀ →
    2 ≤ qp.modelOrder → Tendsto qp.delta atTop (𝓝 0) →
    (
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∃ (a₀ T₀ : ℕ → ℝ) (records : ∀ k (e : Fin (Kh k).eventCount),
            T₀ k ≤ (Kh k).time e.succ →
              GeometricCutoffRecord (Kh k) e (qp.rescale_P6N (c k) (hc k))),
          (∀ k, 0 ≤ a₀ k) ∧
          (∀ k (τ : Icc (0 : ℝ) (Kh k).horizon) (x : ((Kh k).stageAt τ).Carrier),
            InFixedHamiltonIveyRegion ((Kh k).stageMetric ((Kh k).activeStage τ) τ)
              (a₀ k + τ) x) ∧
          (∀ k, T₀ k ≤ (aSeed k : ℝ)) ∧
          (∀ k (e : Fin (Kh k).eventCount), T₀ k ≤ (Kh k).time e.succ →
            ((Kh k).event e).old = ((Kh k).event e).transition.trace.retainedCore) ∧
          (∀ k (e : Fin (Kh k).eventCount) (he : T₀ k ≤ (Kh k).time e.succ) b,
            ((records k e he).static b).hasCanonicalWindow) ∧
          (∀ k, riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) ≠ ⊤) ∧
          ∀ᶠ k in atTop, WindowNeckScaleBudget_P6HS (Kh k) (qp.rescale_P6N (c k) (hc k))
            (T₀ k) (aSeed k : ℝ) (R k)
    ) →
    (∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T) →
    ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        let Qs : ℕ → ℝ := fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount),
            max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ →
              GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time
            i.succ → q.delta ((Ho n).time i.succ) ≤ δ₀ Ctime₀ n) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ ζ Ctime₀ n) →
          (∀ n : ℕ, Rn Ctime₀ n ≤ (p n).modelRadius) →
          (∀ n : ℕ, m₀ Ctime₀ n ≤ (p n).modelOrder) →
          (∀ n i hi b, max (0 : ℝ) 1 ≤ Cb Ctime₀ n * ((recordsK n i hi).static b).neck.scale) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) →
          (∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
            (p n).recenterConstant * (p n).delta τ ≤ 1 / 2) →
          (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → ∀ n (i : Fin (Ho n).eventCount),
            (Ho n).time i.succ ∈ Icc (τ / 2) τ →
            ∀ (hi : max (T₀ n) (c n * ((σ n : ℝ) - L n / R n)) ≤ (Ho n).time i.succ) h,
              (recordsK n i hi).nominalRadius h ≤ ε * q.neckRadius τ) →
          (∃ κd : ℝ, 0 < κd ∧ ∀ D Lv B : ℝ, 0 < D → 0 < Lv → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Ho n).toHistory.stageMetric
            ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).uncastRescale_P6CK (hc n) (σ n) (y n)) (D / Real.sqrt (R n / c n)),
        ∀ (v : Icc (0 : ℝ) (Ho n).toHistory.horizon)
          (hvt : v ≤ (Ho n).unscaleTime_P6X (hc n) (σ n)),
          (((Ho n).unscaleTime_P6X (hc n) (σ n) : Icc (0 : ℝ) (Ho n).toHistory.horizon) : ℝ) -
            B / (R n / c n) ≤ v →
        ∀ tr : BackwardPointTrace (Ho n).toHistory ((Ho n).toHistory.activeStage v)
          ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
          ((Ho n).toHistory.activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ Lv →
          (Ho n).toHistory.isParabolicallyRmControlledBall v
            (tr.point ((Ho n).toHistory.activeStage v) le_rfl
              ((Ho n).toHistory.activeStage_mono hvt))
            (ϱ / Real.sqrt (R n / c n)) →
          ENNReal.ofReal (κd * ϱ ^ 3) ≤
            ballVolume (scaleMetric (R n / c n) (div_pos (hRpos n) (hc n))
              ((Ho n).toHistory.stageMetric ((Ho n).toHistory.activeStage v) v))
              (tr.point ((Ho n).toHistory.activeStage v) le_rfl
                ((Ho n).toHistory.activeStage_mono hvt)) ϱ)) := by
  obtain ⟨ε₀, hε₀, hST⟩ := hstay_interior_tower_J11S.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F q ε C1 C2 Ctime Cb Rn ζ δ₀ m₀ Ctime₀ a₀ T₀ Qt qp hanti hfresh hC2 hDm hacc hm hδlim
    hfamT hDextJ A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm
    hlate seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ
    hroom hball hdistσ hev hlt Qs p recordsK _ _ _ _ _ _ _ _ _ _
  have hDext := hDextJ A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  have hTc : ∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ) := fun k => by
    change (k : ℝ) + 1 ≤ c k * ((Ho k).rescaleTime_P6X (hc k) (Tno k) : ℝ)
    rw [(Ho k).mul_rescaleTime_P6X (hc k) (Tno k)]
    exact hk k
  have hσH : ∀ k, (σ k : ℝ) < (Kh k).horizon := fun k => by
    obtain ⟨j, -, hj⟩ := hev k
    exact lt_of_lt_of_le hj ((Kh k).time_le_horizon_at _)
  have hRr' : ∀ k : ℕ, (k : ℝ) + 1 ≤ R k := hRr
  have hstayK := fun (T r' : ℝ) (hT : 0 < T) (hr' : 0 < r') =>
    hST hC2 hDm hacc hm hδlim hfamT T r' hT hr' ind c hc Tn pT hTc aSeed haT hclock h1 hsm
      seedTrace σ y R hsT has L hRdef hRpos hRr' hL hsel hgood hwin hwin' hRt hradii hσH
  have hfpL := ObservedHistory.hfpL_hPN_of_depthExt_J11S (haT := haT) seedTrace σ y R hsT has L
    hRpos hL
      hstayK hDext hdistσ
  obtain ⟨κ, hκ, Tf, hsup⟩ := hfresh (A + 3) (by linarith)
  have hsupK := GC.LongTime.Ch11.fresh_rescale_adapter_P6JA hsup ind c hc
  have hA0 : (0 : ℝ) < A := by linarith
  have hR1 : ∀ k, (1 : ℝ) ≤ R k := fun k => by
    have := hRr k
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hprep0 := fun k => freshK_prep_J11S hanti (Ho k) (Tno k) (pTo k) (hr k) hA0
    (Tno k).2.1 (h2r k) (hvolo k) (hR1 k) (hRρ k)
  have hTf : ∀ᶠ k in atTop, Tf / c k ≤ (Tn k : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_ge Tf
    filter_upwards [eventually_ge_atTop N] with k hkN
    have h1' : (N : ℝ) ≤ k := by exact_mod_cast hkN
    exact (freshK_prep_J11S hanti (Ho k) (Tno k) (pTo k) (hr k) hA0
      (by linarith [hk k]) (h2r k) (hvolo k) (hR1 k) (hRρ k)).1
  exact hJ11_of_fresh_fpL_J11S (Ho := Ho) (c := c) (haT := haT) hc seedTrace σ y R hsT hκ hRpos
    (fun k w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (fun k => Tf / c k)
    hsupK hTf (fun k => (hprep0 k).2.1) hsm (fun k => (hprep0 k).2.2.1)
    (fun k => (hprep0 k).2.2.2) hclock hwin hwin' hradii hfpL

/-- **consumer（`_J11S`）**：G3c 的输出逐字喂 KT2c event producer 的 `hJ11` 槽（部分应用到 `hJ11`）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (Cb Rn ζ δ₀ : ℝ≥0 → ℕ → ℝ) (m₀ : ℝ≥0 → ℕ → ℕ)
    (hCb : ∀ (C : ℝ≥0) (n : ℕ), 0 < Cb C n ∧ Cb C n ≤ 1 / ((n : ℝ) + 1) ^ 2)
    (hζ : ∀ (C : ℝ≥0) (n : ℕ), 0 < ζ C n) (hδ₀ : ∀ (C : ℝ≥0) (n : ℕ), 0 < δ₀ C n)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    {Ctime₀ : ℝ≥0} (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime₀)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    {T₀ Qt : ℕ → ℝ}
    (hT₀ : ∀ n, lateThrJ_P6WR (fun n => Cb Ctime₀ n) (fun n => Rn Ctime₀ n) (fun n => ζ Ctime₀ n)
      (fun n => δ₀ Ctime₀ n) (fun n => m₀ Ctime₀ n) a₀ hP5L hδq hanti n ≤ T₀ n)
    {qp : CutoffParameters}
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory)
    (hW : ∀ ε₀ : ℝ, 0 < ε₀ → qp.modelAccuracy ≤ ε₀) (hC2 : 0 ≤ C2)
    (hDm : StandardCap.transitionEnd + 10 < qp.modelRadius) (hm : 2 ≤ qp.modelOrder)
    (hδlim : Tendsto qp.delta atTop (𝓝 0)) : True := by
  obtain ⟨ε₀, hε₀, h⟩ := hJ11_loc_of_depthExt_J11S.{u}
  have hJ := fun hfamT hDextJ => h (T₀ := T₀) (Qt := Qt) (a₀ := a₀) (Ctime₀ := Ctime₀) (ε := ε)
    (C1 := C1) (C2 := C2) (Ctime := Ctime) Cb Rn ζ δ₀ m₀ hanti hfresh hC2 hDm (hW ε₀ hε₀) hm
    hδlim hfamT hDextJ
  have _ := fun hfamT hDextJ => hgapJ_loc_of_producers_P6KT2c (ε := ε) (C1 := C1) (C2 := C2)
    (Ctime := Ctime) Cb Rn ζ δ₀ m₀ hCb hζ hδ₀ hanti hP5L hδq records hTD ha₀ hHI hT₀
    (hJ hfamT hDextJ)
  trivial

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
