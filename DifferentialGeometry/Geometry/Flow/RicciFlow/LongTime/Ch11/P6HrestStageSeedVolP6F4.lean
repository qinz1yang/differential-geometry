import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HrestJointPrefixP6HP3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6VolumeRescaleCXSP

/-!
# HP3 stage 的 seedVol 孪生：hfootE′ 在实际 family 上付 hseedVol（O-CH11-FOOT4 G1 consumer，`_P6F4`）

R-C11-17 D-8(i)：hseedVol 须传到 stage / HRESTP 消费面。hfootE 唯一实际喂 family 的地方是 HP3 stage
`hbd_stage_jointPrefix_P6HP3`（HB4 只把 hfootE 交给同一 family；上层 HP3 Assemble / Top、G7B BadTop、
FINCOARSE G3、HTUBERET G1 只透传 binder）。该处 family 是 joint prefix 的原 seed `(Ho, Tno, pTo, r)` 经
`c = r²` 重标度，前缀自带 `hvolo : A⁻¹r³ ≤ Vol(B(pTo, r))`（`1 < A`）。
* `seedVol_of_orig_P6F4`（PROVED）：`hvolo` ⇒ 重标度 `hseedVol(A)`（`le_ballVolume_castRescale_iff_CXSP`）。
* `hbd_stage_jointPrefix_seedVol_P6F4`：结论逐字；`hfootE` 槽 → `hfootE′`
  （G1 `hfootEA_of_localSupplies_seedVol_P6F4` 的输出形），在 `Aseed := A` 实例化。其余 binder（`hcapWL hcenE
  htransE hrerunE8' hcan₁ hanti hT₀m`）逐字。
陈述由 build-logs/scratch/O-CH11-FOOT4/gen/gen_g1b.py 从 `P6HrestJointPrefixP6HP3.lean` 逐字抽取
+ 定点插入生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn

namespace ObservedHistory

/-- **原尺度 seed 体积 ⇒ 重标度 `hseedVol`（`_P6F4`，PROVED）**：`A⁻¹r³ ≤ Vol_{g(v)}(B(p, r))` ⇒ 在
`c = r²` 的重标度 history 上 `A⁻¹·1³ ≤ Vol(B(p̃, 1))`（`le_ballVolume_castRescale_iff_CXSP`，`r/√(r²) =
  1`）。
右端写成 FOOT3 `hseedVol` 的 `riemannianVolumeMeasure` 展开形。 -/
theorem seedVol_of_orig_P6F4 (H : RetainedCoreHistory.{u}) {r : ℝ} (hr : 0 < r) (hc : 0 < r ^ 2)
    {v : Icc (0 : ℝ) H.toHistory.horizon} {p : (H.toHistory.stageAt v).Carrier} {A : ℝ}
    (hvol : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤
      ballVolume (H.toHistory.stageMetric (H.toHistory.activeStage v) v) p r) :
    ENNReal.ofReal (A⁻¹ * 1 ^ 3) ≤
      riemannianVolumeMeasure ThreeModel
        ((H.rescale_P6N (r ^ 2) hc).toHistory.stageAt (H.rescaleTime_P6X hc v)).Carrier
        ((H.rescale_P6N (r ^ 2) hc).toHistory.stageMetric
          ((H.rescale_P6N (r ^ 2) hc).toHistory.activeStage (H.rescaleTime_P6X hc v))
          (H.rescaleTime_P6X hc v))
        (riemannianBallOf ((H.rescale_P6N (r ^ 2) hc).toHistory.stageMetric
          ((H.rescale_P6N (r ^ 2) hc).toHistory.activeStage (H.rescaleTime_P6X hc v))
          (H.rescaleTime_P6X hc v)) (H.castRescale_P6X hc v p) 1) := by
  have hs : r / Real.sqrt (r ^ 2) = 1 := by
    rw [Real.sqrt_sq hr.le, div_self hr.ne']
  have h := (H.le_ballVolume_castRescale_iff_CXSP hc (v := v) (p := p) (κ := A⁻¹) (r := r)).2 hvol
  rw [hs] at h
  exact h

/-- **HP3 stage seedVol 孪生（`_P6F4`，PROVISIONAL：binder 同 `hbd_stage_jointPrefix_P6HP3`）**：结论逐字
（hrestP joint prefix + hstage 槽类前提）；唯一槽形变化 `hfootE` → `hfootE′`
（`∀ Aseed : ℝ, 1 < Aseed →` + 前缀 `hseedVol(Aseed)`，与 FOOT3 / G1 逐字同一行）。**实付**：此处 family
= 原 seed `(Ho, Tno, pTo, r)` 的 `c = r²` 重标度，`hseedVol(A)` 由前缀 `hvolo`（`A⁻¹r³ ≤ Vol(B(pTo, r))`）经
`seedVol_of_orig_P6F4` 给出，`Aseed := A`、`1 < A` 即 `hA`。证明其余逐字。 -/
theorem hbd_stage_jointPrefix_seedVol_P6F4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {T₀ Qt : ℕ → ℝ}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {C1f C2f m η₁ C1₁ C2₁ : ℝ} {kk : ℕ} {Ctime₁ : ℝ≥0}
    (hcapWL : ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
      let Kh : ℕ → ObservedHistory.{u} := fun k =>
        ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
      ∀ i : ∀ k, Fin (Kh k).eventCount,
        Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop →
        ∀ᶠ k in atTop, ∃ (pp : CutoffParameters) (Rc : GeometricCutoffRecord (Kh k) (i k) pp),
          ∀ (b : ((Kh k).event (i k)).RetainedBoundaryIndex) (x : ThreeBall),
            ∃ W : SpatialCanonicalWitness ((Kh k).event (i k)).outputMetric ε C1 C2
              ((Rc.static b).inclusion ((Rc.static b).witness.cap x)), W.capTubeHasNeckChart ε)
    (hcenE :
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
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ D : ((Kh k).event (i k)).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
          ∀ᶠ n in atTop, ∀ (t : Icc (0 : ℝ) (Kh k).horizon) (z : ((Kh k).stageAt t).Carrier),
            (t : ℝ) = D.v n → HEq z p' → ∀ (hav : aSeed k ≤ t) (hvt : t ≤ Tn k),
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage t) t)
                ((seedTrace k).point ((Kh k).activeStage t) ((Kh k).activeStage_mono hav)
                  ((Kh k).activeStage_mono hvt)) z ≤
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                  ((seedTrace k).point ((Kh k).activeStage (σ k))
                    ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                ENNReal.ofReal (L k / (4 * Real.sqrt (R k))))
    (hfootE : ∀ Aseed : ℝ, 1 < Aseed →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, ENNReal.ofReal (Aseed⁻¹ * 1 ^ 3) ≤
            riemannianVolumeMeasure ThreeModel ((Kh k).stageAt (Tn k)).Carrier
              ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
              (riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (Tn k)) (Tn k))
                (pT k) 1)) →
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
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          Nonempty (((Kh k).event (i k)).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk))
    (htransE :
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
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ D : ((Kh k).event (i k)).BufferedFootprintData_P6ST2 p' q ε C1f C2f m kk,
          (¬ ∃ W : SpatialCanonicalWitness ((Kh k).event (i k)).outputMetric ε C1 C2 q,
            W.capTubeHasNeckChart ε) →
          ∃ᶠ n in atTop, ¬ ∃ W : SpatialCanonicalWitness
            (((Kh k).event (i k)).incoming.flow.base.metric (D.v n)) η₁ C1₁ C2₁ p',
            W.capTubeHasNeckChart η₁)
    (hrerunE8' :
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
        (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
        Tendsto L atTop atTop →
        (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ k) (y k)) →
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
            8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
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
      False)
    (hcan₁ : GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius η₁ C1₁ C2₁)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (hT₀m : Monotone T₀) :
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
    (∀ k, ∃ i : Fin (Kh k).eventCount, (σ k : ℝ) = (Kh k).time i.succ) → False := by
  intro A hA ind Ho Tno pTo r hr hlate htime hsmallo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm
    hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ
    hroom hball hdistσ hS
  have hvolK := fun k => seedVol_of_orig_P6F4 (Ho k) (hr k) (hc k) (hvolo k)
  choose i hi using hS
  have hTc : ∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ) := fun k => by
    have e : c k * (Tn k : ℝ) = Tno k := by
      change r k ^ 2 * ((Tno k : ℝ) / r k ^ 2) = Tno k
      field_simp [(hr k).ne']
    rw [e]
    exact hlate k
  have hlate' : Tendsto (fun k => c k * (Kh k).time (i k).succ) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_)
      ((tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop).atTop_div_const
        two_pos)
    have hck := hc k
    have has' : (aSeed k : ℝ) ≤ σ k := Subtype.coe_le_coe.mpr (has k)
    have hcl := hclock k
    have h1k := h1 k
    have hT := hTc k
    rw [← hi k]
    nlinarith [mul_le_mul_of_nonneg_left has' hck.le,
      mul_nonneg hck.le (by nlinarith : (0 : ℝ) ≤ (Tn k : ℝ) - 2)]
  have hloc : ∀ᶠ k in atTop, aSeed k < σ k → 0 < L k →
      LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) (Kh k).horizon => (t : ℝ))
        (fun t z => ¬ ∃ W : SpatialCanonicalWitness
          ((Kh k).stageMetric ((Kh k).activeStage t) t) η₁ C1₁ C2₁ z,
          W.capTubeHasNeckChart η₁)
        (fun t z => metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage t) t) z)
        (fun t z => if h : aSeed k ≤ t ∧ t ≤ Tn k then
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage t) t)
            ((seedTrace k).point ((Kh k).activeStage t) ((Kh k).activeStage_mono h.1)
              ((Kh k).activeStage_mono h.2)) z
          else 0)
        (σ k) (R k) (L k)
        (riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
          ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
            ((Kh k).activeStage_mono (hsT k))) (y k)) := by
    filter_upwards [hcapWL ind c hc i hlate', hcenE ind c hc Tn pT hTc aSeed haT hclock h1 hsm
      seedTrace σ y R hsT has L hRdef hRpos hRr hL hsel hgood hwin hwin' hroomT hradii i hi,
      hfootE A hA ind c hc Tn pT hTc aSeed haT hclock h1 hsm hvolK seedTrace σ y R hsT has L hRdef
          hRpos hRr
      hL hsel hgood hwin hwin' hroomT hradii i hi,
      htransE ind c hc Tn pT hTc aSeed haT hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr
      hL hsel hgood hwin hwin' hroomT hradii i hi]
      with k hW hE hF hT
    intro hak _
    choose pp Rc hW using hW
    rw [hRdef k] at hE ⊢
    exact Rc.stage_localizedBad_trans_P6HB4 hW (haT k) (seedTrace k) (hsT k) (has k) (y k)
      (hi k) hak hE hF hT (hsel k)
  have hlo : ∀ k, (Kh k).time (i k).castSucc < σ k := fun k => by
    rw [hi k]
    exact (Kh k).time_strictMono (Fin.castSucc_lt_succ (i := i k))
  exact false_of_rerun_jointPrefix_P6HP
    (fun H s => ∃ j : Fin H.eventCount, H.time j.castSucc < (s : ℝ) ∧ (s : ℝ) < H.time j.succ)
    hrerunE8' hcan₁ hanti hT₀m A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock
    h1 hsm hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT
    hradii hQρ hroom hball hdistσ
    (fun k => (Kh k).time (i k).castSucc) hlo
    (fun k s hs1 hs2 => ⟨i k, hs1, hs2.trans_eq (hi k)⟩) hloc

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
