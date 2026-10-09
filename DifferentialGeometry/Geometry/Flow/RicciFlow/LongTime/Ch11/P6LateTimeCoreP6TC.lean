import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateTimeCoreDefP6TC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NormalizePrefixP6X3

/-!
# 时间版 normalized-prefix 反证：`canonicalLateTimeCore_of_normalized_prefix_P6TC`（O-CH11-P6TIME G2a）

R-C11-14 D-2 / G0 (a)：jointD 链上**唯一**的空间投影点是 `lateCoreAt_of_normalized_prefix_P6X3`
（P6NormalizePrefixP6X3.lean L52–256）：它的反例取 `¬∃W` 坏点，并以
`noWitness_castRescale_P6X … hG.1` 喂 retained selector 的 `hbad`。本文件：
* **`noGood_castRescale_P6TC`**：`¬HSCTC` 坏点重标度（`c = r²`）后仍 `¬HSCTC`——空间分量走
  `noWitness_castRescale_P6X`，时间分量走树内 `derivWithin_rescale_iff_P6X`（`∂R̃ = c²∂R`、`Ctime` 不变），
  前件 `time (activeStage) < v`、`v < horizon` 同除 `c`；
* `lateTimeCoreAt_mono_P6TC`：单个 `A` 的时间版对 `A` 向下单调（照 `lateCoreAt_mono_P6X`）；
* **`lateTimeCoreAt_of_normalized_prefix_P6TC`** /
  **`canonicalLateTimeCore_of_normalized_prefix_P6TC`**：binder（`hanti hcan hder T₀ Qt hPN`）
  与 `_P6X3` 原文逐字相同；证明照抄，只把坏点谓词换成 `¬HSCTC`、`hbad` 换成
  `noGood_castRescale_P6TC`，结论换时间版。
陈述由 build-logs/scratch/O-CH11-P6TIME/mk_g2.py 从 `P6NormalizePrefixP6X3.lean`
（sha256 e7647c09a841df4b…）逐字抽取 + 定点替换生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace RetainedCoreHistory

/-- **`¬HSCTC` 坏点重标度后仍 `¬HSCTC`**（`c > 0`，同 `ε C1 C2 Ctime`）。 -/
theorem noGood_castRescale_P6TC (H : RetainedCoreHistory.{u}) {c : ℝ} (hc : 0 < c)
    (v : Icc (0 : ℝ) H.toHistory.horizon) (x : (H.toHistory.stageAt v).Carrier)
    {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (h : ¬ H.toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v x) :
    ¬ (H.rescale_P6N c hc).toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ctime
        (H.rescaleTime_P6X hc v) (H.castRescale_P6X hc v x) := by
  rintro ⟨hW, hD⟩
  refine h ⟨?_, fun hlo hhi => ?_⟩
  · by_contra hW0
    exact H.noWitness_castRescale_P6X hc v x hW0 hW
  · have hj := H.activeStage_rescaleTime_P6X hc v
    have hlo' : (H.rescale_P6N c hc).toHistory.time
        ((H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc v)) <
          ((H.rescaleTime_P6X hc v : Icc (0 : ℝ) (H.rescale_P6N c hc).toHistory.horizon) : ℝ) := by
      rw [hj]
      change H.time (H.toHistory.activeStage v) / c < (v : ℝ) / c
      exact div_lt_div_of_pos_right hlo hc
    have hhi' : ((H.rescaleTime_P6X hc v : Icc (0 : ℝ) (H.rescale_P6N c hc).toHistory.horizon) :
        ℝ) < (H.rescale_P6N c hc).toHistory.horizon := by
      change (v : ℝ) / c < H.horizon / c
      exact div_lt_div_of_pos_right hhi hc
    have h1 := (H.derivWithin_rescale_iff_P6X hc
      (j := (H.rescale_P6N c hc).toHistory.activeStage (H.rescaleTime_P6X hc v))
      (t := H.rescaleTime_P6X hc v) (z := H.castRescale_P6X hc v x) (Ctime := Ctime)).mp
      (hD hlo' hhi')
    rw [H.mul_rescaleTime_P6X hc v] at h1
    exact (carrier_transfer_P6X (S := H.stage)
      (Pr := fun j z => |derivWithin (fun s => metricScalarAt (H.toHistory.stageMetric j s) z)
          (Iic (v : ℝ)) v| ≤ Ctime * metricScalarAt (H.toHistory.stageMetric j v) z ^ 2)
      hj (H.heq_castRescale_P6X hc v x)).mp h1

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.LongTime.Ch11

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

/-- 单个 `A` 的时间版对 `A` 向下单调（照抄 `lateCoreAt_mono_P6X`，输出换 HSCTC）。 -/
theorem lateTimeCoreAt_mono_P6TC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {A A' : ℝ}
    (h :
      ∃ K₁ T : ℝ, 0 < K₁ ∧ 0 < T ∧
        ∀ n, let H := (F.tower.history n).toHistory;
        ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
          T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
          ENNReal.ofReal (A'⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
          ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A' * r),
            K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
            H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime t y)
    (hA : 0 < A) (hAA : A ≤ A') :
    ∃ K₁ T : ℝ, 0 < K₁ ∧ 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
          K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
          H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime t y := by
  obtain ⟨K₁, T, hK₁, hT, hB⟩ := h
  refine ⟨K₁, T, hK₁, hT, fun n t p r hTt ht hs hv y hy hK => ?_⟩
  have hv' : ENNReal.ofReal (A'⁻¹ * r ^ 3) ≤ ballVolume
      ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) p r := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hv
    have hr : 0 < r := hs.1
    have : A'⁻¹ ≤ A⁻¹ := inv_anti₀ hA hAA
    have h3 : 0 < r ^ 3 := by positivity
    nlinarith
  have hr : 0 < r := hs.1
  exact hB n t p r hTt ht hs hv' y (riemannianBallOf_mono _ _ (by nlinarith) hy) hK

/-- **(b) 时间版于单个 `A > 1` ⇐ S5 + S11 + `hPNP`**：照抄 `lateCoreAt_of_normalized_prefix_P6X3`，坏点谓词
`¬∃W` → `¬HSCTC`（不做空间投影）。 -/
theorem lateTimeCoreAt_of_normalized_prefix_P6TC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime) (T₀ Qt : ℕ → ℝ)
    (hPN : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
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
        False)
    {A : ℝ} (hA : 1 < A) :
    ∃ K₁ T : ℝ, 0 < K₁ ∧ 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) → 2 * r ^ 2 < (t : ℝ) → hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p (A * r),
          K₁ * (r ^ 2)⁻¹ ≤ metricScalarAt (H.stageMetric (H.activeStage t) t) y →
          H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime t y := by
  by_contra hcon
  have hk : ∀ k : ℕ, ∃ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (p : ((F.tower.history n).toHistory.stageAt t).Carrier) (r : ℝ)
      (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
      (k : ℝ) + 1 ≤ (t : ℝ) ∧ 2 * T₀ k ≤ (t : ℝ) ∧ 2 * r ^ 2 < (t : ℝ) ∧
      hasSmallParabolicCurvature (F.tower.history n).toHistory t p r ∧
      ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) p r ∧
      x ∈ riemannianBallOf ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) p (A * r) ∧
      max ((k : ℝ) + 1) (Qt k + 1) * (r ^ 2)⁻¹ ≤ metricScalarAt
        ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage t) t) x ∧
      ¬ (F.tower.history n).toHistory.HasSpatialCanonicalTimeControl ε C1 C2 Ctime t x := by
    intro k
    by_contra hk
    refine hcon ⟨max ((k : ℝ) + 1) (Qt k + 1), max ((k : ℝ) + 1) (2 * T₀ k),
      lt_max_of_lt_left (by positivity), lt_max_of_lt_left (by positivity), ?_⟩
    intro n _ t p r hT ht hs hv x hx hK
    by_contra hW
    exact hk ⟨n, t, p, r, x, (le_max_left _ _).trans hT, (le_max_right _ _).trans hT, ht, hs, hv,
      hx, hK, hW⟩
  choose ind Tn pT r x hlate hlateT₀ htime hsmall hvol hx hK hbad0 using hk
  have hr : ∀ k, 0 < r k := fun k => (hsmall k).1
  have hseed : ∀ k, ∃ (a : Icc (0 : ℝ) (F.tower.history (ind k)).toHistory.horizon)
      (hat : a ≤ Tn k), (a : ℝ) = (Tn k : ℝ) - r k ^ 2 ∧
      Nonempty (BackwardPointTrace (F.tower.history (ind k)).toHistory
        ((F.tower.history (ind k)).toHistory.activeStage a)
        ((F.tower.history (ind k)).toHistory.activeStage (Tn k))
        ((F.tower.history (ind k)).toHistory.activeStage_mono hat) (pT k)) := fun k => by
    obtain ⟨hrk, a, hat, ha, htr⟩ := hsmall k
    have hp : pT k ∈ riemannianBallOf ((F.tower.history (ind k)).toHistory.stageMetric
        ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (pT k) (r k) := by
      change riemannianEDistOf _ (pT k) (pT k) < ENNReal.ofReal (r k)
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hrk
    obtain ⟨tr, -⟩ := htr (pT k) hp
    exact ⟨a, hat, ha, ⟨tr⟩⟩
  choose aSeed haT hclock hst using hseed
  have hc : ∀ k, 0 < r k ^ 2 := fun k => pow_pos (hr k) 2
  have hsq : ∀ k, Real.sqrt (r k ^ 2) = r k := fun k => Real.sqrt_sq (hr k).le
  have hRx : ∀ k : ℕ, max ((k : ℝ) + 1) (Qt k + 1) ≤ r k ^ 2 * metricScalarAt
      ((F.tower.history (ind k)).toHistory.stageMetric
        ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (x k) := by
    intro k
    have := mul_le_mul_of_nonneg_left (hK k) (hc k).le
    rwa [← mul_assoc, mul_comm (r k ^ 2), mul_assoc, mul_inv_cancel₀ (hc k).ne', mul_one] at this
  have hRx' : ∀ k : ℕ, max ((k : ℝ) + 1) (Qt k + 1) ≤ metricScalarAt
      (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.stageMetric
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.activeStage
          ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
        ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
      ((F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k)) := fun k => by
    rw [(F.tower.history (ind k)).scalar_castRescale_P6X (hc k)]
    exact hRx k
  have hxb : ∀ k, (F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k) ∈
      riemannianBallOf
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.stageMetric
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.activeStage
          ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
        ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
      ((F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (pT k)) (A * 1) := fun k => by
    have h := (F.tower.history (ind k)).ball_castRescale_P6X (hc k) (Tn k) (pT k) (x k) (hx k)
    rwa [hsq k, mul_div_assoc, div_self (hr k).ne'] at h
  have hclock' : ∀ k, (((F.tower.history (ind k)).rescaleTime_P6X (hc k) (aSeed k) :
      Icc (0 : ℝ) ((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.horizon) :
        ℝ) = ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k) : ℝ) - 1 ^ 2 := fun k => by
    change (aSeed k : ℝ) / r k ^ 2 = (Tn k : ℝ) / r k ^ 2 - 1 ^ 2
    rw [hclock k, sub_div, div_self (hc k).ne', one_pow]
  have hRx0 : ∀ k : ℕ, (k : ℝ) + 1 ≤ metricScalarAt
      (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.stageMetric
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.activeStage
          ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
        ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
      ((F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k)) :=
    fun k => (le_max_left _ _).trans (hRx' k)
  have hRpos0 : ∀ k, 0 < metricScalarAt
      (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.stageMetric
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.activeStage
          ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
        ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
      ((F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k)) :=
    fun k => lt_of_lt_of_le (by positivity) (hRx0 k)
  have hdiv : Tendsto (fun k => metricScalarAt
      (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.stageMetric
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.activeStage
          ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
        ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
      ((F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k))
      * (fun _ : ℕ => (1 : ℝ)) k ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun k : ℕ => by rw [one_pow, mul_one]; linarith [hRx0 k])
      tendsto_natCast_atTop_atTop
  have hA0 : 0 < A := zero_lt_one.trans hA
  have hsel := ObservedHistory.selection_of_bad_sequence_retained_P6R2
    (Kh := fun k => ((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory)
    (fun k => q.rescale_P6N (r k ^ 2) (hc k)) le_rfl le_rfl le_rfl
    (fun k => RetainedCoreHistory.neckRadius_rescale_antitone_P6X (hc k) hanti)
    (fun k => (F.tower.history (ind k)).canonical_rescale_P6X (hc k) (hcan (ind k)))
    (fun k => (F.tower.history (ind k)).derivative_rescale_P6X (hc k)
      (fun v z hlo hhi hR =>
        stageDerivative_of_timeDerivativeSupply_P6X hder (ind k) v z hlo hhi hR))
    (fun k => (F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k))
    (fun k => (F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (pT k))
    (fun _ => 1) A (fun _ => one_pos) hA0
    (fun k => (F.tower.history (ind k)).rescaleTime_P6X (hc k) (aSeed k))
    (fun k => (F.tower.history (ind k)).rescaleTime_mono_P6X (hc k) (haT k)) hclock'
    (fun k => (F.tower.history (ind k)).seedTrace_rescale_P6X (hc k) (haT k) (hst k).some)
    (fun k => (F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k)) hxb hRpos0
    (fun k => (F.tower.history (ind k)).noGood_castRescale_P6TC (hc k) (Tn k) (x k) (hbad0 k))
    hdiv
  obtain ⟨σ, y, R, hsT, has, L, ⟨hRdef, hRpos, hRle, hQρ, hL, hbad, hgood, hwin, hwin', hroomT,
    hradii⟩, hLdef, hroom, hball⟩ := hsel
  have hdistσ := ObservedHistory.hdistσ_of_retained_P6R2 (Aκ := A + 3)
    (haT := fun k => (F.tower.history (ind k)).rescaleTime_mono_P6X (hc k) (haT k)) (hsT := hsT)
    (has := has) hA0 le_rfl (fun _ => one_pos) hRpos0 hRle hLdef hdiv hball
  have hsmallR : ∀ k, hasSmallParabolicCurvature
      ((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory
      ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k))
      ((F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (pT k)) 1 := fun k => by
    have h := (F.tower.history (ind k)).hasSmallParabolicCurvature_rescale_P6X3 (hc k) (Tn k)
      (pT k) (hsmall k)
    rwa [hsq k, div_self (hr k).ne'] at h
  have hT₀l : ∀ k, T₀ k ≤ r k ^ 2 *
      ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (aSeed k) : ℝ) := fun k => by
    rw [(F.tower.history (ind k)).mul_rescaleTime_P6X (hc k), hclock k]
    linarith [hlateT₀ k, htime k]
  have hQR : ∀ k, Qt k < R k := fun k => by
    have := (le_max_right _ _).trans ((hRx' k).trans (hRle k))
    linarith
  refine hPN A hA ind Tn pT r hr hlate htime hsmall hvol
    (fun k => (F.tower.history (ind k)).rescaleTime_P6X (hc k) (aSeed k))
    (fun k => (F.tower.history (ind k)).rescaleTime_mono_P6X (hc k) (haT k)) hclock'
    (fun k => ?_) hsmallR hT₀l
    (fun k => (F.tower.history (ind k)).seedTrace_rescale_P6X (hc k) (haT k) (hst k).some)
    σ y R hsT has L hRdef hRpos (fun k => (hRx0 k).trans (hRle k)) hQR hL hbad hgood hwin hwin'
    hroomT hradii hQρ hroom hball hdistσ
  rw [hclock' k]
  change 1 ≤ (Tn k : ℝ) / r k ^ 2 - 1 ^ 2
  rw [le_sub_iff_add_le, le_div_iff₀ (hc k)]
  linarith [htime k]

/-- **(b) 时间版 ⇐ S5 + S11 + `hPNP`**（binder 与 `canonicalLateCore_of_normalized_prefix_P6X3` 逐字相同；
`A ≤ 1` 借 `max A 2`）。 -/
theorem canonicalLateTimeCore_of_normalized_prefix_P6TC {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime) (T₀ Qt : ℕ → ℝ)
    (hPN : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
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
        False) :
    CanonicalLateTimeCore_P6X F ε C1 C2 Ctime := by
  intro A hA
  have hA2 : 1 < max A 2 := lt_of_lt_of_le one_lt_two (le_max_right _ _)
  exact lateTimeCoreAt_mono_P6TC
    (lateTimeCoreAt_of_normalized_prefix_P6TC hanti hcan hder T₀ Qt hPN hA2) hA (le_max_left _ _)

/-- 投影回旧形：时间版 normalized-prefix ⇒ 原 `canonicalLateCore_of_normalized_prefix_P6X3` 的结论。 -/
example : type_of% @canonicalLateCore_of_normalized_prefix_P6X3.{u} := by
  intro P g F q ε C1 C2 Ctime hanti hcan hder T₀ Qt hPN
  exact canonicalLateCore_of_timeCore_P6TC
    (canonicalLateTimeCore_of_normalized_prefix_P6TC hanti hcan hder T₀ Qt hPN)

end GC.LongTime.Ch11
