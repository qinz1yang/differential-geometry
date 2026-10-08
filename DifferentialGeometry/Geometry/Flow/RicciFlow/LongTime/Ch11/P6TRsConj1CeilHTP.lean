import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6R4DriverGateHCT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KframeHelpersDrvHI

set_option autoImplicit false

/-!
# HTRSPAY G1：hTRs conj1（hsepWK）⇐ recent + 天花板，及 R4 帧 event-slab pinching（后缀 `_HTP`）

* `conj1_of_recent_ceil_HTP`（PROVED）：hTRs conj1 的孪生形——在原前缀末（`∀ i` 之前）加 HCEILT gate 的
  天花板 `R k ≤ ρ̃(Tn k)⁻²`（`ρ̃ := (q.rescale_P6N c).neckRadius`；槽变弱，lead VAC2-DRV ALERT，R52 法）——
  由 env 的塔 records recent 供给（`hrec`）、`pF.delta → 0`、`q` 反单调与 `pF = q`（[0,∞) 上）付。
  逐事件用 `sepRhoPlus'_of_recentSupply_P6SF`（`T := Tn`，`hlate` 由 `Tn − ½ ≤ σ − T/R` 与 `Tn ≥ 2`），
  末步算术 = VAC2-DRV `conj1_of_recent_ceiling_V2D`（K₀ = 1）。无 ceiling 时不可付（V2D 缺口见证）。
* `curvatureLB_stage_of_eventPinched_HTP`（PROVED）：`v < time j.succ`（非 final 支）时 stage 曲率
  下界 ⇐ event slab ∩ `Ici w` 的 Φ-pinching（`curvatureOperatorLowerBoundAt_stage_of_pinched_DH`
  去 final 支）。
生成器 build-logs/scratch/HTRSPAY/gen/gA.py。
-/

noncomputable section

open Set Filter Function Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 算术核（= `conj1_of_recent_ceiling_V2D` 单点形，`K₀ = 1`）。 -/
theorem conj1_arith_HTP {A C Rk ρ2 S : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hρ1 : 1 ≤ ρ2)
    (hceil : Rk ≤ ρ2) (hS : (2 * (A + C) + 1) * ρ2 ≤ S) : 2 * max A (C * Rk) < S := by
  have h1 : A ≤ (A + C) * ρ2 := by nlinarith
  have h2 : C * Rk ≤ (A + C) * ρ2 := by nlinarith
  have hmax : max A (C * Rk) ≤ (A + C) * ρ2 := max_le h1 h2
  nlinarith

/-- **hTRs conj1 ⇐ recent + 天花板（`_HTP`，PROVED）**：见模块文档。 -/
theorem conj1_of_recent_ceil_HTP {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {pF q : CutoffParameters}
    (records : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e pF)
    (hpq : ∀ t : ℝ, 0 ≤ t → pF.neckRadius t = q.neckRadius t)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (hδ : Tendsto pF.delta atTop (𝓝 0))
    (hrec : ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
      ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
        (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
        ∀ h, (records n e).nominalRadius h ≤ η * pF.neckRadius t) :
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
        (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
      ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
      ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ k in atTop,
        ∀ (e : Fin (Kh k).eventCount) b, (σ k : ℝ) - T / R k < (Kh k).time e.succ →
          2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R k) <
            (((records (ind k) e).rescale_P6M (c k) (hc k)).static b).neck.scale := by
  intro ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef hRpos
    hRr hL hsel hgood haS hTnS hroom hradii hceil i hi T hT C hC
  have hantiF : AntitoneOn pF.neckRadius (Ici 0) := by
    intro a ha b hb hab
    rw [hpq a ha, hpq b hb]
    exact hanti ha hb hab
  set A : ℝ := 3 / ((1 : ℝ) / 100) ^ 2 with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; norm_num
  set N : ℝ := 2 * (A + C) + 1 with hNdef
  have hN1 : 1 ≤ N := by rw [hNdef]; linarith
  have hη : (0 : ℝ) < 1 / (N + 1) := by positivity
  have hηN : 2 * (1 / (N + 1)) ^ 2 * N ≤ 1 := by
    have hp : (0 : ℝ) < N + 1 := by linarith
    rw [div_pow, one_pow, ← mul_div_assoc, mul_one, div_mul_eq_mul_div,
      div_le_one (by positivity)]
    nlinarith
  obtain ⟨Trec, -, hTrec⟩ := hrec (1 / (N + 1)) hη
  obtain ⟨Tδ, -, hTδ⟩ := exists_late_recenter_CXW hδ
  obtain ⟨M, hM⟩ := exists_nat_ge (max Trec (2 * Tδ))
  filter_upwards [hTnS T hT, eventually_ge_atTop M] with k hk hkM e b hlt
  have hcTn : max Trec (2 * Tδ) ≤ c k * (Tn k : ℝ) := by
    have h1 : (M : ℝ) ≤ k := by exact_mod_cast hkM
    linarith [hTc k]
  have hTn2 : (2 : ℝ) ≤ Tn k := by linarith [hclock k, hone k]
  have htK : (Tn k : ℝ) - 1 / 2 ≤ (Kh k).time e.succ := by
    norm_num at hk ⊢
    linarith
  have hlate : (Tn k : ℝ) ≤ 2 * (Kh k).time e.succ := by linarith
  have hΛδ : (pF.rescale_P6N (c k) (hc k)).recenterConstant *
      (pF.rescale_P6N (c k) (hc k)).delta ((Kh k).time e.succ) ≤ 1 / 2 := by
    change pF.recenterConstant * pF.delta (c k * (Kh k).time e.succ) ≤ 1 / 2
    apply hTδ
    have h1 := mul_le_mul_of_nonneg_left hlate (hc k).le
    have h3 : 2 * Tδ ≤ c k * (Tn k : ℝ) := (le_max_right _ _).trans hcTn
    nlinarith
  have hTr : Trec / c k ≤ (Tn k : ℝ) := by
    rw [div_le_iff₀ (hc k)]
    linarith [(le_max_left Trec (2 * Tδ)).trans hcTn]
  have hsep := sepRhoPlus'_of_recentSupply_P6SF ((records (ind k) e).rescale_P6M (c k) (hc k)) b
    (antitoneOn_rescale_P6N_HCT hantiF (hc k)) hΛδ hη.le hηN (Tn k).2.1 hTr hlate
    (fun s hs hmem => hrecK_of_recent_HCT records (fun t ht n i' hm => hTrec t ht n i' hm)
      (ind k) (hc k) e s hs hmem)
  have hρe : (pF.rescale_P6N (c k) (hc k)).neckRadius (Tn k) =
      (q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) := by
    change pF.neckRadius (c k * (Tn k : ℝ)) / Real.sqrt (c k) =
      q.neckRadius (c k * (Tn k : ℝ)) / Real.sqrt (c k)
    rw [hpq _ (mul_nonneg (hc k).le (Tn k).2.1)]
  rw [hρe] at hsep
  have hR1 : (1 : ℝ) ≤ R k := by
    have := hRr k
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  exact conj1_arith_HTP hA0 hC (hR1.trans (hceil k)) (hceil k) hsep

namespace ObservedHistory

/-- **stage 曲率下界 ⇐ event slab pinching（`_HTP`，PROVED）**：`v < time j.succ` ⇒ 非 final 支。 -/
theorem curvatureLB_stage_of_eventPinched_HTP (K : RetainedCoreHistory.{u})
    {phi : ℝ → ℝ} {w : ℝ}
    (hev : ∀ i : Fin K.eventCount, Perelman.PhiAlmostNonnegative
      (K.toHistory.event i).incoming.flow
      (Ico (K.time i.castSucc) (K.time i.succ) ∩ Ici w) phi)
    (v : Icc (0 : ℝ) K.toHistory.horizon) (hvw : w ≤ (v : ℝ)) (j : Fin K.eventCount)
    (hvj : (v : ℝ) < K.time j.succ)
    (x : (K.toHistory.stage (K.toHistory.activeStage v)).Carrier) :
    curvatureOperatorLowerBoundAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) x
      (metricAlgebraicCurvatureTensorAt
        (K.toHistory.stageMetric (K.toHistory.activeStage v) v) x)
      (phi (metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) x)) := by
  have hmem := K.toHistory.activeStage_mem v
  revert x
  generalize K.toHistory.activeStage v = k at hmem ⊢
  intro x
  cases k using Fin.lastCases with
  | last =>
    have hmem' := (K.toHistory.mem_stageDomain_last v).1 hmem
    have hjl : K.toHistory.time j.succ ≤ K.toHistory.time (Fin.last K.eventCount) :=
      K.toHistory.time_strictMono.monotone (Fin.le_last _)
    exact absurd (lt_of_lt_of_le hvj (hjl.trans hmem'.1)) (lt_irrefl _)
  | cast j' =>
    rw [ObservedHistory.stageMetric_castSucc_apply]
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] at hmem
    exact hev j' v ⟨hmem, hvw⟩ x

end ObservedHistory

/-- consumer：conj1 孪生形的实例化。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {pF q : CutoffParameters}
    (records : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e pF)
    (hpq : ∀ t : ℝ, 0 ≤ t → pF.neckRadius t = q.neckRadius t)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (hδ : Tendsto pF.delta atTop (𝓝 0))
    (hrec : ∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
      ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
        (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
        ∀ h, (records n e).nominalRadius h ≤ η * pF.neckRadius t) : True := by
  have := conj1_of_recent_ceil_HTP (ε := 1) (C1 := 1) (C2 := 1) (Ctime := 1) F records hpq hanti
    hδ hrec
  trivial

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
