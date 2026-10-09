import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceGuardedFinalCoreP6HK
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HbcadCGuardedP6HK
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardWireFinalWireP6GWF

/-!
# 位置无关 `hbcadC` producer 去 `hclosC` / `hclosCF`（A1 续 HARNACK N4-f，后缀 `_P6HK`）

SLICEDICH G4b F6 / F7（`hUVCF_of_selection_Cg_local_P6SD` / `hbcadC_final_of_hclosC_sepRho_P6SD`）的孪生：
* `hUVCF_of_selection_Cg_guarded_P6HK`：final slab 中心 U 侧；梯度 / κ / D2 只在 c⋆ guard 点要，stay ⇐
  GUARDWIRE-FINAL `windowSeed_pointAnchor_final_P6GWF`（PROVED，无 binder）；κ ⇐ `hκRF` 在 `B(w) ∩
  {guard}` 上；
  **`hclosCF` 不再是前提**；D1（final 中心前 slab trace Dt）仍吃 `hstaySlCF`（见 GAP）。新增的前提
  `hCg`、`hRn1`、`rX/hsmall/hclock/aP/hpin/hRa` 均是 F7 已有的输入（CXJD 族），不是新 binder。
* `hbcadC_final_of_guarded_P6HK`：F7 逐字，去 `hclosC`、`hclosCF`；event 中心经 N4-c 的 L6 guard 版，
  final 中心经上式，序列层经 N4-e。
**GAP（`hstaySlCF`）**：final 中心 D1 的 w 中心三分需要 SLICE-BCBD2 `scalar_gt_of_slabs_prefix_P6SB2` 与
`stay_cstar_prefix_sepRho_P6SB2` 的 final 孪生（中心 slab `(K.event j).incoming` → restrict final slab；
`hbound_of_eventSlabs_P6SB2` 的末段改用 `hderF`；`hσlast` 换 final stageDomain 引理）。缺的是孪生，不是数学事实。
生成器 `build-logs/scratch/O-CH11-HARNACK/gen2/g3c.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

/-- **F6 guard 版（`_P6HK`）**：F6 逐字，去 `hclosCF`；U 侧梯度 / κ / D2 加 c⋆ guard，stay ⇐ final
  point-anchor。 -/
theorem ObservedHistory.hUVCF_of_selection_Cg_guarded_P6HK {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2')
    {κ Aκ : ℝ} {K : ℕ → RetainedCoreHistory.{u}}
    (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl)
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier) (R L r ρV : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v) ((K n).toHistory.activeStage_mono
              hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) z
          →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono
            (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hκRF : ∀ᶠ n in atTop, ∀ (c : ((K n).toHistory.stage (Fin.last (K
      n).toHistory.eventCount)).Carrier)
      (U : Set ((K n).toHistory.stage (Fin.last (K n).toHistory.eventCount)).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (K n).toHistory.time (Fin.last (K n).toHistory.eventCount) < τ → (τ : ℝ) < (K
          n).toHistory.horizon →
        ∀ z ∈ U, ∀ zz cc : ((K n).toHistory.stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (K n).toHistory.time (Fin.last (K n).toHistory.eventCount) < τ → (τ : ℝ) < (K
          n).toHistory.horizon →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((K n).toHistory.stageAt τ).Carrier, HEq cc c
          →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
              ((seedTrace n).point ((K n).toHistory.activeStage τ) ((K n).toHistory.activeStage_mono
                hav)
                ((K n).toHistory.activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (K n).toHistory.time (Fin.last (K n).toHistory.eventCount) < τ → (τ : ℝ) < (K
          n).toHistory.horizon →
        ∀ z ∈ U, ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
              ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
              (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ) zz
                b))
    (hstaySlCF : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (v : ℝ), (K n).toHistory.time (Fin.last (K n).toHistory.eventCount) < v →
        v < (K n).toHistory.horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : (Fin.last (K n).toHistory.eventCount) ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory (Fin.last (K n).toHistory.eventCount) ((K
          n).toHistory.activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ (Fin.last (K n).toHistory.eventCount))
        (h2 : (Fin.last (K n).toHistory.eventCount) ≤ (K n).toHistory.activeStage (Tn n)) (w : ((K
          n).toHistory.stage (Fin.last (K n).toHistory.eventCount)).Carrier),
        riemannianEDistOf ((K n).toHistory.stageMetric (Fin.last (K n).toHistory.eventCount) v)
            ((seedTrace n).point (Fin.last (K n).toHistory.eventCount) h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((K n).toHistory.stageMetric (Fin.last (K n).toHistory.eventCount) v)
            (tr.point (Fin.last (K n).toHistory.eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd /
              Real.sqrt (R n)) →
        R n ≤ metricScalarAt ((K n).toHistory.stageMetric (Fin.last (K n).toHistory.eventCount) v) w
          →
        ∀ (i : Fin (K n).toHistory.eventCount) (first : Fin ((K n).toHistory.eventCount + 1))
          (hf : first ≤ i.castSucc),
        ∀ z ∈ riemannianBallOf ((K n).toHistory.stageMetric (Fin.last (K n).toHistory.eventCount) v)
            w (Rad / Real.sqrt (metricScalarAt
              ((K n).toHistory.stageMetric (Fin.last (K n).toHistory.eventCount) v) w)),
        ∀ Btr : BackwardPointTrace (K n).toHistory first (Fin.last (K n).toHistory.eventCount)
          (hf.trans (Fin.castSucc_lt_last i).le) z,
        ∀ v' ∈ Ioo ((K n).toHistory.time i.castSucc) ((K n).toHistory.time i.succ),
        v - B / metricScalarAt ((K n).toHistory.stageMetric (Fin.last (K n).toHistory.eventCount) v)
          w ≤ v' →
        (v - v') * max (Cg * R n)
            (metricScalarAt ((K n).toHistory.stageMetric (Fin.last (K n).toHistory.eventCount) v)
              z) ≤ 1 / (2 * max (Ctime' : ℝ) 1) →
        Cg * R n < ((K n).toHistory.event i).incoming.flow.scalar v'
          (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) →
        ∀ (h1' : (K n).toHistory.activeStage (aSeed n) ≤ i.castSucc)
          (h2' : i.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
          riemannianEDistOf (((K n).toHistory.event i).incoming.flow.base.metric v')
              ((seedTrace n).point i.castSucc h1' h2')
              (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
                (σ n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hCg : 1 ≤ Cg) (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    {rX : ℝ} (hrX : 0 < rX)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) rX)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - rX ^ 2)
    (aP : ℕ → ℝ) (haP : ∀ n, 0 ≤ aP n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage s) s)
        (aP n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n) :
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
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
            ENNReal.ofReal ((L n / 4 + Dd) / Real.sqrt (R n)) →
        riemannianEDistOf ((G n).flow.base.metric v)
            (tr.point (Fin.last (K n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R
              n)) →
        R n ≤ (G n).flow.scalar v w →
          (∀ x ∈ riemannianBallOf ((G n).flow.base.metric v) w
                (Rad / Real.sqrt ((G n).flow.scalar v w)),
            Cg * R n < (G n).flow.scalar v x →
            ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric v)
              eps C1' C2' x, W.capTubeHasNeckChart eps) ∧
          (∀ x ∈ riemannianBallOf ((G n).flow.base.metric v) w
                (Rad / Real.sqrt ((G n).flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) v,
            v - B / (G n).flow.scalar v w ≤ v' →
            Cg * R n < (G n).flow.scalar v' x →
            (v - v') * max (Cg * R n) ((G n).flow.scalar v x) ≤
              1 / (2 * max (Ctime' : ℝ) 1) →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential (G n).flow v' x ξ| ≤
                (C2'.toNNReal : ℝ) * (G n).flow.scalar v' x *
                  Real.sqrt ((G n).flow.scalar v' x) *
                  Real.sqrt (((G n).flow.base.metric v').inner x ξ ξ)) ∧
          (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon),
            v - B / (G n).flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (K n).time (Fin.last (K n).eventCount) < τ → (τ : ℝ) < (K n).horizon →
            ∀ z ∈ riemannianBallOf ((G n).flow.base.metric v) w
                  (Rad / Real.sqrt ((G n).flow.scalar v w)),
            (v - τ) * max (Cg * R n) ((G n).flow.scalar v z) ≤
              1 / (2 * max (Ctime' : ℝ) 1) →
            ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
                  ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                  (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                    zz b)) ∧
          (∀ x ∈ riemannianBallOf ((G n).flow.base.metric v) w
                (Rad / Real.sqrt ((G n).flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) v,
            v - B / (G n).flow.scalar v w ≤ v' →
            Cg * R n < (G n).flow.scalar v' x →
            (v - v') * max (Cg * R n) ((G n).flow.scalar v x) ≤
              1 / (2 * max (Ctime' : ℝ) 1) →
            |derivWithin (fun s => (G n).flow.scalar s x) (Iic v') v'| ≤
              Ctime' * (G n).flow.scalar v' x ^ 2) ∧
          (∀ (i : Fin (K n).eventCount) (first : Fin ((K n).eventCount + 1))
              (hf : first ≤ i.castSucc),
            ∀ z ∈ riemannianBallOf ((G n).flow.base.metric v) w
                (Rad / Real.sqrt ((G n).flow.scalar v w)),
            ∀ Btr : BackwardPointTrace (K n).toHistory first (Fin.last (K n).eventCount)
              (hf.trans (Fin.castSucc_lt_last i).le) z,
            ∀ v' ∈ Ioo ((K n).time i.castSucc) ((K n).time i.succ),
            v - B / (G n).flow.scalar v w ≤ v' →
            (v - v') * max (Cg * R n) ((G n).flow.scalar v z) ≤
              1 / (2 * max (Ctime' : ℝ) 1) →
            Cg * R n < ((K n).toHistory.event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) →
            |derivWithin (fun s => ((K n).toHistory.event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le)) (Iic v') v'| ≤
              Ctime' * ((K n).toHistory.event i).incoming.flow.scalar v'
                (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) ^ 2) := by
  intro Rad B σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr
  obtain ⟨Cc, hCcdef⟩ : ∃ Cc : ℝ, Cc = max (max 1 (6 * Cg))
      (2 * Cg / localPropagationRadius C2' ^ 2) := ⟨_, rfl⟩
  obtain ⟨MC, hMCdef⟩ : ∃ MC : ℝ,
      MC = max 1 (2 * Real.sqrt 3 * (Cc / 2 + max Cc (2 * Real.exp 4))) := ⟨_, rfl⟩
  obtain ⟨ρg, hρgdef⟩ : ∃ ρg : ℝ, ρg = localPropagationRadius C2' / Real.sqrt (2 * Cg) :=
    ⟨_, rfl⟩
  have hρ : 0 < localPropagationRadius C2' := localPropagationRadius_pos hC2
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hRt : Tendsto R atTop atTop := tendsto_atTop_mono hRn1 hnat
  have hm1 : (1 : ℝ) ≤ max (Ctime' : ℝ) 1 := le_max_right _ _
  have hc1 : 1 / (2 * max (Ctime' : ℝ) 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hX1 : (1 : ℝ) ≤ max B 0 - σ₁ + 1 := by
    have := le_max_right B 0
    linarith
  filter_upwards [Filter.Eventually.filter_mono hφt (hRt.eventually_ge_atTop (2500 * MC / rX ^ 2)),
    Filter.Eventually.filter_mono hφt (hL.eventually_ge_atTop
      (4 * (Dd + max Rad 0 + ρg) + 4 * (2 + 16 * Real.sqrt MC) + 4)),
    Filter.Eventually.filter_mono hφt
      (hL.eventually_ge_atTop (max (2 * max Rad 0) (max B 0 - σ₁ + 1))),
    Filter.Eventually.filter_mono hφt (hwin (max B 0 - σ₁ + 1) (by linarith)),
    Filter.Eventually.filter_mono hφt hκRF, Filter.Eventually.filter_mono hφt hdistσ,
    hstaySlCF Rad B σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr]
    with n hRbig hLbig hLn hwn hκn hdσ hst
  intro v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw
  rw [hG n] at hwseed hwnear hRw ⊢
  have hRn := hR n
  have hLX : max B 0 - σ₁ + 1 ≤ L n := (le_max_right _ _).trans hLn
  have hL0 : 0 ≤ L n := by linarith
  have hRad : 2 * max Rad 0 ≤ L n := (le_max_left _ _).trans hLn
  have hvσ : v ≤ (σ n : ℝ) := by
    have : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ hRn
    linarith
  have hwinB : ∀ τ : ℝ, v - B / (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
    le_rfl).flow.scalar v w ≤ τ →
      (aSeed n : ℝ) ≤ τ ∧ (σ n : ℝ) - L n ^ 2 / R n ≤ τ := fun τ hτ => by
    obtain ⟨e1, e2⟩ := window_P6L3 hRn hRw hvσ1 hτ le_rfl hX1 hLX
    exact ⟨hwn.trans e1, e2⟩
  have hwin0 : (aSeed n : ℝ) ≤ v ∧ (σ n : ℝ) - L n ^ 2 / R n ≤ v := by
    have hX0 : max 0 0 - σ₁ + 1 ≤ max B 0 - σ₁ + 1 := by
      rw [max_self]
      linarith [le_max_right B 0]
    obtain ⟨e1, e2⟩ := window_P6L3 (B := 0) (τ := v) hRn hRw hvσ1 (by simp) hX0 hX1 hLX
    exact ⟨hwn.trans e1, e2⟩
  have hCg0 : 0 < Cg := lt_of_lt_of_le one_pos hCg
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hρg0 : 0 ≤ ρg := by rw [hρgdef]; positivity
  have hβ0 : 0 ≤ 1 / (2 * max (Ctime' : ℝ) 1) / Cg := by positivity
  have hβ1 : 1 / (2 * max (Ctime' : ℝ) 1) / Cg ≤ 1 := by
    rw [div_le_one hCg0]
    exact hc1.trans hCg
  have hMC1 : 1 ≤ MC := by rw [hMCdef]; exact le_max_left _ _
  have hRr : 2500 * MC ≤ R n * rX ^ 2 := (div_le_iff₀ (by positivity)).1 hRbig
  rw [hMCdef] at hRr
  have hLc : 2 + 16 * Real.sqrt MC * max (1 / (2 * max (Ctime' : ℝ) 1) / Cg) 0 ≤
      L n - 2 * ρg := by
    have e1 : max (1 / (2 * max (Ctime' : ℝ) 1) / Cg) 0 ≤ 1 := max_le hβ1 zero_le_one
    have e2 : 0 ≤ Real.sqrt MC := Real.sqrt_nonneg _
    have e3 : 16 * Real.sqrt MC * max (1 / (2 * max (Ctime' : ℝ) 1) / Cg) 0 ≤
        16 * Real.sqrt MC := mul_le_of_le_one_right (by positivity) e1
    have e4 : 0 ≤ Dd + max Rad 0 := add_nonneg hDd.le (le_max_right _ _)
    linarith only [e3, e4, hLbig, hρg0, e2]
  rw [hMCdef] at hLc
  have hρL : L n - 2 * ρg + 2 * (localPropagationRadius C2' / Real.sqrt (2 * Cg)) ≤ L n :=
    le_of_eq (by rw [hρgdef]; ring)
  have hC1c : 1 ≤ Cc := by rw [hCcdef]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hΛC : 6 * Cg ≤ Cc := by rw [hCcdef]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hρC : 2 * Cg ≤ localPropagationRadius C2' ^ 2 * Cc := by
    have e := le_max_right (max 1 (6 * Cg)) (2 * Cg / localPropagationRadius C2' ^ 2)
    rw [← hCcdef, div_le_iff₀ (by positivity)] at e
    linarith only [e, mul_comm Cc (localPropagationRadius C2' ^ 2)]
  have hbudP := pa_bud_P6HK (Ctime'.coe_nonneg) hCg0
  have hwseed2 : riemannianEDistOf ((((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
      le_rfl).flow.base.metric v)
      ((seedTrace n).point (Fin.last (K n).eventCount) h1 h2) w ≤
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) := by
    have e1 := le_max_right Rad 0
    have e2 := Real.sqrt_nonneg MC
    have e3 : L n / 4 + Dd ≤ L n / 2 := by linarith only [hLbig, hρg0, e1, hMC1, e2]
    exact budget_mono_P6HK e3 hwseed hsR.le
  have hrrx : Rad / Real.sqrt ((((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
      le_rfl).flow.scalar v w) ≤ max Rad 0 / Real.sqrt (R n) :=
    (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans
      (div_le_div_of_nonneg_left (le_max_right _ _) hsR (Real.sqrt_le_sqrt hRw))
  have hwlow : ∀ x : ((K n).stage (Fin.last (K n).eventCount)).Carrier, ∀ τ : ℝ,
      (v - τ) * max (Cg * R n) ((((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
          le_rfl).flow.scalar v x) ≤ 1 / (2 * max (Ctime' : ℝ) 1) →
      (aSeed n : ℝ) ≤ v - 1 / (2 * max (Ctime' : ℝ) 1) / Cg /
          (max (Cg * R n) ((((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
              le_rfl).flow.scalar v x) / Cg) ∧
        (σ n : ℝ) - L n ^ 2 / R n ≤ v - 1 / (2 * max (Ctime' : ℝ) 1) / Cg /
          (max (Cg * R n) ((((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
              le_rfl).flow.scalar v x) / Cg) ∧
        v - 1 / (2 * max (Ctime' : ℝ) 1) / Cg / (max (Cg * R n) ((((K n).finalSlab (hfin
            n)).restrictIncoming le_rfl (hfin n) le_rfl).flow.scalar v x) / Cg) ≤
          τ := by
    intro x τ hg
    have hMpos : 0 < max (Cg * R n) ((((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
        le_rfl).flow.scalar v x) :=
      lt_of_lt_of_le (mul_pos hCg0 hRn) (le_max_left _ _)
    have hlow := pa_lower_P6HK (σ := (σ n : ℝ)) hRn (pa_q_ge_P6HK
      (X := (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl).flow.scalar v x)
          hCg0 hRn) hβ0 hβ1 hvσ1 (le_max_right B 0)
    exact ⟨hwn.trans hlow, (pa_L_P6HK hRn hLX hX1).trans hlow, pa_window_P6HK hCg0 hMpos hg⟩
  have hcl' : ∀ x ∈ riemannianBallOf ((((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin
      n) le_rfl).flow.base.metric v) w
      (Rad / Real.sqrt ((((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
          le_rfl).flow.scalar v w)), ∀ τ : ℝ,
      (v - τ) * max (Cg * R n) ((((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
          le_rfl).flow.scalar v x) ≤ 1 / (2 * max (Ctime' : ℝ) 1) →
      τ ≤ v → (K n).time (Fin.last (K n).eventCount) < τ →
      riemannianEDistOf ((((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
          le_rfl).flow.base.metric τ)
          ((seedTrace n).point (Fin.last (K n).eventCount) h1 h2) x ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    intro x hx τ hg hτv hτ1
    obtain ⟨hav, hσL, hwτ⟩ := hwlow x τ hg
    have hlate : 1 ≤ R n * (v - 1 / (2 * max (Ctime' : ℝ) 1) / Cg /
        (max (Cg * R n) ((((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
            le_rfl).flow.scalar v x) / Cg)) :=
      (hRa n).trans (mul_le_mul_of_nonneg_left hav hRn.le)
    have hwx : riemannianEDistOf ((((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
        le_rfl).flow.base.metric v) w x ≤
        ENNReal.ofReal (max Rad 0 / Real.sqrt (R n)) :=
      (le_of_lt hx).trans (ENNReal.ofReal_le_ofReal hrrx)
    have e1 := le_max_right Rad 0
    have e2 := Real.sqrt_nonneg MC
    have e3 : L n / 4 + Dd + max Rad 0 ≤ (L n - 2 * ρg) / 2 := by
      linarith only [hLbig, hρg0, hDd, e1, hMC1, e2]
    have e5 : 0 ≤ L n / 4 + Dd := by linarith only [hL0, hDd]
    have e4 : 0 ≤ (L n / 4 + Dd) / Real.sqrt (R n) := div_nonneg e5 hsR.le
    have hxG := budget_add_P6HK hsR.le e4 (div_nonneg e1 hsR.le) e3 hwseed hwx
    exact RetainedCoreHistory.windowSeed_pointAnchor_final_P6GWF hC2 (K n) (hfin n) (haT n)
      (hsT n) (has n) (hsmall n) (hclock n) (seedTrace n) (haP n) (hpin n) (y n) hRn (hgood n) h1
      h2 hv2 (pa_q_ge_P6HK hCg0 hRn) hCg0 (pa_CgL_P6HK hCg0) hbudP hC1c hΛC hρC hRr hLc hρL hav
      hvσ hσL hlate x ((riemannianEDistOf_triangle _ _ _ _).trans hxG) (pa_xv_P6HK hCg0) τ hwτ
      hτv hτ1
  have hst' := hst v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w
    (by rw [(K n).stageMetric_last_restrict_P6HF (hfin n)]; exact hwseed2)
    (by rw [(K n).stageMetric_last_restrict_P6HF (hfin n)]; exact hwnear)
    (by rw [(K n).stageMetric_last_restrict_P6HF (hfin n)]; exact hRw)
  simp only [(K n).stageMetric_last_restrict_P6HF (hfin n)] at hst'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx hRx
    exact (K n).witness_of_hgood_final_P6HF (hfin n) (haT n) (hsT n) (has n) (seedTrace n) (y n)
      (R n) (L n) (hgood n) v hv1 hwin0.1 hvσ hwin0.2 h1 h2 x
      (seed_triangle_metric_P6HF _ _ w x _ hRn hRw hL0 hRad hwseed2 hx) hRx.le
  · intro x hx v' hv' hBv' hRx hg ξ
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    exact (K n).gradient_of_hgood_final_P6HF hC2 (hfin n) (haT n) (hsT n) (has n) (seedTrace n)
      (y n) (R n) (L n) (hgood n) v' hv'.1 ha (hv'.2.le.trans hvσ) hLτ h1 h2 x
      (hcl' x hx v' hg hv'.2.le hv'.1) hRx.le ξ
  · intro τ _ hτv hτ1 hτ2 z hz hg
    obtain ⟨-, hσL, hwτ⟩ := hwlow z τ hg
    exact (K n).regionalKappa_of_closure_final_P6HF (hfin n) (haT n) (hsT n) (has n) (seedTrace n)
      (y n) hRn hL0 hκn hdσ {x | x ∈ riemannianBallOf ((((K n).finalSlab (hfin
          n)).restrictIncoming le_rfl (hfin n) le_rfl).flow.base.metric v) w
          (Rad / Real.sqrt ((((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
              le_rfl).flow.scalar v w)) ∧
        (v - τ) * max (Cg * R n) ((((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
            le_rfl).flow.scalar v x) ≤ 1 / (2 * max (Ctime' : ℝ) 1)}
      τ v ((hroom n).trans (hσL.trans hwτ)) (hvσ.trans (hsT n)) h1 h2
      (fun τ' haτ hτv' hτ1' _ x hx => hcl' x hx.1 τ'
        (cstar_guard_mono_P6HK (le_trans (mul_pos hCg0 hRn).le (le_max_left _ _)) hx.2 haτ)
        hτv' hτ1') τ le_rfl hτv hτ1 hτ2 z ⟨hz, hg⟩
  · intro x hx v' hv' hBv' hRx hg
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    exact (K n).deriv_of_hgood_final_P6SD (hfin n) (haT n) (hsT n) (has n) (seedTrace n) (y n)
      (R n) (L n) (hgood n) v' hv'.1 (hv'.2.trans hv2) ha (hv'.2.le.trans hvσ) hLτ h1 h2 x
      (hcl' x hx v' hg hv'.2.le hv'.1) hRx.le
  · intro i first hf z hz Btr v' hv' hBv' hg hRx
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    have hv'v : v' < v := hv'.2.trans_le
      (((K n).toHistory.time_strictMono.monotone (Fin.le_last i.succ)).trans hv1.le)
    have h0 : (0 : ℝ) ≤ v' := ((K n).toHistory.time_nonneg _).trans hv'.1.le
    let vI : Icc (0 : ℝ) (K n).toHistory.horizon :=
      ⟨v', h0, (hv'v.le.trans hvσ).trans (σ n).2.2⟩
    have hact : (K n).toHistory.activeStage vI = i.castSucc :=
      (K n).toHistory.activeStage_eq_of_slab_P6L3 i vI hv'.1.le hv'.2
    have h1' : (K n).toHistory.activeStage (aSeed n) ≤ i.castSucc := by
      rw [← hact]
      exact (K n).toHistory.activeStage_mono (show aSeed n ≤ vI from ha)
    have h2' : i.castSucc ≤ (K n).toHistory.activeStage (Tn n) :=
      (Fin.castSucc_lt_last i).le.trans h2
    exact (K n).toHistory.deriv_of_hgood_slab_Cg_P6SD (haT n) (hsT n) (has n) (seedTrace n)
      (y n) (R n) (L n) (hgood n) i v' hv'.1 hv'.2 ha (hv'v.le.trans hvσ) hLτ h1' h2' _
      (hst' i first hf z hz Btr v' hv' hBv' hg hRx h1' h2') hRx.le

/-- **F7 guard 版（`_P6HK`）**：F7 逐字，去 `hclosC` / `hclosCF`；`hstaySlCF` 保留（GAP 见文件头）。 -/
theorem ObservedHistory.hbcadC_final_of_guarded_P6HK
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime' : ℝ≥0}
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
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime' (Q n) (Fin.last (K n).eventCount))
    (hpinchF : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi)
    (hderF : ∀ n, (G n).DerivativeBoundBefore Ctime' (Q n) (K n).horizon)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (hC2 : 0 ≤ C2) {Aκ : ℝ} (r : ℕ → ℝ)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl ε C1 C2 Ctime' v z)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
      (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))
    (hκRF : ∀ᶠ n in atTop, ∀ (c : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier)
      (U : Set ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))
    (hstaySlCF : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (v : ℝ), (Kh n).time (Fin.last (Kh n).eventCount) < v →
      v < (Kh n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) (Fin.last (Kh n).eventCount) ((Kh n).activeStage (σ n))
          hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ (Fin.last (Kh n).eventCount))
        (h2 : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage
          (Fin.last (Kh n).eventCount)).Carrier),
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt
              (R n)) →
        R n ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w →
        ∀ (i : Fin (Kh n).eventCount) (first : Fin ((Kh n).eventCount + 1))
          (hf : first ≤ i.castSucc),
        ∀ z ∈ riemannianBallOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            w (Rad / Real.sqrt (metricScalarAt
              ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w)),
        ∀ Btr : BackwardPointTrace (Kh n) first (Fin.last (Kh n).eventCount)
          (hf.trans (Fin.castSucc_lt_last i).le) z,
        ∀ v' ∈ Ioo ((Kh n).time i.castSucc) ((Kh n).time i.succ),
        v - B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
          w ≤ v' →
        (v - v') * max (Cg * R n)
            (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
              z) ≤ 1 / (2 * max (Ctime' : ℝ) 1) →
        Cg * R n < ((Kh n).event i).incoming.flow.scalar v'
          (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) →
        ∀ (h1' : (Kh n).activeStage (aSeed n) ≤ i.castSucc)
          (h2' : i.castSucc ≤ (Kh n).activeStage (Tn n)),
          riemannianEDistOf (((Kh n).event i).incoming.flow.base.metric v')
              ((seedTrace n).point i.castSucc h1' h2')
              (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n))
                (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n))
                  ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    {rX : ℝ} (hrX : 0 < rX)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) rX)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - rX ^ 2)
    (aP : ℕ → ℝ) (haP : ∀ n, 0 ≤ aP n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s) (aP n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hdfin : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤) :
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (K * R n)) →
      ∀ᶠ n in map φ atTop,
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
  subst hKh
  have hUVC := ObservedHistory.hUVC_of_selection_Cg_guarded_P6HK (Ctime' := Ctime') (Cg := Cg) hC2
    (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT seedTrace y R L r ρV hRpos hL hgood hwin
    hroom hdistσ hκR rfl hCg hRn1 hcanK hacc hrad hord hscaleK hslabK hT₀ hrX hsmall hclock
    aP haP hpin hRa T₀X hT₀X hOldX hdfin
  have hUVCF := ObservedHistory.hUVCF_of_selection_Cg_guarded_P6HK (Ctime' := Ctime') (Cg := Cg) hC2
    hfin hG Tn aSeed σ haT hsT has pT seedTrace y R L r ρV hRpos hL hgood hwin hroom hdistσ hκRF
    hstaySlCF hCg hRn1 hrX hsmall hclock aP haP hpin hRa
  exact ObservedHistory.hbcadC_lateHI_of_slice_data_final_cond_localG_P6HK hεle hκ hphi hCg hfin hG
    recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK hpinchF hderF σ y R hRpos
    hRn1 hT₀ Tn aSeed haT hsT has pT seedTrace L hL hwin ρV hρV hdistQC hUVC hUVCF

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
