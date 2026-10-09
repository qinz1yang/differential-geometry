import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HbcadCFinalBodyTruncKFP

/-!
# HFINDT G1：`P6HbcadCFinalBodyTruncKFP` 四个 `ObservedHistory` 定理的 final 条件形孪生（`_HFT`）

HFIN（`_HF`，DW 线）的改法机械移植到 DT 截断线：删 `hfin : ∀ n, time last < horizon`；
`G : ∀ n, time last < horizon → IncomingSlab …`，`hG` / `hpinchF` / `hderF : ∀ n h, …`（`hderF`
终点仍 `min horizon (tK n)`）；`hUVCF` 形陈述在 `v` 前加 `∀ hfn`；F4 final 支由 `ht1 ht2` 局部取
`hfL`。K 级引理 `RetainedCoreHistory.*_KFP` 的 `hfin` 是单 `K` 的局部假设，不动，原样复用。
末事件时刻 = horizon（退化末 slab）时 final 数据前提全部空真。PROVED，无 binder。
生成器 `build-logs/scratch/HFINDT/gen/gT1.py`
（源 sha256 `9c2b706f55ac064d37a3c25e35dfc0e65b607a38a10162c918d24db40fa8977f`）。
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

/-- **hUVCF 截断 final 条件形孪生（`_HFT`，PROVED）**：`…guarded2T_KFP` 逐字，`hfin` 删去，
final 数据条件形（`G n h` 等）；结论在 `v` 前加 `∀ hfn`（证明里 `hfin n ↦ hfL`）。 -/
theorem ObservedHistory.hUVCF_of_selection_Cg_guarded2T_HFT {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg
    : ℝ}
    (hC2 : 0 ≤ C2')
    {κ Aκ : ℝ} {K : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon →
      ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n h, G n h = ((K n).finalSlab h).restrictIncoming le_rfl h le_rfl)
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
    (hCg : 1 ≤ Cg) (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    {rX : ℝ} (hrX : 0 < rX)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) rX)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - rX ^ 2)
    (aP : ℕ → ℝ) (haP : ∀ n, 0 ≤ aP n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage s) s)
        (aP n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    {Q T₀ tK : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hslabK : ∀ n (j₀ : Fin (K n).eventCount),
      ((K n).toHistory.event j₀).incoming.DerivativeBoundBefore Ctime' (Q n)
        (min ((K n).time j₀.succ) (tK n)))
    (hderF : ∀ n h, (G n h).DerivativeBoundBefore Ctime' (Q n) (min (K n).horizon (tK n)))
    (hTnK : ∀ n, (Tn n : ℝ) ≤ tK n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (K n).eventCount), T₀X n ≤ (K n).toHistory.time e.succ →
      ((K n).toHistory.event e).old = ((K n).toHistory.event e).transition.trace.retainedCore)
    :
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (hfn : (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
      (v : ℝ), (K n).time (Fin.last (K n).eventCount) < v →
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
        riemannianEDistOf ((G n hfn).flow.base.metric v)
            ((seedTrace n).point (Fin.last (K n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal ((L n / 4 + Dd) / Real.sqrt (R n)) →
        riemannianEDistOf ((G n hfn).flow.base.metric v)
            (tr.point (Fin.last (K n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R
              n)) →
        R n ≤ (G n hfn).flow.scalar v w →
          (∀ x ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            Cg * R n < (G n hfn).flow.scalar v x →
            ∃ W : SpatialCanonicalWitness ((G n hfn).flow.base.metric v)
              eps C1' C2' x, W.capTubeHasNeckChart eps) ∧
          (∀ x ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) v,
            v - B / (G n hfn).flow.scalar v w ≤ v' →
            Cg * R n < (G n hfn).flow.scalar v' x →
            (v - v') * max (Cg * R n) ((G n hfn).flow.scalar v x) ≤
              1 / (2 * max (Ctime' : ℝ) 1) →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential (G n hfn).flow v' x ξ| ≤
                (C2'.toNNReal : ℝ) * (G n hfn).flow.scalar v' x *
                  Real.sqrt ((G n hfn).flow.scalar v' x) *
                  Real.sqrt (((G n hfn).flow.base.metric v').inner x ξ ξ)) ∧
          (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon),
            v - B / (G n hfn).flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (K n).time (Fin.last (K n).eventCount) < τ → (τ : ℝ) < (K n).horizon →
            ∀ z ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                  (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            (v - τ) * max (Cg * R n) ((G n hfn).flow.scalar v z) ≤
              1 / (2 * max (Ctime' : ℝ) 1) →
            ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
                  ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                  (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                    zz b)) ∧
          (∀ x ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) v,
            v - B / (G n hfn).flow.scalar v w ≤ v' →
            Cg * R n < (G n hfn).flow.scalar v' x →
            (v - v') * max (Cg * R n) ((G n hfn).flow.scalar v x) ≤
              1 / (2 * max (Ctime' : ℝ) 1) →
            |derivWithin (fun s => (G n hfn).flow.scalar s x) (Iic v') v'| ≤
              Ctime' * (G n hfn).flow.scalar v' x ^ 2) ∧
          (∀ (i : Fin (K n).eventCount) (first : Fin ((K n).eventCount + 1))
              (hf : first ≤ i.castSucc),
            ∀ z ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            ∀ Btr : BackwardPointTrace (K n).toHistory first (Fin.last (K n).eventCount)
              (hf.trans (Fin.castSucc_lt_last i).le) z,
            ∀ v' ∈ Ioo ((K n).time i.castSucc) ((K n).time i.succ),
            v - B / (G n hfn).flow.scalar v w ≤ v' →
            (v - v') * max (Cg * R n) ((G n hfn).flow.scalar v z) ≤
              1 / (2 * max (Ctime' : ℝ) 1) →
            Cg * R n < ((K n).toHistory.event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) →
            |derivWithin (fun s => ((K n).toHistory.event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le)) (Iic v') v'| ≤
              Ctime' * ((K n).toHistory.event i).incoming.flow.scalar v'
                (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) ^ 2) := by
  obtain ⟨ε₀, hε₀, hnc0⟩ := exists_hnc_of_records_P6SB2.{u}
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
    Filter.Eventually.filter_mono hφt (hT₀ (max B 0 - σ₁ + 1)),
    Filter.Eventually.filter_mono hφt (hnat.eventually_ge_atTop 9),
    Filter.Eventually.filter_mono hφt (hnat.eventually_ge_atTop (6 / rX ^ 2 + 1)),
    Filter.Eventually.filter_mono hφt (hnat.eventually_gt_atTop (StandardCap.transitionEnd + 10)),
    Filter.Eventually.filter_mono hφt (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (ge_mem_nhds (lt_min hε₀ (by norm_num : (0 : ℝ) < 1 / 2)))),
    Filter.Eventually.filter_mono hφt (hL.eventually_ge_atTop (max (max
      (8 * localPropagationRadius C2')
      (4 * (max Rad 0 + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) /
        min (min (rX / 50) (localPropagationRadius C2' / 2))
          (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4))))) + 4)) 2))]
    with n hRbig hLbig hLn hwn hκn hdσ hT₀n h9 hr6 hTEn hacn hLX2
  intro hfL v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw
  rw [hG n hfL] at hwseed hwnear hRw ⊢
  have hRn := hR n
  have hLX : max B 0 - σ₁ + 1 ≤ L n := (le_max_right _ _).trans hLn
  have hL0 : 0 ≤ L n := by linarith
  have hRad : 2 * max Rad 0 ≤ L n := (le_max_left _ _).trans hLn
  have hvσ : v ≤ (σ n : ℝ) := by
    have : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ hRn
    linarith
  have hvtK : v < tK n := by
    have : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ hRn
    have h2 : (σ n : ℝ) ≤ Tn n := hsT n
    linarith [hTnK n]
  have hwinB : ∀ τ : ℝ, v - B / (((K n).finalSlab hfL).restrictIncoming le_rfl hfL
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
  have hwseed2 : riemannianEDistOf ((((K n).finalSlab hfL).restrictIncoming le_rfl hfL
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
  have hrrx : Rad / Real.sqrt ((((K n).finalSlab hfL).restrictIncoming le_rfl hfL
      le_rfl).flow.scalar v w) ≤ max Rad 0 / Real.sqrt (R n) :=
    (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans
      (div_le_div_of_nonneg_left (le_max_right _ _) hsR (Real.sqrt_le_sqrt hRw))
  have hwlow : ∀ x : ((K n).stage (Fin.last (K n).eventCount)).Carrier, ∀ τ : ℝ,
      (v - τ) * max (Cg * R n) ((((K n).finalSlab hfL).restrictIncoming le_rfl hfL
          le_rfl).flow.scalar v x) ≤ 1 / (2 * max (Ctime' : ℝ) 1) →
      (aSeed n : ℝ) ≤ v - 1 / (2 * max (Ctime' : ℝ) 1) / Cg /
          (max (Cg * R n) ((((K n).finalSlab hfL).restrictIncoming le_rfl hfL
              le_rfl).flow.scalar v x) / Cg) ∧
        (σ n : ℝ) - L n ^ 2 / R n ≤ v - 1 / (2 * max (Ctime' : ℝ) 1) / Cg /
          (max (Cg * R n) ((((K n).finalSlab hfL).restrictIncoming le_rfl hfL
              le_rfl).flow.scalar v x) / Cg) ∧
        v - 1 / (2 * max (Ctime' : ℝ) 1) / Cg / (max (Cg * R n) ((((K n).finalSlab
            hfL).restrictIncoming le_rfl hfL le_rfl).flow.scalar v x) / Cg) ≤
          τ := by
    intro x τ hg
    have hMpos : 0 < max (Cg * R n) ((((K n).finalSlab hfL).restrictIncoming le_rfl hfL
        le_rfl).flow.scalar v x) :=
      lt_of_lt_of_le (mul_pos hCg0 hRn) (le_max_left _ _)
    have hlow := pa_lower_P6HK (σ := (σ n : ℝ)) hRn (pa_q_ge_P6HK
      (X := (((K n).finalSlab hfL).restrictIncoming le_rfl hfL le_rfl).flow.scalar v x)
          hCg0 hRn) hβ0 hβ1 hvσ1 (le_max_right B 0)
    exact ⟨hwn.trans hlow, (pa_L_P6HK hRn hLX hX1).trans hlow, pa_window_P6HK hCg0 hMpos hg⟩
  have hcl' : ∀ x ∈ riemannianBallOf ((((K n).finalSlab hfL).restrictIncoming le_rfl hfL
      le_rfl).flow.base.metric v) w
      (Rad / Real.sqrt ((((K n).finalSlab hfL).restrictIncoming le_rfl hfL
          le_rfl).flow.scalar v w)), ∀ τ : ℝ,
      (v - τ) * max (Cg * R n) ((((K n).finalSlab hfL).restrictIncoming le_rfl hfL
          le_rfl).flow.scalar v x) ≤ 1 / (2 * max (Ctime' : ℝ) 1) →
      τ ≤ v → (K n).time (Fin.last (K n).eventCount) < τ →
      riemannianEDistOf ((((K n).finalSlab hfL).restrictIncoming le_rfl hfL
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
        (max (Cg * R n) ((((K n).finalSlab hfL).restrictIncoming le_rfl hfL
            le_rfl).flow.scalar v x) / Cg)) :=
      (hRa n).trans (mul_le_mul_of_nonneg_left hav hRn.le)
    have hwx : riemannianEDistOf ((((K n).finalSlab hfL).restrictIncoming le_rfl hfL
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
    exact RetainedCoreHistory.windowSeed_pointAnchor_final_P6GWF hC2 (K n) hfL (haT n)
      (hsT n) (has n) (hsmall n) (hclock n) (seedTrace n) (haP n) (hpin n) (y n) hRn (hgood n) h1
      h2 hv2 (pa_q_ge_P6HK hCg0 hRn) hCg0 (pa_CgL_P6HK hCg0) hbudP hC1c hΛC hρC hRr hLc hρL hav
      hvσ hσL hlate x ((riemannianEDistOf_triangle _ _ _ _).trans hxG) (pa_xv_P6HK hCg0) τ hwτ
      hτv hτ1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx hRx
    exact (K n).witness_of_hgood_final_P6HF hfL (haT n) (hsT n) (has n) (seedTrace n) (y n)
      (R n) (L n) (hgood n) v hv1 hwin0.1 hvσ hwin0.2 h1 h2 x
      (seed_triangle_metric_P6HF _ _ w x _ hRn hRw hL0 hRad hwseed2 hx) hRx.le
  · intro x hx v' hv' hBv' hRx hg ξ
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    exact (K n).gradient_of_hgood_final_P6HF hC2 hfL (haT n) (hsT n) (has n) (seedTrace n)
      (y n) (R n) (L n) (hgood n) v' hv'.1 ha (hv'.2.le.trans hvσ) hLτ h1 h2 x
      (hcl' x hx v' hg hv'.2.le hv'.1) hRx.le ξ
  · intro τ _ hτv hτ1 hτ2 z hz hg
    obtain ⟨-, hσL, hwτ⟩ := hwlow z τ hg
    exact (K n).regionalKappa_of_closure_final_P6HF hfL (haT n) (hsT n) (has n) (seedTrace n)
      (y n) hRn hL0 hκn hdσ {x | x ∈ riemannianBallOf ((((K n).finalSlab hfL).restrictIncoming
          le_rfl hfL le_rfl).flow.base.metric v) w
          (Rad / Real.sqrt ((((K n).finalSlab hfL).restrictIncoming le_rfl hfL
              le_rfl).flow.scalar v w)) ∧
        (v - τ) * max (Cg * R n) ((((K n).finalSlab hfL).restrictIncoming le_rfl hfL
            le_rfl).flow.scalar v x) ≤ 1 / (2 * max (Ctime' : ℝ) 1)}
      τ v ((hroom n).trans (hσL.trans hwτ)) (hvσ.trans (hsT n)) h1 h2
      (fun τ' haτ hτv' hτ1' _ x hx => hcl' x hx.1 τ'
        (cstar_guard_mono_P6HK (le_trans (mul_pos hCg0 hRn).le (le_max_left _ _)) hx.2 haτ)
        hτv' hτ1') τ le_rfl hτv hτ1 hτ2 z ⟨hz, hg⟩
  · intro x hx v' hv' hBv' hRx hg
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    exact (K n).deriv_of_hgood_final_P6SD hfL (haT n) (hsT n) (has n) (seedTrace n) (y n)
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
    obtain ⟨e1, -⟩ := window_P6L3 hRn hRw hvσ1 hBv' le_rfl hX1 hLX
    have hR1 : (1 : ℝ) ≤ R n := by
      have e2 := hRn1 n
      have e3 : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith only [e2, e3]
    have hacc1 : (p n).modelAccuracy ≤ min ε₀ (1 / 2) := (hacc n).trans hacn
    have hDm' : StandardCap.transitionEnd + 10 < (p n).modelRadius := by
      linarith only [hrad n, hTEn]
    have hncK := hnc0 (H := (K n).toHistory) (q := p n) (T₀ := T₀ n) (recordsK n)
      (hacc1.trans (min_le_left _ _)) (le_trans (by omega) (hord n)) (hcanK n)
    have hderFn := hderF n hfL
    rw [hG n hfL] at hderFn
    have hL2 : (2 : ℝ) ≤ L n := (le_max_right _ _).trans hLX2
    have hLρ : 8 * localPropagationRadius C2' ≤ L n :=
      ((le_max_left _ _).trans (le_max_left _ _)).trans hLX2
    have hLc : 4 * (max Rad 0 + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) /
        min (min (rX / 50) (localPropagationRadius C2' / 2))
          (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4))))) + 4 ≤ L n :=
      ((le_max_right _ _).trans (le_max_left _ _)).trans hLX2
    have hwinJ : ∀ s : ℝ, v - (L n / 2) ^ 2 / R n ≤ s → (σ n : ℝ) - L n ^ 2 / R n ≤ s := by
      intro s hs
      have hLa : -σ₁ + 1 ≤ L n := by linarith only [hLX, le_max_right B 0]
      have hσ0 : σ₁ < 0 := lt_of_le_of_lt h12 hσ₂
      have hsq := mul_le_mul hLa hLa (by linarith only [hσ0]) hL0
      have hA' : 0 ≤ σ₁ + 3 / 4 * L n ^ 2 := by
        nlinarith only [hsq, sq_nonneg (σ₁ - 1 / 3)]
      have hdiv : 0 ≤ (σ₁ + 3 / 4 * L n ^ 2) / R n := div_nonneg hA' hRn.le
      have heq : (σ₁ + 3 / 4 * L n ^ 2) / R n =
          σ₁ / R n + L n ^ 2 / R n - (L n / 2) ^ 2 / R n := by
        rw [add_div, mul_div_assoc, div_pow]
        ring
      linarith only [hvσ1, hdiv, heq, hs]
    exact RetainedCoreHistory.slabDeriv_final_D1T_KFP hC2 hCg (K n) hfL (haT n) (hsT n)
      (has n) (seedTrace n) (y n) hR1 (hgood n) (recordsK n) (hcanK n) hncK
      (hacc1.trans (min_le_right _ _)) hDm' h9 (hscaleK n) (hslabK n) hderFn hrX hr6 (hsmall n)
      (hclock n) (haP n) (hpin n) (hOldX n)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans hdσ)) hLρ hLc hL2 hv1 hv2 hvσ
      hvtK hwinJ h1 h2 w z
      hwseed2 (riemannianBallOf_mono _ _ hrrx hz) i first hf Btr v' hv' ha hLτ (hT₀n.trans e1)
      ((hT₀X n).trans ha) ((hRa n).trans (mul_le_mul_of_nonneg_left ha hRn.le)) hg hRx

/-- **F4 核心截断 final 条件形孪生（`_HFT`，PROVED）**：`…localGT_KFP` 逐字，`hfin` 删去，
`G` / `hG` / `hpinchF` / `hderF` 条件形；final 支内由 `ht1 ht2` 局部取 `hfL`。 -/
theorem ObservedHistory.hsliceR_lateHI_core_final_localGT_HFT
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc)
    {K : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon →
      ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n h, G n h = ((K n).finalSlab h).restrictIncoming le_rfl h le_rfl)
    {Q T₀ tK : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
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
    (hslabK : ∀ n (j₀ : Fin (K n).eventCount),
      ((K n).toHistory.event j₀).incoming.DerivativeBoundBefore Ctime (Q n)
        (min ((K n).time j₀.succ) (tK n)))
    (hpinchF : ∀ n h, Perelman.PhiAlmostNonnegative (G n h).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi)
    (hderF : ∀ n h, (G n h).DerivativeBoundBefore Ctime (Q n) (min (K n).horizon (tK n)))
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt (σ
      n)).Carrier)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n)
    (hTnK : ∀ n, (Tn n : ℝ) ≤ tK n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
 :
    ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ Rad Bw : ℝ, 0 ≤ QB ∧
      Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
      ∀ l : Filter ℕ, l ≤ atTop → ∀ σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw : ℝ, 0 < Dw →
      (∀ᶠ n in l,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
        (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) + σ₁ / R n ≤ v →
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
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
      (∀ᶠ n in l,
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
            ENNReal.ofReal ((L n / 4 + Dd) / Real.sqrt (R n)) →
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
            v - Bw / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((K n).toHistory.event j').incoming.flow.scalar v' x →
            (v - v') * max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential ((K n).toHistory.event j').incoming.flow v' x ξ| ≤
                Cgrad * ((K n).toHistory.event j').incoming.flow.scalar v' x *
                  Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v' x) *
                  Real.sqrt ((((K n).toHistory.event j').incoming.flow.base.metric v').inner x ξ ξ))
                    ∧
          (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon),
            v - Bw / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (K n).toHistory.time j'.castSucc < τ → (τ : ℝ) < (K n).toHistory.time j'.succ →
            ∀ z ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                  (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            (v - τ) * max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
                  ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                  (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                    zz b)) ∧
          (∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).toHistory.time j'.castSucc) v,
            v - Bw / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((K n).toHistory.event j').incoming.flow.scalar v' x →
            (v - v') * max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            |derivWithin (fun s => ((K n).toHistory.event j').incoming.flow.scalar s x)
                (Iic v') v'| ≤
              Ctime * ((K n).toHistory.event j').incoming.flow.scalar v' x ^ 2) ∧
          (∀ (i : Fin (K n).toHistory.eventCount) (first : Fin ((K n).toHistory.eventCount + 1))
              (hf : first ≤ i.castSucc) (hij : i.castSucc < j'.castSucc),
            ∀ z ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            ∀ Btr : BackwardPointTrace (K n).toHistory first j'.castSucc (hf.trans hij.le) z,
            ∀ v' ∈ Ioo ((K n).toHistory.time i.castSucc) ((K n).toHistory.time i.succ),
            v - Bw / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ v' →
            (v - v') * max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            Cg * R n < ((K n).toHistory.event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf hij.le) →
            |derivWithin (fun s => ((K n).toHistory.event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf hij.le)) (Iic v') v'| ≤
              Ctime * ((K n).toHistory.event i).incoming.flow.scalar v'
                (Btr.point i.castSucc hf hij.le) ^ 2)) →
      (∀ᶠ n in l,
      ∀ (hfn : (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
      (v : ℝ), (K n).time (Fin.last (K n).eventCount) < v →
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
        riemannianEDistOf ((G n hfn).flow.base.metric v)
            ((seedTrace n).point (Fin.last (K n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal ((L n / 4 + Dd) / Real.sqrt (R n)) →
        riemannianEDistOf ((G n hfn).flow.base.metric v)
            (tr.point (Fin.last (K n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R
              n)) →
        R n ≤ (G n hfn).flow.scalar v w →
          (∀ x ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            Cg * R n < (G n hfn).flow.scalar v x →
            ∃ W : SpatialCanonicalWitness ((G n hfn).flow.base.metric v)
              ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
          (∀ x ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) v,
            v - Bw / (G n hfn).flow.scalar v w ≤ v' →
            Cg * R n < (G n hfn).flow.scalar v' x →
            (v - v') * max (Cg * R n) ((G n hfn).flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential (G n hfn).flow v' x ξ| ≤
                Cgrad * (G n hfn).flow.scalar v' x *
                  Real.sqrt ((G n hfn).flow.scalar v' x) *
                  Real.sqrt (((G n hfn).flow.base.metric v').inner x ξ ξ)) ∧
          (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon),
            v - Bw / (G n hfn).flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (K n).time (Fin.last (K n).eventCount) < τ → (τ : ℝ) < (K n).horizon →
            ∀ z ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                  (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            (v - τ) * max (Cg * R n) ((G n hfn).flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
                  ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                  (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                    zz b)) ∧
          (∀ x ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) v,
            v - Bw / (G n hfn).flow.scalar v w ≤ v' →
            Cg * R n < (G n hfn).flow.scalar v' x →
            (v - v') * max (Cg * R n) ((G n hfn).flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            |derivWithin (fun s => (G n hfn).flow.scalar s x) (Iic v') v'| ≤
              Ctime * (G n hfn).flow.scalar v' x ^ 2) ∧
          (∀ (i : Fin (K n).eventCount) (first : Fin ((K n).eventCount + 1))
              (hf : first ≤ i.castSucc),
            ∀ z ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            ∀ Btr : BackwardPointTrace (K n).toHistory first (Fin.last (K n).eventCount)
              (hf.trans (Fin.castSucc_lt_last i).le) z,
            ∀ v' ∈ Ioo ((K n).time i.castSucc) ((K n).time i.succ),
            v - Bw / (G n hfn).flow.scalar v w ≤ v' →
            (v - v') * max (Cg * R n) ((G n hfn).flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            Cg * R n < ((K n).toHistory.event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) →
            |derivWithin (fun s => ((K n).toHistory.event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le)) (Iic v') v'| ≤
              Ctime * ((K n).toHistory.event i).incoming.flow.scalar v'
                (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) ^ 2)) →
      ∀ᶠ n in l,
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) + σ₁ / R n ≤ v →
        (v : ℝ) ≤ σ n + σ₂ / R n → (K n).toHistory.time ((K n).toHistory.activeStage v) < v →
      ∀ tr₁ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v) ((K
        n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x₁,
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono hvt))
            ≤ A * R n →
        ∃ CWP : ((K n).toHistory.stage ((K n).toHistory.activeStage v)).Carrier → Prop,
          (∀ w, riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
                hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → ¬ CWP w →
            R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) w →
              ∀ x,
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) w x <
              ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
                Real.sqrt (metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage
                  v) v) w)) →
            metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) x ≤
              QB * metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) w)
                ∧
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
                    (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃) := by
  intro A Dd hA hDd
  obtain ⟨Cbirth, hCbirth, hP⟩ :=
    RetainedCoreHistory.slice_dichotomy_late_Cg_window_local_bothG_P6HK hεle
    κ C1
    C2 hκ Ctime Cgrad Cg (by linarith) hphi hη₃ hLc
  obtain ⟨QB, Dcap, D₂, hQB, hD₂, Λ, Rad, Bw, Rmin, ζmin, δ₀, m₀, hΛ, -, hζ, hδ₀, hmain, hmainF⟩ :=
    hP A Dd hA hDd
  refine ⟨QB, Dcap, D₂, Rad, Bw, hQB, hD₂, fun l hl σ₁ σ₂ h12 hσ₂ Dw hDw hdl hUl hUFl => ?_⟩
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hR : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRn1 hnat
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδ : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ δ₀ := h0.eventually (ge_mem_nhds hδ₀)
  have hacc' : ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ζmin :=
    (h0.eventually (ge_mem_nhds hζ)).mono fun n hn => (hacc n).trans hn
  have hrad' : ∀ᶠ n in atTop, Rmin ≤ (p n).modelRadius :=
    (hnat.eventually_ge_atTop Rmin).mono fun n hn => hn.trans (hrad n)
  have hord' : ∀ᶠ n in atTop, m₀ ≤ (p n).modelOrder :=
    (eventually_ge_atTop m₀).mono fun n hn => le_trans (by omega) (hord n)
  have hbirth : ∀ᶠ n : ℕ in atTop, ∀ i hi b,
      max ((n : ℝ) + 1) (Q n) ≤ Cbirth * ((recordsK n i hi).static b).neck.scale ∧
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale := by
    filter_upwards [hnat.eventually_ge_atTop (1 / Cbirth), hbirthA] with n hn1 hbA i hi b
    have hs := hscaleK n i hi b
    have hC1 : 1 ≤ ((n : ℝ) + 1) * Cbirth := (div_le_iff₀ hCbirth).1 hn1
    have hq : (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) (Q n) := le_max_left _ _
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    refine ⟨?_, hbA i hi b⟩
    calc max ((n : ℝ) + 1) (Q n) = max ((n : ℝ) + 1) (Q n) * 1 := by ring
      _ ≤ max ((n : ℝ) + 1) (Q n) * (((n : ℝ) + 1) * Cbirth) :=
        mul_le_mul_of_nonneg_left hC1 (by linarith)
      _ = ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) * Cbirth := by ring
      _ ≤ ((recordsK n i hi).static b).neck.scale * Cbirth :=
        mul_le_mul_of_nonneg_right hs hCbirth.le
      _ = Cbirth * ((recordsK n i hi).static b).neck.scale := by ring
  have hT1 : 0 < -σ₁ := by linarith
  have hRσ : ∀ᶠ n in atTop, Λ - σ₁ ≤ R n * σ n := by
    filter_upwards [hwin (max (Λ - σ₁) 1) (lt_max_of_lt_right one_pos)] with n hn
    have ha0 : (0 : ℝ) ≤ aSeed n := (aSeed n).2.1
    have hRn := hRpos n
    have h1 : max (Λ - σ₁) 1 / R n ≤ σ n := by linarith
    rw [div_le_iff₀ hRn] at h1
    nlinarith [le_max_left (Λ - σ₁) 1]
  filter_upwards [Filter.Eventually.filter_mono hl hδ, Filter.Eventually.filter_mono hl hrad',
    Filter.Eventually.filter_mono hl hord', Filter.Eventually.filter_mono hl hacc',
    Filter.Eventually.filter_mono hl hbirth,
    Filter.Eventually.filter_mono hl (hR.eventually_ge_atTop Λ),
    Filter.Eventually.filter_mono hl hRσ,
    Filter.Eventually.filter_mono hl (hρV.eventually_ge_atTop Λ),
    Filter.Eventually.filter_mono hl (hL.eventually_ge_atTop (4 * Dd)),
    Filter.Eventually.filter_mono hl (hwin (-σ₁) hT1),
    Filter.Eventually.filter_mono hl (hT₀ (Bw - σ₁)), hdl, hUl,
    hUFl]
    with n e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
  intro x₁ hx₁ v hvt hv1 hv2 hage tr₁ _
  have hvwin : (σ n : ℝ) - -σ₁ / R n ≤ v := by
    rw [neg_div, sub_neg_eq_add]
    exact hv1
  have hav : aSeed n ≤ v := show (aSeed n : ℝ) ≤ v from e10.trans hvwin
  have hT₀v : T₀ n ≤ v - Bw / R n := by
    have : (Bw - σ₁) / R n = Bw / R n - σ₁ / R n := sub_div _ _ _
    rw [this] at e11
    linarith
  have hvtK : (v : ℝ) ≤ tK n :=
    (show (v : ℝ) ≤ Tn n from hvt.trans (hsT n)).trans (hTnK n)
  by_cases hlastF : (K n).toHistory.activeStage v = Fin.last (K n).eventCount
  · -- final slab 内部切片：final 单切片二分
    have ht1 : (K n).time (Fin.last (K n).eventCount) < v := by
      have h := hage
      rw [hlastF] at h
      exact h
    have ht2 : (v : ℝ) < (K n).horizon := by
      have h1 : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ (hRpos n)
      have h2 : (σ n : ℝ) ≤ (K n).horizon := (σ n).2.2
      linarith
    have hfL : (K n).time (Fin.last (K n).eventCount) < (K n).horizon := ht1.trans ht2
    have h1 : (K n).toHistory.activeStage (aSeed n) ≤ Fin.last (K n).eventCount := Fin.le_last _
    have h2 : Fin.last (K n).eventCount ≤ (K n).toHistory.activeStage (Tn n) :=
      hlastF.symm.le.trans ((K n).toHistory.activeStage_mono (hvt.trans (hsT n)))
    have hs := point_heq_of_eq_P6M2 (seedTrace n) hlastF ((K n).toHistory.activeStage_mono hav)
      ((K n).toHistory.activeStage_mono (hvt.trans (hsT n))) h1 h2
    have hfn : (K n).toHistory.activeStage v ≤ Fin.last (K n).eventCount := le_of_eq hlastF
    have hjσ : Fin.last (K n).eventCount ≤ (K n).toHistory.activeStage (σ n) :=
      hlastF.symm.le.trans ((K n).toHistory.activeStage_mono hvt)
    have hzj := point_heq_of_eq_P6M2 tr₁ hlastF le_rfl ((K n).toHistory.activeStage_mono hvt)
      (hfn.trans le_rfl) hjσ
    have hΛv : Λ ≤ R n * v := by
      have hRv : R n * ((σ n : ℝ) + σ₁ / R n) ≤ R n * v :=
        mul_le_mul_of_nonneg_left hv1 (hRpos n).le
      have hRne := (hRpos n).ne'
      have heq : R n * ((σ n : ℝ) + σ₁ / R n) = R n * σ n + σ₁ := by
        field_simp
      linarith
    have hL0 : 0 ≤ L n / 4 / Real.sqrt (R n) := by
      have : 0 < Dd := hDd
      have : 0 ≤ L n := by linarith
      positivity
    refine hmainF (K n) (T₀ n) (recordsK n) (hcanK n) e2 e3 e4 (hpinchK0 n) (recordsF n)
      (1 / ((n : ℝ) + 1)) (hδF n) e1 (max ((n : ℝ) + 1) (Q n)) (a₀ n)
      (lt_of_lt_of_le (by positivity) (le_max_left _ _)) (fun x => (hHI n x).1)
      (fun x => (hHI n x).2) e5 hfL (G n hfL) (hG n hfL) (hpinchF n hfL)
      (fun i _ y' t' ht hR' => hslabK n i y' t' ⟨ht.1, lt_min ht.2 (ht.2.trans_le
        (((K n).time_strictMono.monotone (Fin.le_last i.succ)).trans (ht1.le.trans hvtK)))⟩
        ((le_max_right _ _).trans_lt hR')) v ht1 ht2
      (fun y' t' ht hR' => hderF n hfL y' t' ⟨ht.1, lt_min (ht.2.trans ht2) (ht.2.trans_le hvtK)⟩
        ((le_max_right _ _).trans_lt hR'))
      (R n) (ρV n) (hRpos n) e6 hΛv e8
      hT₀v _ hlastF
      (tr₁.point _ le_rfl _) _ _ hs _ (e12 x₁ hx₁ v hav hvt hv1 tr₁)
      ((tr₁.restrictFirst hfn hjσ).point (Fin.last (K n).eventCount) le_rfl hjσ) hzj ?_
    intro w hw hzw hRw
    refine (fun H => ?hU) (e14 hfL v ht1 ht2 hv1 hv2 x₁ hx₁ hjσ (tr₁.restrictFirst hfn hjσ) h1 h2 w
      (hw.trans ?hd) hzw hRw)
    case hU =>
      obtain ⟨u1, u2, u3, u4, u5⟩ := H
      exact ⟨u1, u2, u3, u4, fun i first hf z hz Btr v' hv' hBv' hg hR =>
        u5 (Fin.castLE (Nat.le_of_lt_succ (Fin.last (K n).eventCount).isLt) i)
          (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ (Fin.last (K n).eventCount).isLt))
            first)
          (Fin.le_def.mpr (Fin.le_def.mp hf)) z hz
          ((K n).backwardPointTraceOfPrefix (Fin.last (K n).eventCount) Btr) v' hv' hBv' hg hR⟩
    rw [add_assoc]
    refine add_le_add le_rfl ?_
    rw [← ENNReal.ofReal_add hL0 (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsq : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 (hRpos n)
    rw [← add_div]
  have hlast : (K n).toHistory.activeStage v ≠ Fin.last (K n).eventCount := hlastF
  obtain ⟨j', hj'⟩ := Fin.exists_castSucc_eq.mpr hlast
  have ht1 : (K n).time j'.castSucc < v := by
    change (K n).toHistory.time j'.castSucc < v
    rw [hj']
    exact hage
  have ht2 : (v : ℝ) < (K n).time j'.succ := by
    have hlt : ((K n).toHistory.activeStage v : ℕ) < (K n).toHistory.eventCount := by
      rw [← hj']
      exact j'.isLt
    have h := (K n).toHistory.activeStage_before_next v hlt
    have heq : (⟨((K n).toHistory.activeStage v : ℕ) + 1, by omega⟩ :
        Fin ((K n).toHistory.eventCount + 1)) = j'.succ := by
      apply Fin.ext
      simp only [← hj', Fin.val_castSucc, Fin.val_succ]
    rwa [heq] at h
  have h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc := by
    rw [hj']
    exact (K n).toHistory.activeStage_mono hav
  have h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n) := by
    rw [hj']
    exact (K n).toHistory.activeStage_mono (hvt.trans (hsT n))
  have hs := point_heq_of_eq_P6M2 (seedTrace n) hj'.symm ((K n).toHistory.activeStage_mono hav)
    ((K n).toHistory.activeStage_mono (hvt.trans (hsT n))) h1 h2
  have hfn : (K n).toHistory.activeStage v ≤ j'.castSucc := le_of_eq hj'.symm
  have hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n) :=
    (le_of_eq hj').trans ((K n).toHistory.activeStage_mono hvt)
  have hzj := point_heq_of_eq_P6M2 tr₁ hj'.symm le_rfl ((K n).toHistory.activeStage_mono hvt)
    (hfn.trans le_rfl) hjσ
  have hΛv : Λ ≤ R n * v := by
    have hRv : R n * ((σ n : ℝ) + σ₁ / R n) ≤ R n * v :=
      mul_le_mul_of_nonneg_left hv1 (hRpos n).le
    have hRne := (hRpos n).ne'
    have heq : R n * ((σ n : ℝ) + σ₁ / R n) = R n * σ n + σ₁ := by
      field_simp
    linarith
  have hL0 : 0 ≤ L n / 4 / Real.sqrt (R n) := by
    have : 0 < Dd := hDd
    have : 0 ≤ L n := by linarith
    positivity
  refine hmain (K n) (T₀ n) (recordsK n) (hcanK n) e2 e3 e4 (hpinchK0 n) (recordsF n)
    (1 / ((n : ℝ) + 1)) (hδF n) e1 (max ((n : ℝ) + 1) (Q n)) (a₀ n)
    (lt_of_lt_of_le (by positivity) (le_max_left _ _)) (fun x => (hHI n x).1)
    (fun x => (hHI n x).2) e5 j'
    (fun i hi y' t' ht hR' => hslabK n i y' t' ⟨ht.1, lt_min ht.2 (ht.2.trans_le
      ((time_succ_le_of_castSucc_lt_A6K (K n) hi).trans (ht1.le.trans hvtK)))⟩
      ((le_max_right _ _).trans_lt hR')) v ht1 ht2
    (fun y' t' ht hR' => hslabK n j' y' t' ⟨ht.1, lt_min (ht.2.trans ht2) (ht.2.trans_le hvtK)⟩
      ((le_max_right _ _).trans_lt hR'))
    (R n) (ρV n) (hRpos n) e6 hΛv e8
    hT₀v _ hj'.symm
    (tr₁.point _ le_rfl _) _ _ hs _ (e12 x₁ hx₁ v hav hvt hv1 tr₁)
    ((tr₁.restrictFirst hfn hjσ).point j'.castSucc le_rfl hjσ) hzj ?_
  intro w hw hzw hRw
  refine (fun H => ?hUe) (e13 j' v ht1 ht2 hv1 hv2 x₁ hx₁ hjσ (tr₁.restrictFirst hfn hjσ) h1 h2 w
    (hw.trans ?hde) hzw hRw)
  case hUe =>
    obtain ⟨u1, u2, u3, u4, u5⟩ := H
    exact ⟨u1, u2, u3, u4, fun i first hf z hz Btr v' hv' hBv' hg hR =>
      u5 (Fin.castLE (Nat.le_of_lt_succ j'.castSucc.isLt) i)
        (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j'.castSucc.isLt)) first)
        (Fin.le_def.mpr (Fin.le_def.mp hf)) (Fin.lt_def.mpr i.isLt) z hz
        ((K n).backwardPointTraceOfPrefix j'.castSucc Btr) v' hv' hBv' hg hR⟩
  rw [add_assoc]
  refine add_le_add le_rfl ?_
  rw [← ENNReal.ofReal_add hL0 (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsq : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 (hRpos n)
  rw [← add_div]

/-- **F5 截断 final 条件形孪生（`_HFT`，PROVED）**：`…final_cond_localGT_KFP` 逐字，`hfin` 删去，
`hUVCF` 槽在 `v` 前加 `∀ hfn`。 -/
theorem ObservedHistory.hbcadC_lateHI_of_slice_data_final_cond_localGT_HFT
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Cg : ℝ} (hCg : 1 ≤ Cg)
    {K : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon →
      ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n h, G n h = ((K n).finalSlab h).restrictIncoming le_rfl h le_rfl)
    {Q T₀ tK : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
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
    (hslabK : ∀ n (j₀ : Fin (K n).eventCount),
      ((K n).toHistory.event j₀).incoming.DerivativeBoundBefore Ctime (Q n)
        (min ((K n).time j₀.succ) (tK n)))
    (hpinchF : ∀ n h, Perelman.PhiAlmostNonnegative (G n h).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi)
    (hderF : ∀ n h, (G n h).DerivativeBoundBefore Ctime (Q n) (min (K n).horizon (tK n)))
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt (σ
      n)).Carrier)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n)
    (hTnK : ∀ n, (Tn n : ℝ) ≤ tK n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * D / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
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
    (hUVC : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
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
            ENNReal.ofReal ((L n / 4 + Dd) / Real.sqrt (R n)) →
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
            (v - v') * max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
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
            (v - τ) * max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
                  ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                  (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                    zz b)) ∧
          (∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).toHistory.time j'.castSucc) v,
            v - B / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((K n).toHistory.event j').incoming.flow.scalar v' x →
            (v - v') * max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            |derivWithin (fun s => ((K n).toHistory.event j').incoming.flow.scalar s x)
                (Iic v') v'| ≤
              Ctime * ((K n).toHistory.event j').incoming.flow.scalar v' x ^ 2) ∧
          (∀ (i : Fin (K n).toHistory.eventCount) (first : Fin ((K n).toHistory.eventCount + 1))
              (hf : first ≤ i.castSucc) (hij : i.castSucc < j'.castSucc),
            ∀ z ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((K n).toHistory.event j').incoming.flow.scalar v w)),
            ∀ Btr : BackwardPointTrace (K n).toHistory first j'.castSucc (hf.trans hij.le) z,
            ∀ v' ∈ Ioo ((K n).toHistory.time i.castSucc) ((K n).toHistory.time i.succ),
            v - B / ((K n).toHistory.event j').incoming.flow.scalar v w ≤ v' →
            (v - v') * max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            Cg * R n < ((K n).toHistory.event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf hij.le) →
            |derivWithin (fun s => ((K n).toHistory.event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf hij.le)) (Iic v') v'| ≤
              Ctime * ((K n).toHistory.event i).incoming.flow.scalar v'
                (Btr.point i.castSucc hf hij.le) ^ 2))
    (hUVCF : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (hfn : (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
      (v : ℝ), (K n).time (Fin.last (K n).eventCount) < v →
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
        riemannianEDistOf ((G n hfn).flow.base.metric v)
            ((seedTrace n).point (Fin.last (K n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal ((L n / 4 + Dd) / Real.sqrt (R n)) →
        riemannianEDistOf ((G n hfn).flow.base.metric v)
            (tr.point (Fin.last (K n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R
              n)) →
        R n ≤ (G n hfn).flow.scalar v w →
          (∀ x ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            Cg * R n < (G n hfn).flow.scalar v x →
            ∃ W : SpatialCanonicalWitness ((G n hfn).flow.base.metric v)
              ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
          (∀ x ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) v,
            v - B / (G n hfn).flow.scalar v w ≤ v' →
            Cg * R n < (G n hfn).flow.scalar v' x →
            (v - v') * max (Cg * R n) ((G n hfn).flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential (G n hfn).flow v' x ξ| ≤
                Cgrad * (G n hfn).flow.scalar v' x *
                  Real.sqrt ((G n hfn).flow.scalar v' x) *
                  Real.sqrt (((G n hfn).flow.base.metric v').inner x ξ ξ)) ∧
          (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon),
            v - B / (G n hfn).flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (K n).time (Fin.last (K n).eventCount) < τ → (τ : ℝ) < (K n).horizon →
            ∀ z ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                  (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            (v - τ) * max (Cg * R n) ((G n hfn).flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
                  ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                  (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                    zz b)) ∧
          (∀ x ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) v,
            v - B / (G n hfn).flow.scalar v w ≤ v' →
            Cg * R n < (G n hfn).flow.scalar v' x →
            (v - v') * max (Cg * R n) ((G n hfn).flow.scalar v x) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            |derivWithin (fun s => (G n hfn).flow.scalar s x) (Iic v') v'| ≤
              Ctime * (G n hfn).flow.scalar v' x ^ 2) ∧
          (∀ (i : Fin (K n).eventCount) (first : Fin ((K n).eventCount + 1))
              (hf : first ≤ i.castSucc),
            ∀ z ∈ riemannianBallOf ((G n hfn).flow.base.metric v) w
                (Rad / Real.sqrt ((G n hfn).flow.scalar v w)),
            ∀ Btr : BackwardPointTrace (K n).toHistory first (Fin.last (K n).eventCount)
              (hf.trans (Fin.castSucc_lt_last i).le) z,
            ∀ v' ∈ Ioo ((K n).time i.castSucc) ((K n).time i.succ),
            v - B / (G n hfn).flow.scalar v w ≤ v' →
            (v - v') * max (Cg * R n) ((G n hfn).flow.scalar v z) ≤
              1 / (2 * max (Ctime : ℝ) 1) →
            Cg * R n < ((K n).toHistory.event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) →
            |derivWithin (fun s => ((K n).toHistory.event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le)) (Iic v') v'| ≤
              Ctime * ((K n).toHistory.event i).incoming.flow.scalar v'
                (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) ^ 2)) :
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T Kc : ℝ, -σ' < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * Dw / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
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
    ObservedHistory.hbcadC_of_slice_dichotomy_open_final_P6FC.{u}
  have hR1 : ∀ᶠ n in atTop, 1 ≤ R n := Eventually.of_forall fun n => by
    have h1 := hRn1 n
    have h3 : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  refine hB K σ y R hRpos hR1 ?_
  intro A Dd hA hDd
  obtain ⟨QB, Dcap, D₂, Rad, Bw, hQB, hD₂, hcore⟩ :=
    ObservedHistory.hsliceR_lateHI_core_final_localGT_HFT hεle hκ hphi hCg hη₃ hLc hG recordsF
      hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK hpinchF hderF σ y R hRpos hRn1
      hT₀
      Tn aSeed haT hsT hTnK has pT seedTrace L hL hwin ρV hρV A Dd hA hDd
  refine ⟨QB, Dcap, D₂, hQB, hD₂, fun φ hφ σ₁ σ₂ h12 hσ₂ Dw hDw T Kc hT hKc htr => ?_⟩
  refine hcore (map φ atTop) hφ.tendsto_atTop σ₁ σ₂ h12 hσ₂ Dw hDw ?_
    (hUVC Rad Bw σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr)
    (hUVCF Rad Bw σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr)
  filter_upwards [hdistQC φ hφ Dw T Kc hDw (by linarith) hKc htr] with n hn
  intro x hx v hav hvs hv tr
  refine hn x hx v hav hvs ?_ tr
  have h1 : -T / R n ≤ σ₁ / R n := div_le_div_of_nonneg_right (by linarith) (hRpos n).le
  rw [sub_eq_add_neg, ← neg_div]
  linarith

/-- **F7g2 截断 final 条件形孪生（`_HFT`，PROVED）**：`hbcadC_final_of_guarded2T_KFP` 逐字，`hfin` 删去，
final 数据条件形；结论（`hbcadC` 槽）逐字同原件、不含 `G`。 -/
theorem ObservedHistory.hbcadC_final_of_guarded2T_HFT
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime' : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Cg : ℝ} (hCg : 1 ≤ Cg)
    {K : ℕ → RetainedCoreHistory.{u}}
    {G : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon →
      ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n h, G n h = ((K n).finalSlab h).restrictIncoming le_rfl h le_rfl)
    {Q T₀ tK : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
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
    (hslabK : ∀ n (j₀ : Fin (K n).eventCount),
      ((K n).toHistory.event j₀).incoming.DerivativeBoundBefore Ctime' (Q n)
        (min ((K n).time j₀.succ) (tK n)))
    (hpinchF : ∀ n h, Perelman.PhiAlmostNonnegative (G n h).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi)
    (hderF : ∀ n h, (G n h).DerivativeBoundBefore Ctime' (Q n) (min (K n).horizon (tK n)))
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n)
    (hTnK : ∀ n, (Tn n : ℝ) ≤ tK n) (has : ∀ n, aSeed n ≤ σ n)
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
    :
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
  have hUVC := ObservedHistory.hUVC_of_selection_Cg_guarded_A6K (Ctime' := Ctime') (Cg := Cg) hC2
    (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT seedTrace y R L r ρV hRpos hL hgood hwin
    hroom hdistσ hκR rfl hCg hRn1 hcanK hacc hrad hord hscaleK hslabK hTnK hT₀ hrX hsmall hclock
    aP haP hpin hRa T₀X hT₀X hOldX
  have hUVCF := ObservedHistory.hUVCF_of_selection_Cg_guarded2T_HFT (Ctime' := Ctime') (Cg := Cg)
      hC2
    hG Tn aSeed σ haT hsT has pT seedTrace y R L r ρV hRpos hL hgood hwin hroom hdistσ hκRF
    hCg hRn1 hrX hsmall hclock aP haP hpin hRa hcanK hacc hrad hord hscaleK hslabK hderF hTnK hT₀
    T₀X hT₀X hOldX
  exact ObservedHistory.hbcadC_lateHI_of_slice_data_final_cond_localGT_HFT hεle hκ hphi hCg hG
    recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK hpinchF hderF σ y R hRpos
    hRn1 hT₀ Tn aSeed haT hsT hTnK has pT seedTrace L hL hwin ρV hρV hdistQC hUVC hUVCF

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
