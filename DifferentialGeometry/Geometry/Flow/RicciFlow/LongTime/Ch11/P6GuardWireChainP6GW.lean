import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardWireP6GW

/-!
# GUARDWIRE G2：hdistW event 全链 hseedTop 消去（O-CH11-GUARDWIRE，后缀 `_P6GW`）

`hdistW_eventSlab_guarded_P6GW` = ANCHOR5 `hdistW_eventSlab_of_hgood_local_noJ10_P6AN5` 的 guarded
孪生：
top-anchor 半 `topAnchorInputs_guarded_P6GW`（G1，guarded 合同）→
`hanchor0_event_of_topInputsGuarded_P6GW`
（ShortSLT 侧由 KSWEXIT `shortSLT_guarded_C11KX` 付，无 binder）；depth 半 / `hσev` /
`hdistW_of_firstExit_P6DW`
合成逐字。**结论 = `hdistW` 槽逐字（event 支）**。

**binder 增减表（相对 ANCHOR5 event 全链）**：−1 `hseedTop`（BLOCKED → 消去）；+1 `0 ≤ C2g`（hgood witness 梯度常数
的符号，平凡常数条件，`localPropagationRadius_pos` 需要）。K0 `hsmall / hclock / hRr`、`hwin`、`hpin`、`hL` 原表已有，
现在同时供 P6DW 与 point-anchor。净变化：hseedTop → `0 ≤ C2g`。

**剩余 binder 表（event 支，诚实口径）**：`hslabSel`（J10 残余，见下段）；`hdepthA`（depth driver 槽，⇐ J10GEN2A
无 J10 late_cond driver，PROVISIONAL binder 照其块）；`hkappa`；hgood（`HgoodCg_C11SH`，`εg ≤ coneAccuracy`）；
selection supplies（`records / hcan / hqcan / hpar / hscale / hθcap / hpinch / hnot / hT₀ / hRt`）+
`hR / hRlim`；
P6DW K0 / HI（`hsmall / hclock / hRr / hwin / hpin / hL`）；`hC2`、`0 ≤ C2g`（平凡）。hbcadC 不在本链（depth 槽的
producer 侧）。

**跨 slab `hslabs` 的来源（关闭 KSWEXIT HANDOVER 剩余 (2)）**：`ShortSLTGuarded_C11KX` 的 `hslabs`（早 event slab
沿 `B.point` 的时间导数）在 ANCHOR 链里**只**由 `hslabSel : EventSlabsDerivative Ctime (Cg·R_n)`（prefix 全局导数
背景，`hderE_of_slabSel_P6AN5`）付，**不经 U 侧 WindowSeed / point-anchor** ⇒ guard 在该槽直接丢弃，不需要跨 slab
trace 版 point-anchor（WSBASE G3 §2b 的待确认项 = 否）。guarded 改接**不改变** `hslabSel` 的阈值形
（`Q ≤ Cg·R`，J10 换皮），J10 残余仍由 SLTLOCAL（SLT 核 `eventually_scalar_bound_at_distance_window_P6M` 孪生）负责。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

/-- **G2 `hdistW_eventSlab_guarded_P6GW`（`_P6GW`，PROVISIONAL：binder = `hslabSel`（J10 残余，阈值形不变，owner
SLTLOCAL）+ `hdepthA`（⇐ J10GEN2A）+ `hkappa` + hgood + selection supplies + P6DW K0 / HI + `hR /
hRlim` +
`0 ≤ C2g`；**无 hseedTop**、无 `hqR`）**：ANCHOR5 `hdistW_eventSlab_of_hgood_local_noJ10_P6AN5` 的孪生，只把
hseedTop 换成 `0 ≤ C2g`（seed localization 改由 WSBASE point-anchor 在 guard 点付，ShortSLT 改 guarded 合同）。
结论 = `hdistW` 槽逐字（event 支）。 -/
theorem hdistW_eventSlab_guarded_P6GW :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {j : ∀ n, Fin (K n).eventCount} → {t : ℕ → ℝ} →
      (hjt : ∀ n, (K n).time (j n).castSucc < t n) → (htj : ∀ n, t n < (K n).time (j n).succ) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (j n).castSucc).eventCount),
        T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (j n).castSucc).toHistory i (p n)} →
      {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier} →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsPinched phi ∧
        Perelman.PhiAlmostNonnegative ((K n).toHistory.event (j n)).incoming.flow
          (Ico ((K n).time (j n).castSucc) ((K n).time (j n).succ)) phi) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (j n).castSucc).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (j n).castSucc).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (j n).castSucc).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory i.succ
          (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) hl (yG n))
        (b : (((K n).prefixAt (j n).castSucc).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (j n).castSucc).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      {β : ℝ} → (hβ : 0 < β) →
      (hβ2 : β ≤ 1 / 2) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
      (hR : ∀ n, 0 < R n) → (hRlim : Tendsto R atTop atTop) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      (hdepthA : (∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
          ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
              (yG n)
              (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
            ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
              Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n)) →
        ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R (φ ∘ ψ) T) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
      (L : ℕ → ℝ) (r : ℕ → ℝ),
      ∀ {Cg εg C1g C2g : ℝ} {Ctg : ℝ≥0}, 0 < Cg → εg ≤ coneAccuracy →
      ObservedHistory.HgoodCg_C11SH Cg Kh Tn aSeed σ haT hsT has pT seedTrace y R L εg C1g C2g
        Ctg →
      (∀ n, ((K n).prefixAt (j n).castSucc).EventSlabsDerivative Ctime (Cg * R n)
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount)) →
      ∀ {Cgrad : ℝ≥0}, C2g ≤ (Cgrad : ℝ) →
      0 ≤ C2g →
      Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      ∀ {a₁ : ℝ}, 0 ≤ a₁ →
      (∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₁ + τ') x) →
      ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro Ctime phi hphi K j t hjt htj D θcap qcan T₀ p δb records yG hcan hqcan hpar hscale hθcap
    hpinch hnot hT₀ hRt β hβ hβ2 Kh hKh σ y R hσ hyG hRn hR hRlim κ hκ ρnc hradii hkappa hdepthA
    Tn aSeed haT hsT has pT seedTrace L r Cg εg C1g C2g Ctg hCg hεg hgood hslabSel Cgrad hC2
    hC20 hL hsmall hclock hRr hwin a₁ ha₁ hpin
  subst hKh
  have hin := topAnchorInputs_guarded_P6GW hβ hβ2 hjt htj hcan hqcan hpar hscale
    hθcap hphi hpinch hnot hT₀ hRt hCg hgood hσ hyG hRn hR hRlim hslabSel hL hεg hκ hradii hC2 hwin
    hC20 hsmall hclock hRr ha₁ hpin hkappa
  have hanc := hanchor0_event_of_topInputsGuarded_P6GW hβ hjt htj hin
  exact ObservedHistory.hdistW_of_firstExit_P6DW (fun n => (K n).toHistory) Tn aSeed σ haT hsT has
    pT seedTrace y R L hR r hL hsmall hclock hRr hwin ha₁ hpin
    (hσev_of_selection_P6AN3 hjt htj (fun n => (K n).toHistory) rfl σ hσ)
    (ObservedHistory.hscalW_eventually_of_subseqDriver_P6AN2 (fun n => (K n).toHistory) Tn aSeed σ
      haT hsT has pT seedTrace y R L hR (fun φ hφ _ => hdepthA hanc φ hφ))

/-- consumer（G2，`_P6GW`）：event 全链的 top-anchor 半不再吃 hseedTop——`topAnchorInputs_guarded_P6GW` 喂
KSWEXIT
guarded adapter（`hdistW_eventSlab_guarded_P6GW` 即如此使用）。 -/
example := @hdistW_eventSlab_guarded_P6GW.{u}

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
