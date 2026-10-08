import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResJ10JP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HnotPrefixHNF

/-!
# J10TAIL G1：J10 块尾平移（`_JT`）

`J10ResE2_DJ`（J10PAY）四项中 `hDmX` / `hT₀X` 是 `∀ n`，producer 只给 `∀ᶠ`。driver 核（DW / DT / Cg）里 J10
只用于产出 `∃ Cst, hsurv ∧ hext`（`J10Blk_JT`）；`hsurv` 是 `∀ᶠ n`，`hext` 的 `DepthExtendable` 是
`∀ A ∃ K ∀ᶠ i`，二者对下标尾平移不变。故在平移族 `K (n + N)` 上调用 `j10ResE_of_2_JP`，再平移回来：
* `J10ResE3_JT`：更小残余 = 逐点形 `hnot`（其余三项不再是 J10 残余；`hT₀X` 以
  `∀ᶠ` 形留在 DrvResE 孪生，`a₀K > 0` 由引擎级 `a₀` 付）；
* `j10ResE2_of_3_JT`（PROVED）：同族形，`a₀K > 0`、`hDmX`、`hT₀X` ∀ n ⇒ `J10ResE2_DJ`；
* `j10ResE2_shift_of_3_JT`（PROVED）：尾平移形，`hrad` + `N > transitionEnd + 10` 付 `hDmX`；
* `j10Blk_of_tail_JT`（PROVED）：`j10ResE_of_2_JP` 前提 + `J10ResE3_JT` + `0 < a₀K` + `∀ᶠ hT₀X`
  ⇒ `J10Blk_JT`。
无新顶层 binder。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open ObservedHistory (DepthExtendable)

/-! ## 平移小工具 -/

theorem eventually_add_JT {P : ℕ → Prop} (N : ℕ) (h : ∀ᶠ n in atTop, P n) :
    ∀ᶠ n in atTop, P (n + N) :=
  (tendsto_add_atTop_nat N).eventually h

theorem eventually_of_add_JT {P : ℕ → Prop} (N : ℕ) (h : ∀ᶠ n in atTop, P (n + N)) :
    ∀ᶠ n in atTop, P n := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 h
  refine Filter.eventually_atTop.2 ⟨M + N, fun n hn => ?_⟩
  have h' := hM (n - N) (by omega)
  rwa [Nat.sub_add_cancel (by omega : N ≤ n)] at h'

theorem shiftLe_JT (n N : ℕ) : (n : ℝ) + 1 ≤ ((n + N : ℕ) : ℝ) + 1 := by
  have : (n : ℝ) ≤ ((n + N : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right n N
  linarith

theorem shiftInv_JT (n N : ℕ) : 1 / (((n + N : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
  one_div_le_one_div_of_le (by positivity) (shiftLe_JT n N)

theorem shiftScale_JT (n N : ℕ) (q : ℝ) :
    ((n : ℝ) + 1) * max ((n : ℝ) + 1) q ≤ (((n + N : ℕ) : ℝ) + 1) * max (((n + N : ℕ) : ℝ) + 1) q :=
  mul_le_mul (shiftLe_JT n N) (max_le_max (shiftLe_JT n N) le_rfl)
    ((by positivity : (0 : ℝ) ≤ (n : ℝ) + 1).trans (le_max_left _ _)) (by positivity)

theorem shiftTheta_JT (n N : ℕ) :
    1 - 1 / ((n : ℝ) + 2) ≤ 1 - 1 / (((n + N : ℕ) : ℝ) + 2) := by
  have : (n : ℝ) ≤ ((n + N : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right n N
  have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (n : ℝ) + 2)
    (by linarith : (n : ℝ) + 2 ≤ ((n + N : ℕ) : ℝ) + 2)
  linarith

/-- **J10 块（`_JT`，逐字缩写 def，非合同 Prop）**：`drvSlots_K_of_J10_sepT_HSX` 结论逐字
（= DW / DT / Cg driver 核的 `∃ Cst, hsurv ∧ hext` 合取）。 -/
def J10Blk_JT (K : ℕ → RetainedCoreHistory.{u}) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (yK : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier) (R : ℕ → ℝ) : Prop :=
  ∃ (Cst : ℝ≥0),
    (∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
      ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ᶠ n in atTop,
        (∀ z ∈ riemannianBallOf ((K n).toHistory.stageMetric
            ((K n).toHistory.activeStage (σ n)) (σ n)) (yK n) (A / Real.sqrt (R n)),
          metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            z ≤ Q * R n) →
        (K n).toHistory.isTracedRegion (σ n) (yK n) (A / Real.sqrt (R n)) (T / R n) (Kc * R n)) ∧
    (∀ σs : ℕ → ℕ, StrictMono σs → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable (fun n => (K n).toHistory) σ yK R σs T) →
      (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((K (σs i)).toHistory.stageMetric
          ((K (σs i)).toHistory.activeStage (σ (σs i))) (σ (σs i))) (yK (σs i))
          (A / Real.sqrt (R (σs i))),
      ∀ (w : Icc (0 : ℝ) (K (σs i)).toHistory.horizon),
        (w : ℝ) = σ (σs i) - T' / R (σs i) →
      ∀ (hwt : w ≤ σ (σs i))
        (Bt : BackwardPointTrace (K (σs i)).toHistory ((K (σs i)).toHistory.activeStage w)
          ((K (σs i)).toHistory.activeStage (σ (σs i)))
          ((K (σs i)).toHistory.activeStage_mono hwt) x),
        metricScalarAt ((K (σs i)).toHistory.stageMetric ((K (σs i)).toHistory.activeStage w) w)
          (Bt.point ((K (σs i)).toHistory.activeStage w) le_rfl
            ((K (σs i)).toHistory.activeStage_mono hwt)) ≤
          M * R (σs i)) →
      DepthExtendable (fun n => (K n).toHistory) σ yK R σs
        (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1))))

/-- **J10 块尾平移（`_JT`，PROVED）**：平移族上的 J10 块 ⇒ 原族 J10 块（同 `Cst`）。 -/
theorem j10Blk_of_shift_JT {K : ℕ → RetainedCoreHistory.{u}}
    {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {yK : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R : ℕ → ℝ} (N : ℕ)
    (h : J10Blk_JT (fun n => K (n + N)) (fun n => σ (n + N)) (fun n => yK (n + N))
      (fun n => R (n + N))) :
    J10Blk_JT K σ yK R := by
  obtain ⟨Cst, hsurv, hext⟩ := h
  refine ⟨Cst, fun A T Q hA hT hQ hCQ => ?_, fun σs hσs Tstar M hTs hM hDE hcur => ?_⟩
  · obtain ⟨Kc, hKc, hev⟩ := hsurv A T Q hA hT hQ hCQ
    exact ⟨Kc, hKc, eventually_of_add_JT (P := fun n =>
      (∀ z ∈ riemannianBallOf ((K n).toHistory.stageMetric
          ((K n).toHistory.activeStage (σ n)) (σ n)) (yK n) (A / Real.sqrt (R n)),
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          z ≤ Q * R n) →
      (K n).toHistory.isTracedRegion (σ n) (yK n) (A / Real.sqrt (R n)) (T / R n) (Kc * R n))
      N hev⟩
  · have hge : ∀ i, N ≤ σs (i + N) := fun i => le_trans (Nat.le_add_left N i) (hσs.id_le (i + N))
    obtain ⟨σs', hσs'⟩ : ∃ f : ℕ → ℕ, ∀ i, f i = σs (i + N) - N := ⟨_, fun _ => rfl⟩
    have hidx : ∀ i, σs' i + N = σs (i + N) := fun i => by
      rw [hσs' i]
      exact Nat.sub_add_cancel (hge i)
    have hmono : StrictMono σs' := fun a b hab => by
      have h1 := hσs (by omega : a + N < b + N)
      have h2 := hidx a
      have h3 := hidx b
      omega
    have keyT : ∀ (A T Kc : ℝ) (m m' : ℕ), m = m' →
        (K m).toHistory.isTracedRegion (σ m) (yK m) (A / Real.sqrt (R m)) (T / R m) (Kc * R m) →
        (K m').toHistory.isTracedRegion (σ m') (yK m') (A / Real.sqrt (R m')) (T / R m')
          (Kc * R m') := by
      rintro A T Kc m _ rfl hm
      exact hm
    have hDE' : ∀ T : ℝ, 0 < T → T < Tstar →
        DepthExtendable (fun n => (K (n + N)).toHistory) (fun n => σ (n + N))
          (fun n => yK (n + N)) (fun n => R (n + N)) σs' T := by
      intro T hT hTT A hA
      obtain ⟨Kc, hKc, hev⟩ := hDE T hT hTT A hA
      refine ⟨Kc, hKc, ?_⟩
      filter_upwards [eventually_add_JT N hev] with i hi
      exact keyT A T Kc _ _ (hidx i).symm hi
    have keyC : ∀ (T' A : ℝ) (m m' : ℕ), m = m' →
        (∀ x ∈ riemannianBallOf ((K m).toHistory.stageMetric
            ((K m).toHistory.activeStage (σ m)) (σ m)) (yK m) (A / Real.sqrt (R m)),
          ∀ (w : Icc (0 : ℝ) (K m).toHistory.horizon), (w : ℝ) = σ m - T' / R m →
          ∀ (hwt : w ≤ σ m)
            (Bt : BackwardPointTrace (K m).toHistory ((K m).toHistory.activeStage w)
              ((K m).toHistory.activeStage (σ m)) ((K m).toHistory.activeStage_mono hwt) x),
            metricScalarAt ((K m).toHistory.stageMetric ((K m).toHistory.activeStage w) w)
              (Bt.point ((K m).toHistory.activeStage w) le_rfl
                ((K m).toHistory.activeStage_mono hwt)) ≤ M * R m) →
        (∀ x ∈ riemannianBallOf ((K m').toHistory.stageMetric
            ((K m').toHistory.activeStage (σ m')) (σ m')) (yK m') (A / Real.sqrt (R m')),
          ∀ (w : Icc (0 : ℝ) (K m').toHistory.horizon), (w : ℝ) = σ m' - T' / R m' →
          ∀ (hwt : w ≤ σ m')
            (Bt : BackwardPointTrace (K m').toHistory ((K m').toHistory.activeStage w)
              ((K m').toHistory.activeStage (σ m')) ((K m').toHistory.activeStage_mono hwt) x),
            metricScalarAt ((K m').toHistory.stageMetric ((K m').toHistory.activeStage w) w)
              (Bt.point ((K m').toHistory.activeStage w) le_rfl
                ((K m').toHistory.activeStage_mono hwt)) ≤ M * R m') := by
      rintro T' A m _ rfl hm
      exact hm
    have hcur' := fun (T' : ℝ) (hT' : 0 < T') (hTT : T' < Tstar) (A : ℝ) (hA : 0 < A) =>
      (eventually_add_JT N (hcur T' hT' hTT A hA)).mono fun i hi =>
        keyC T' A _ _ (hidx i).symm hi
    have hfin := hext σs' hmono Tstar M hTs hM hDE' hcur'
    intro A hA
    obtain ⟨Kc, hKc, hev⟩ := hfin A hA
    refine ⟨Kc, hKc, ?_⟩
    refine eventually_of_add_JT (P := fun i => (K (σs i)).toHistory.isTracedRegion (σ (σs i))
      (yK (σs i)) (A / Real.sqrt (R (σs i)))
      ((Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1))) / R (σs i)) (Kc * R (σs i))) N ?_
    exact hev.mono fun i hi => keyT A _ Kc _ _ (hidx i) hi

/-! ## 更小残余 `J10ResE3_JT` 与同族形 `j10ResE2_of_3_JT` -/

/-- **更小残余（`_JT`，逐字缩写 def，非合同 Prop）**：`J10ResE2_DJ` 的 `hnot` 项，逐点形
（`∀ n jn`，而非 `∀ j : ∀ n, …`；便于尾平移）。`a₀K > 0` / `hDmX` / `hT₀X` 不再是残余。 -/
def J10ResE3_JT (K : ℕ → RetainedCoreHistory.{u})
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (yK : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (qK : ℕ → CutoffParameters) (T₀K : ℕ → ℝ)
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n)) : Prop :=
  ∀ (n : ℕ) (jn : Fin (K n).eventCount) (_hjt : (K n).time jn.castSucc < (σ n : ℝ))
    (_htj : (σ n : ℝ) < (K n).time jn.succ) (yG : ((K n).stage jn.castSucc).Carrier),
    HEq (yK n) yG →
    ¬ ∃ (i : Fin ((K n).prefixAt jn.castSucc).eventCount)
      (hi : T₀K n ≤ ((K n).prefixAt jn.castSucc).time i.succ)
      (hl : i.succ ≤ Fin.last ((K n).prefixAt jn.castSucc).eventCount)
      (A : BackwardPointTrace ((K n).prefixAt jn.castSucc).toHistory i.succ
        (Fin.last ((K n).prefixAt jn.castSucc).eventCount) hl yG)
      (b : (((K n).prefixAt jn.castSucc).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (qK n).modelRadius),
      A.point i.succ le_rfl hl =
          (((K n).prefixLateRecords_P6N jn.castSucc (recordsK n) i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        (σ n : ℝ) - ((K n).prefixAt jn.castSucc).time i.succ ≤
          (1 - 1 / ((n : ℝ) + 2)) *
            ((((K n).prefixLateRecords_P6N jn.castSucc (recordsK n) i hi).static b).neck.scale)⁻¹

/-- **同族形（`_JT`，PROVED）**：`0 < a₀K`、`hDmX`、`hT₀X`（∀ n）+ `J10ResE3_JT` ⇒ `J10ResE2_DJ`。 -/
theorem j10ResE2_of_3_JT {K : ℕ → RetainedCoreHistory.{u}}
    {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {yK : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier}
    {qK : ℕ → CutoffParameters} {T₀K : ℕ → ℝ}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n)} {a₀K : ℕ → ℝ}
    (ha₀ : ∀ n, 0 < a₀K n) (hDm : ∀ n, StandardCap.transitionEnd + 10 < (qK n).modelRadius)
    (hT₀X : ∀ n, T₀K n ≤ (σ n : ℝ) - (1 / 100 : ℝ) ^ 2)
    (h3 : J10ResE3_JT K σ yK qK T₀K recordsK) :
    J10ResE2_DJ K σ yK qK T₀K recordsK a₀K :=
  ⟨ha₀, hDm, hT₀X, fun j hjt htj yG hyG n => h3 n (j n) (hjt n) (htj n) (yG n) (hyG n)⟩

/-- **尾平移形（`_JT`，PROVED）**：`N > transitionEnd + 10`、`hrad`、`0 < a₀K`、尾段 `hT₀X` +
`J10ResE3_JT`（原族）⇒ 平移族 `J10ResE2_DJ`（hnot 经 `capNot_mono_HNF` 由 `D, θ` 单调降档）。 -/
theorem j10ResE2_shift_of_3_JT {K : ℕ → RetainedCoreHistory.{u}}
    {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {yK : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier}
    {qK : ℕ → CutoffParameters} {T₀K : ℕ → ℝ}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n)} {a₀K : ℕ → ℝ} (N : ℕ)
    (hN : StandardCap.transitionEnd + 10 < (N : ℝ))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (qK n).modelRadius)
    (ha₀ : ∀ n, 0 < a₀K n) (hT₀X : ∀ n, T₀K (n + N) ≤ (σ (n + N) : ℝ) - (1 / 100 : ℝ) ^ 2)
    (h3 : J10ResE3_JT K σ yK qK T₀K recordsK) :
    J10ResE2_DJ (fun n => K (n + N)) (fun n => σ (n + N)) (fun n => yK (n + N))
      (fun n => qK (n + N)) (fun n => T₀K (n + N)) (fun n => recordsK (n + N))
      (fun n => a₀K (n + N)) := by
  refine ⟨fun n => ha₀ (n + N), fun n => ?_, hT₀X, fun j hjt htj yG hyG n => ?_⟩
  · have h1 : (N : ℝ) ≤ ((n + N : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left N n
    have h2 := hrad (n + N)
    linarith
  · exact RetainedCoreHistory.capNot_mono_HNF ((K (n + N)).prefixAt (j n).castSucc) (Fin.last _)
      ((K (n + N)).prefixLateRecords_P6N (j n).castSucc (recordsK (n + N))) (yG n)
      (shiftLe_JT n N) (shiftTheta_JT n N) (h3 (n + N) (j n) (hjt n) (htj n) (yG n) (hyG n))

/-! ## J10 块 ⇐ J10 帧前提包（同族，`drvResE_DW_of_RX_HSX` 的 J10 段） -/

/-- **J10 块（`_JT`，PROVED）**：`J10ResE_RX_HSX` + DrvResE 合取 1/3/4/6 + `hev` ⇒ `J10Blk_JT`
（`drvResE_DW_of_RX_HSX` 的 J10 段逐字抽出）。 -/
theorem j10Blk_of_J10ResE_JT {K : ℕ → RetainedCoreHistory.{u}}
    {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R : ℕ → ℝ}
    {qK : ℕ → CutoffParameters} {T₀K : ℕ → ℝ}
    (recK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n))
    (hsep : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ) b,
        (σ n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) < ((recK n i hi).static b).neck.scale)
    (hcanK : ∀ n i hi b, ((recK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (qK n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hord : ∀ n : ℕ, n + 2 ≤ (qK n).modelOrder)
    (hRdef : ∀ n, R n = metricScalarAt ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n))
    (hRpos : ∀ n, 0 < R n) (hRr : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hev : ∀ n, ∃ j : Fin (K n).eventCount, (K n).time j.castSucc < (σ n : ℝ) ∧
      (σ n : ℝ) < (K n).time j.succ)
    (hJ : J10ResE_RX_HSX K σ y R qK T₀K) :
    J10Blk_JT K σ y R := by
  choose j hjt htj using hev
  have hact : ∀ n, (K n).toHistory.activeStage (σ n) = (j n).castSucc := fun n =>
    activeStage_eq_of_mem_slab_HSX (K n) (j n) (σ n) (hjt n).le (htj n)
  let yG : ∀ n, ((K n).stage (j n).castSucc).Carrier := fun n =>
    cast (congrArg (fun m => ((K n).stage m).Carrier) (hact n)) (y n)
  have hyG : ∀ n, HEq (y n) (yG n) := fun n => (cast_heq _ _).symm
  let Hs : ℕ → ObservedHistory.{u} := fun n =>
    ((K n).eventPrefix (j n) (σ n) (hjt n) (htj n)).toHistory
  let ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon := fun n =>
    ((K n).prefixAt (j n).castSucc).extendAtTime ((K n).prefixAt_time_last _)
      ((K n).toHistory.event (j n)).incoming ((K n).event_initial (j n)) (hjt n) (htj n)
  have hσ' : ∀ n, (ts n : ℝ) = σ n := fun _ => rfl
  have hidx : ∀ n, Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ (j n).castSucc.isLt))
      ((Hs n).activeStage (ts n)) = (K n).toHistory.activeStage (σ n) := fun n =>
    Fin.ext ((K n).eventPrefix_activeStage_val (j n) (hjt n) (htj n) (ts n) (σ n) (hσ' n))
  let ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier := fun n =>
    cast (congrArg (fun m => ((K n).stage m).Carrier) (hidx n)).symm (y n)
  have hysK : ∀ n, HEq (ys n) (y n) := fun n => cast_heq _ _
  have hys : ∀ n, HEq (ys n) (yG n) := fun n => (hysK n).trans (hyG n)
  have hHs' : ∀ n, Hs n = ((K n).eventPrefix (j n) (σ n) (hjt n) (htj n)).toHistory :=
    fun _ => rfl
  obtain ⟨Ctime_e, phi_e, hphi_e, D_e, θcap_e, qcan_e, T₀_e, p_e, pF_e, δb_e, records_e, recordsF_e,
    a₀_e, hHI_e, hcan_e, hδF_e, hqcan_e, hpar_e, hscale_e, hbirthA_e, hθcap_e, hpinch_e,
    hslab_e, hderG_e, hnot_e, hT₀_e, hRt_e, eps_e, C1'_e, C2'_e, Cg_e, Ctime'_e, Tn_e,
    aSeed_e, haT_e, hsT_e, has_e, pT_e, seedTrace_e, L_e, hL_e, hgood_e, hwin_e, r_e, hC2_e,
    hr_e, hsmall_e, hclock_e, a₀X_e, ha₀X_e, hpinX_e, hRa_e, hT₀X_e,
    hOldX_e, hDmX_e, hfinX_e, -⟩ := hJ j hjt htj yG hyG ys hys
  have hscalE := ObservedHistory.scal_of_extendAt_P6D2
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming) (s := fun n => (K n).time (j n).succ)
    (y := yG) (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hjt htj
    Hs ts ys (fun n => ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n)) rfl
    HEq.rfl hys (fun _ => rfl)
  have hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n) :=
    fun n => (hRdef n).trans ((ObservedHistory.scalar_eq_of_eventPrefix_P6JGH (K n) (j n) (hjt n)
      (htj n) (ts n) (σ n) (hσ' n) (ys n) (y n) (hysK n)).symm.trans (hscalE n))
  have hRlim : Tendsto R atTop atTop :=
    tendsto_atTop_mono hRr (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hsepT_b := ObservedHistory.hsepT_eventPrefix_of_drvSep_HSX hr_e
    K j (fun n => (σ n : ℝ)) hjt htj σ R (hRlim.eventually_ge_atTop 1) ts hσ' recK hsep
  exact ObservedHistory.drvSlots_K_of_J10_sepT_HSX
    (H := fun n => (K n).prefixAt (j n).castSucc)
    (G := fun n => ((K n).toHistory.event (j n)).incoming) (s := fun n => (K n).time (j n).succ)
    (t := fun n => (σ n : ℝ)) (y := yG)
    (Ctime := Ctime_e) (phi := phi_e) (hphi := hphi_e) (D := D_e) (θcap := θcap_e) (qcan := qcan_e)
    (T₀ := T₀_e) (p := p_e) (pF := pF_e) (δb := δb_e) (records := records_e)
    (recordsF := recordsF_e) (a₀ := a₀_e) (hHI := hHI_e) (hcan := hcan_e) (hδF := hδF_e)
    (hqcan := hqcan_e) (hpar := hpar_e) (hscale := hscale_e) (hbirthA := hbirthA_e)
    (hθcap := hθcap_e) (hpinch := hpinch_e) (hslab := hslab_e) (hderG := hderG_e) (hnot := hnot_e)
    (hT₀ := hT₀_e) (hRt := hRt_e) (eps := eps_e) (C1' := C1'_e) (C2' := C2'_e) (Cg := Cg_e)
    (Ctime' := Ctime'_e) (Tn := Tn_e) (aSeed := aSeed_e) (haT := haT_e) (hsT := hsT_e)
    (has := has_e) (pT := pT_e) (seedTrace := seedTrace_e) (L := L_e) (hL := hL_e)
    (hgood := hgood_e) (hwin := hwin_e) (r := r_e) (hC2 := hC2_e) (hr := hr_e) (hsmall := hsmall_e)
    (hclock := hclock_e) (a₀X := a₀X_e) (ha₀X := ha₀X_e) (hpinX := hpinX_e) (hRa := hRa_e)
    (qX := qK) (T₀X := T₀K) (hT₀X := hT₀X_e)
    (recordsX := fun n => (K n).eventPrefixRecords_C11G2 (j n) (hjt n) (htj n) (recK n))
    (hOldX := hOldX_e)
    (hcanX := fun n => (K n).eventPrefixRecords_hcan_C11G2 (j n) (hjt n) (htj n) (recK n) (hcanK n))
    (hDmX := hDmX_e) (haccX := hacc) (hmX := fun n => (Nat.le_add_left 2 n).trans (hord n))
    (hsepT := hsepT_b)
    (hfinX := hfinX_e)
    (fun n => (K n).prefixAt_time_last _) (fun n => (K n).event_initial (j n)) hjt htj
    Hs ts ys R rfl HEq.rfl hys hRn hRpos hRlim
    K j (fun n => (σ n : ℝ)) hjt htj hHs' σ y hσ' hysK

/-- **J10 块 ⇐ 尾平移（`_JT`，PROVED）**：`j10ResE_of_2_JP` 前提（原族）+ DrvResE 合取 1 + `hev` +
`J10ResE3_JT` + `0 < a₀K` + `∀ᶠ hT₀X` ⇒ `J10Blk_JT`。取 `N = N₀ + N₁`（`N₀ > transitionEnd + 10`、
`∀ n ≥ N₁` 有 `hT₀X`），平移族上 `j10ResE_of_2_JP` + `j10Blk_of_J10ResE_JT`，再 `j10Blk_of_shift_JT`。 -/
theorem j10Blk_of_tail_JT {K : ℕ → RetainedCoreHistory.{u}}
    {σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {yK : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R : ℕ → ℝ}
    {Ctime : ℝ≥0} {ε C1 C2 Cg : ℝ} (hC2 : 0 ≤ C2)
    {qK : ℕ → CutoffParameters} {T₀K : ℕ → ℝ}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (qK n)}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (qK n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (qK n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (qK n).modelOrder)
    (hT₀K : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - T / R n)
    {pF : ℕ → CutoffParameters}
    (recordsFK : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    (hδFK : ∀ n (i : Fin (K n).eventCount), T₀K n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Q a₀K : ℕ → ℝ}
    (hHIK : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀K n) x ∧
      -3 / a₀K n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthAK : ∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀K n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀K n)) phi)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (hslabT : ∀ n (i : Fin (K n).eventCount),
      ((K n).toHistory.event i).incoming.DerivativeBoundBefore Ctime (Q n)
        (min ((K n).time i.succ) (Tn n : ℝ)))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - 1 ^ 2) (h1 : ∀ n, 1 ≤ (aSeed n : ℝ))
    (hsm : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) 1)
    (hhalf : ∀ n, (Tn n : ℝ) - 1 ^ 2 / 2 ≤ σ n)
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (hgoodK : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v)
      (hvs : v ≤ σ n), (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (yK n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) z
          →
        (K n).toHistory.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z)
    (hRdef : ∀ n, R n = metricScalarAt ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (yK n))
    (hRpos : ∀ n, 0 < R n) (hRr : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hfinK : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (yK n) ≠ ⊤)
    (hsep : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀K n ≤ (K n).time i.succ) b,
        (σ n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale)
    (hev : ∀ n, ∃ j : Fin (K n).eventCount, (K n).time j.castSucc < (σ n : ℝ) ∧
      (σ n : ℝ) < (K n).time j.succ)
    (ha₀ : ∀ n, 0 < a₀K n) (hT₀X : ∀ᶠ n in atTop, T₀K n ≤ (σ n : ℝ) - (1 / 100 : ℝ) ^ 2)
    (h3 : J10ResE3_JT K σ yK qK T₀K recordsK) :
    J10Blk_JT K σ yK R := by
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hT₀X
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (StandardCap.transitionEnd + 10)
  have hNd : StandardCap.transitionEnd + 10 < ((N₀ + N₁ : ℕ) : ℝ) := by
    have : (N₀ : ℝ) ≤ ((N₀ + N₁ : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right N₀ N₁
    linarith
  have hJ2 := j10ResE2_shift_of_3_JT (a₀K := a₀K) (N₀ + N₁) hNd hrad ha₀
    (fun n => hN₁ (n + (N₀ + N₁)) (by omega)) h3
  have hJ := j10ResE_of_2_JP (K := fun n => K (n + (N₀ + N₁)))
    (σ := fun n => σ (n + (N₀ + N₁))) (yK := fun n => yK (n + (N₀ + N₁)))
    (R := fun n => R (n + (N₀ + N₁))) (Ctime := Ctime) (ε := ε) (C1 := C1) (C2 := C2) (Cg := Cg)
    hC2 (qK := fun n => qK (n + (N₀ + N₁))) (T₀K := fun n => T₀K (n + (N₀ + N₁)))
    (recordsK := fun n => recordsK (n + (N₀ + N₁)))
    (fun n => hcanK (n + (N₀ + N₁)))
    (fun n => (hacc (n + (N₀ + N₁))).trans (shiftInv_JT n (N₀ + N₁)))
    (fun n => (shiftLe_JT n (N₀ + N₁)).trans (hrad (n + (N₀ + N₁))))
    (fun n => le_trans (by omega) (hord (n + (N₀ + N₁))))
    (fun T hT => eventually_add_JT (N₀ + N₁) (hT₀K T hT))
    (pF := fun n => pF (n + (N₀ + N₁))) (fun n => recordsFK (n + (N₀ + N₁)))
    (fun n i hi => (hδFK (n + (N₀ + N₁)) i hi).trans (shiftInv_JT n (N₀ + N₁)))
    hphi (Q := fun n => Q (n + (N₀ + N₁))) (a₀K := fun n => a₀K (n + (N₀ + N₁)))
    (fun n => hHIK (n + (N₀ + N₁)))
    (fun n i hi b => (shiftScale_JT n (N₀ + N₁) (Q (n + (N₀ + N₁)))).trans
      (hscaleK (n + (N₀ + N₁)) i hi b))
    (eventually_add_JT (N₀ + N₁) hbirthAK) (fun n => hpinchK (n + (N₀ + N₁)))
    (fun n => Tn (n + (N₀ + N₁))) (fun n => aSeed (n + (N₀ + N₁))) (fun n => haT (n + (N₀ + N₁)))
    (fun n => hsT (n + (N₀ + N₁))) (fun n => has (n + (N₀ + N₁))) (fun n => pT (n + (N₀ + N₁)))
    (fun n => seedTrace (n + (N₀ + N₁))) (fun n => hslabT (n + (N₀ + N₁)))
    (fun n => hclock (n + (N₀ + N₁))) (fun n => h1 (n + (N₀ + N₁)))
    (fun n => hsm (n + (N₀ + N₁))) (fun n => hhalf (n + (N₀ + N₁)))
    (L := fun n => L (n + (N₀ + N₁))) (hL.comp (tendsto_add_atTop_nat (N₀ + N₁)))
    (fun n => hgoodK (n + (N₀ + N₁))) (fun n => hRdef (n + (N₀ + N₁)))
    (fun n => hRpos (n + (N₀ + N₁)))
    (fun n => (shiftLe_JT n (N₀ + N₁)).trans (hRr (n + (N₀ + N₁))))
    (fun n => hfinK (n + (N₀ + N₁))) hJ2
  exact j10Blk_of_shift_JT (N₀ + N₁) (j10Blk_of_J10ResE_JT (fun n => recordsK (n + (N₀ + N₁)))
    (fun T hT C hC => eventually_add_JT (N₀ + N₁) (hsep T hT C hC))
    (fun n => hcanK (n + (N₀ + N₁)))
    (fun n => (hacc (n + (N₀ + N₁))).trans (shiftInv_JT n (N₀ + N₁)))
    (fun n => le_trans (by omega) (hord (n + (N₀ + N₁))))
    (fun n => hRdef (n + (N₀ + N₁))) (fun n => hRpos (n + (N₀ + N₁)))
    (fun n => (shiftLe_JT n (N₀ + N₁)).trans (hRr (n + (N₀ + N₁))))
    (fun n => hev (n + (N₀ + N₁))) hJ)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
