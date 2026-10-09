import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedCenterProducerC11PT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6PickedBallKappaC11PK

/-!
# driver 中心 Step 1 / 中心邻域合同 ⇐ hgood + hdistQC + FRESH 中心 κ（O-CH11-PICKSEL G1，后缀 `_P6PS`）

(docstring 待写)
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

section Vacuous

/-- **中心邻域合同的退化情形（`_P6PS`，PROVED）**：`Dc ≤ 0` 时区域球 `B_v(tr x₁, Dc/√Rn)` 空，合同平凡成立
（family producer 对 `Dd + Rad ≤ 0` 的分支用；`pickedCenterNeighborhood_zero_C11PT` 的 `Dc ≤ 0` 推广）。 -/
theorem pickedCenterNeighborhood_of_nonpos_P6PS {Dw Dc Tc θ Rn qthr ρ κ ε C1 C2 : ℝ}
    {Cgrad : ℝ≥0} (K : RetainedCoreHistory.{u}) (σ' : Icc (0 : ℝ) K.toHistory.horizon)
    (y' : (K.toHistory.stageAt σ').Carrier) (hDc : Dc ≤ 0) :
    PickedCenterNeighborhood_C11PT Dw Dc Tc θ Rn qthr ρ κ ε C1 C2 Cgrad K σ' y' := by
  intro j' v _ _ _ _ x₁ _ hjσ tr x hx
  exfalso
  have hx' : riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) x < ENNReal.ofReal (Dc / Real.sqrt Rn) := hx
  rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hDc (Real.sqrt_nonneg _))] at hx'
  exact ENNReal.not_lt_zero hx'

/-- **slab 内 scalar 的 `HEq` 搬运（`_P6PS`，PROVED）**：`τ` 在 event `j′` 的 slab 内、`z ∈ stageAt τ` 与
`x ∈ stage j′⁻` 为 `HEq` ⇒ `stageMetric` 上 `z` 处的下界搬到 `K.event j′` incoming flow 的 `scalar τ x`。 -/
theorem scalar_le_of_heq_P6PS (K : RetainedCoreHistory.{u}) (j' : Fin K.eventCount)
    (τ : Icc (0 : ℝ) K.toHistory.horizon) (hτ1 : K.time j'.castSucc < τ)
    (hτ2 : (τ : ℝ) < K.time j'.succ) (z : (K.toHistory.stageAt τ).Carrier)
    (x : (K.stage j'.castSucc).Carrier) (hzx : HEq z x) {c : ℝ}
    (hc : c ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) z) :
    c ≤ (K.toHistory.event j').incoming.flow.scalar τ x := by
  have hact := K.activeStage_eq_castSucc_C11PB j' τ hτ1 hτ2
  have key : ∀ (k : Fin (K.toHistory.eventCount + 1)) (_hk : K.toHistory.activeStage τ = k)
      (x' : (K.toHistory.stage k).Carrier), HEq z x' →
      metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) z =
        metricScalarAt (K.toHistory.stageMetric k τ) x' := by
    intro k hk
    subst hk
    intro x' h
    rw [eq_of_heq h]
  rw [key j'.castSucc hact x hzx, ObservedHistory.stageMetric_castSucc_apply] at hc
  exact hc

end Vacuous

section PerCenter

variable {K : ℕ → RetainedCoreHistory.{u}}
  {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
  {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
  {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
  {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
    ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
  {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
  {Ctime : ℝ≥0} {Cg : ℝ}

/-- **slice 时刻中心区域点的 seed 距离（`_P6PS`，PROVED：hdistQC + 三角不等式）**：`hdl`（T1 壳的 `hdl` /
`hdistQC` 在固定 `n` 处的体，traced 点余量 `L/4`，时间 `σ − Tc/R_n ≤ v`）+ `x ∈ B_v(tr x₁, Dc/√R_n)`
⇒ `d_v(O, x) ≤ dσ + (L/4 + Dc)/√R_n`（`O` = seed 在 stage `j′⁻` 的位置；`v` 在 event `j′` 的 slab 内，
`activeStage v = j′⁻`）。只在 slice 时刻 `v`，无窗口、无曲率阈值。 -/
theorem seedDist_slice_P6PS (n : ℕ) {Dw Dc Tc : ℝ} (hRn : 0 < R n) (hL0 : 0 ≤ L n)
    (hDc : 0 ≤ Dc)
    (hdl : ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - Tc / R n ≤ v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              ((seedTrace n).point ((K n).toHistory.activeStage v)
                  ((K n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvs)) ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
                (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (haS : (aSeed n : ℝ) ≤ (σ n : ℝ) - Tc / R n)
    (j' : Fin (K n).eventCount) (v : ℝ) (hv1 : (K n).time j'.castSucc < v)
    (hv2 : v < (K n).time j'.succ) (hvT : (σ n : ℝ) - Tc / R n ≤ v) (hvσ : v ≤ σ n)
    (x₁ : ((K n).toHistory.stage ((K n).toHistory.activeStage (σ n))).Carrier)
    (hx₁ : x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
      (σ n)) (y n) (Dw / Real.sqrt (R n)))
    (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
    (tr : BackwardPointTrace (K n).toHistory j'.castSucc ((K n).toHistory.activeStage (σ n)) hjσ
      x₁)
    (x : ((K n).stage j'.castSucc).Carrier)
    (hx : x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt (R n)))
    (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
    (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)) :
    riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
        ((seedTrace n).point j'.castSucc h1 h2) x ≤
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n / 4 + Dc) / Real.sqrt (R n)) := by
  have hvh : v ≤ (K n).toHistory.horizon := hvσ.trans (σ n).2.2
  let vI : Icc (0 : ℝ) (K n).toHistory.horizon :=
    ⟨v, ((K n).toHistory.time_nonneg _).trans hv1.le, hvh⟩
  have hact : (K n).toHistory.activeStage vI = j'.castSucc :=
    (K n).activeStage_eq_castSucc_C11PB j' vI hv1 hv2
  have hav : aSeed n ≤ vI := by
    change (aSeed n : ℝ) ≤ v
    linarith
  have hvs : vI ≤ σ n := by
    change v ≤ (σ n : ℝ)
    exact hvσ
  have key : ∀ (k : Fin ((K n).toHistory.eventCount + 1))
      (_hk : (K n).toHistory.activeStage vI = k) (hkσ : k ≤ (K n).toHistory.activeStage (σ n))
      (tr' : BackwardPointTrace (K n).toHistory k ((K n).toHistory.activeStage (σ n)) hkσ x₁)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n)),
      riemannianEDistOf ((K n).toHistory.stageMetric k vI) ((seedTrace n).point k h1' h2')
          (tr'.point k le_rfl hkσ) ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / 4 / Real.sqrt (R n)) := by
    intro k hk
    subst hk
    intro hkσ tr' h1' h2'
    exact hdl x₁ hx₁ vI hav hvs hvT tr'
  have htr := key j'.castSucc hact hjσ tr h1 h2
  rw [ObservedHistory.stageMetric_castSucc_apply] at htr
  have hs : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have ha0 : 0 ≤ L n / 4 / Real.sqrt (R n) := div_nonneg (div_nonneg hL0 (by norm_num)) hs.le
  have hb0 : 0 ≤ Dc / Real.sqrt (R n) := div_nonneg hDc hs.le
  calc riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
        ((seedTrace n).point j'.castSucc h1 h2) x
      ≤ riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
          ((seedTrace n).point j'.castSucc h1 h2) (tr.point j'.castSucc le_rfl hjσ) +
        riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
          (tr.point j'.castSucc le_rfl hjσ) x := riemannianEDistOf_triangle _ _ _ _
    _ ≤ (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) +
        ENNReal.ofReal (Dc / Real.sqrt (R n)) := add_le_add htr hx.le
    _ = riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal ((L n / 4 + Dc) / Real.sqrt (R n)) := by
        rw [add_assoc, ← ENNReal.ofReal_add ha0 hb0, ← add_div]

/-- **hgood ⇒ witness（stage `j′⁻` 形，`_P6PS`，PROVED）**：`τ` 在 event `j′` 的 slab 内、hgood 的时间域内，
`d_τ(O, x) ≤ dσ + L/√R_n`、`Cg·R_n ≤ R(τ, x)` ⇒ `K.event j′` incoming metric 上 `x` 处
spatial canonical witness（neck chart）。= PICKBALL `pickedBallWitness_of_hgood_C11PB` 的点形（去掉球）。 -/
theorem witness_of_seedDist_P6PS
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctime)
    (n : ℕ) (j' : Fin (K n).eventCount) (τ : Icc (0 : ℝ) (K n).toHistory.horizon)
    (hτ1 : (K n).time j'.castSucc < τ) (hτ2 : (τ : ℝ) < (K n).time j'.succ)
    (hav : aSeed n ≤ τ) (hvs : τ ≤ σ n) (hvL : (σ n : ℝ) - L n ^ 2 / R n ≤ (τ : ℝ))
    (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
    (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)) (x : ((K n).stage j'.castSucc).Carrier)
    (hd : riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric τ)
        ((seedTrace n).point j'.castSucc h1 h2) x ≤
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hR : Cg * R n ≤ ((K n).toHistory.event j').incoming.flow.scalar τ x) :
    ∃ W : SpatialCanonicalWitness (((K n).toHistory.event j').incoming.flow.base.metric τ)
      eps C1 C2 x, W.capTubeHasNeckChart eps := by
  have hact := (K n).activeStage_eq_castSucc_C11PB j' τ hτ1 hτ2
  have key : ∀ (k : Fin ((K n).toHistory.eventCount + 1))
      (_hk : (K n).toHistory.activeStage τ = k)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n)) (x' : ((K n).toHistory.stage k).Carrier),
      riemannianEDistOf ((K n).toHistory.stageMetric k τ) ((seedTrace n).point k h1' h2') x' ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) →
      Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric k τ) x' →
      ∃ W : SpatialCanonicalWitness ((K n).toHistory.stageMetric k τ) eps C1 C2 x',
        W.capTubeHasNeckChart eps := by
    intro k hk
    subst hk
    intro h1' h2' x' hd' hR'
    exact (hgood n τ hav hvs hvL x' hd' hR').1
  have hd' : riemannianEDistOf ((K n).toHistory.stageMetric j'.castSucc τ)
      ((seedTrace n).point j'.castSucc h1 h2) x ≤
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hd
  have hR' : Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric j'.castSucc τ) x := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hR
  have hres := key j'.castSucc hact h1 h2 x hd' hR'
  rw [ObservedHistory.stageMetric_castSucc_apply] at hres
  exact hres

/-- **hgood ⇒ `HasSpatialCanonicalTimeControl`（`stageAt` 形，`_P6PS`，PROVED）**：同上前提，`z ∈ stageAt τ`
与 `x` 为 `HEq`、`Cg·R_n ≤ R(τ, z)` ⇒ `HasSpatialCanonicalTimeControl eps C1 C2 Ctime τ z`
（Step 1 合同的点形）。 -/
theorem hasSCTC_of_seedDist_P6PS
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctime)
    (n : ℕ) (j' : Fin (K n).eventCount) (τ : Icc (0 : ℝ) (K n).toHistory.horizon)
    (hτ1 : (K n).time j'.castSucc < τ) (hτ2 : (τ : ℝ) < (K n).time j'.succ)
    (hav : aSeed n ≤ τ) (hvs : τ ≤ σ n) (hvL : (σ n : ℝ) - L n ^ 2 / R n ≤ (τ : ℝ))
    (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
    (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)) (x : ((K n).stage j'.castSucc).Carrier)
    (hd : riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric τ)
        ((seedTrace n).point j'.castSucc h1 h2) x ≤
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)))
    (z : ((K n).toHistory.stageAt τ).Carrier) (hzx : HEq z x)
    (hR : Cg * R n ≤
      metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ) z) :
    (K n).toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ctime τ z := by
  have hact := (K n).activeStage_eq_castSucc_C11PB j' τ hτ1 hτ2
  have key : ∀ (k : Fin ((K n).toHistory.eventCount + 1))
      (_hk : (K n).toHistory.activeStage τ = k)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n)) (x' : ((K n).toHistory.stage k).Carrier),
      HEq z x' →
      riemannianEDistOf ((K n).toHistory.stageMetric k τ) ((seedTrace n).point k h1' h2') x' ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) →
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
          ((seedTrace n).point ((K n).toHistory.activeStage τ)
            ((K n).toHistory.activeStage_mono hav)
            ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    intro k hk
    subst hk
    intro h1' h2' x' hzx' hd'
    rw [eq_of_heq hzx']
    exact hd'
  have hd' : riemannianEDistOf ((K n).toHistory.stageMetric j'.castSucc τ)
      ((seedTrace n).point j'.castSucc h1 h2) x ≤
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hd
  exact hgood n τ hav hvs hvL z (key j'.castSucc hact h1 h2 x hzx hd') hR

/-- **G1 主定理之一：driver 中心 12.1 Step 1 合同 ⇐ hgood + hdistQC + 窗口 seed closure（`_P6PS`）**。
`PickedCenterStepOne_C11PT` 逐字（`K n`、`σ n`、`y n`、`Rn := R n`）。证明按窗口时刻 `v′` 分两支：
* `v′ = v`（**slice 部分，PROVED，无 binder**）：`seedDist_slice_P6PS`（`hdl` 的 `L/4` 余量 + 三角不等式，
  `4·Dc ≤ 3L`）把 `x` 放进 hgood 的 seed 域 `dσ + L/√R_n`，`Λ ≥ Cg` 给阈值，hgood 给
  `HasSpatialCanonicalTimeControl`；
* `v′ < v`（**窗口部分**）：只经 `PickedCenterWindowSeed_C11PT`（显式 binder `hWS`，`O` = seed 在 stage
  `j′⁻` 的位置 `hO`，`D = dσ + L/√R_n`，`qthr < Λ·R_n`）。
时间域：`aSeed ≤ σ − (Tc + θ)/R_n`、`Tc + θ ≤ L²`（hgood 的 `[σ − L²/R_n, σ]`）。**不用** hpick /
`PickedBallTop_C11PB`、hUVC 的 M4 链、hclosG、hscalU、hstop。 -/
theorem pickedCenterStepOne_of_hgood_P6PS
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctime)
    (n : ℕ) {Dw Dc Tc θ Λ qthr : ℝ} (hRn : 0 < R n) (hDc : 0 ≤ Dc) (hDcL : 4 * Dc ≤ 3 * L n)
    (hθ : 0 ≤ θ) (hTL : Tc + θ ≤ L n ^ 2) (haS : (aSeed n : ℝ) ≤ (σ n : ℝ) - (Tc + θ) / R n)
    (hΛ : Cg ≤ Λ) (hqΛ : qthr < Λ * R n)
    (hdl : ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - Tc / R n ≤ v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              ((seedTrace n).point ((K n).toHistory.activeStage v)
                  ((K n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvs)) ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
                (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (O : ∀ j' : Fin (K n).eventCount, ((K n).stage j'.castSucc).Carrier)
    (hO : ∀ (j' : Fin (K n).eventCount)
      (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      O j' = (seedTrace n).point j'.castSucc h1 h2)
    (hWS : PickedCenterWindowSeed_C11PT Dw Dc Tc θ (R n) qthr (K n) (σ n) (y n) O
      (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
           (σ n))
         ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
           ((K n).toHistory.activeStage_mono (has n))
           ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)))) :
    PickedCenterStepOne_C11PT Dw Dc Tc θ (R n) Λ eps C1 C2 Ctime (K n) (σ n) (y n) := by
  intro j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx v' hv'θ hv'v hv'1 z hzx hRz
  have hL0 : 0 ≤ L n := by linarith
  have hs : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hTR : Tc / R n ≤ (Tc + θ) / R n := div_le_div_of_nonneg_right (by linarith) hRn.le
  have hθR : (Tc + θ) / R n = Tc / R n + θ / R n := add_div _ _ _
  have hLR : (Tc + θ) / R n ≤ L n ^ 2 / R n := div_le_div_of_nonneg_right hTL hRn.le
  have hv'2 : (v' : ℝ) < (K n).time j'.succ := lt_of_le_of_lt hv'v hv2
  have hact := (K n).activeStage_eq_castSucc_C11PB j' v' hv'1 hv'2
  have hav' : aSeed n ≤ v' := by
    change (aSeed n : ℝ) ≤ v'
    linarith
  have hvs' : v' ≤ σ n := by
    change (v' : ℝ) ≤ σ n
    linarith
  have hvL' : (σ n : ℝ) - L n ^ 2 / R n ≤ (v' : ℝ) := by linarith
  have h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc := by
    rw [← hact]
    exact (K n).toHistory.activeStage_mono hav'
  have h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n) := by
    rw [← hact]
    exact (K n).toHistory.activeStage_mono (hvs'.trans (hsT n))
  have hRz' : Cg * R n ≤
      metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v') v') z :=
    (mul_le_mul_of_nonneg_right hΛ hRn.le).trans hRz
  have hd : riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v')
      ((seedTrace n).point j'.castSucc h1 h2) x ≤
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    rcases eq_or_lt_of_le hv'v with heq | hlt
    · rw [heq]
      exact (seedDist_slice_P6PS (haT := haT) (hsT := hsT) (has := has) n hRn hL0 hDc hdl
        (by linarith) j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx h1 h2).trans
          (add_le_add le_rfl (ENNReal.ofReal_le_ofReal
            (div_le_div_of_nonneg_right (by linarith) hs.le)))
    · have hq : qthr < ((K n).toHistory.event j').incoming.flow.scalar v' x :=
        hqΛ.trans_le (scalar_le_of_heq_P6PS (K n) j' v' hv'1 hv'2 z x hzx hRz)
      have h := hWS j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx v' ⟨hv'1, hlt⟩ hv'θ hq
      rwa [hO j' h1 h2] at h
  exact hasSCTC_of_seedDist_P6PS hgood n j' v' hv'1 hv'2 hav' hvs' hvL' h1 h2 x hd z hzx hRz'

/-- **slice 部分单独陈述（`_P6PS`，PROVED，无任何 binder）**：Step 1 合同在 `v′ = v` 处的体（窗口退化为
slice 时刻）⇐ hgood + `hdl` + 三角不等式。即 PICKT1 G2 §1 所说"slice 时刻 `P_n ⊆` Good 域"的可证接线。 -/
theorem pickedCenterStepOne_slice_of_hgood_P6PS
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctime)
    (n : ℕ) {Dw Dc Tc Λ : ℝ} (hRn : 0 < R n) (hDc : 0 ≤ Dc) (hDcL : 4 * Dc ≤ 3 * L n)
    (hTL : Tc ≤ L n ^ 2) (haS : (aSeed n : ℝ) ≤ (σ n : ℝ) - Tc / R n) (hΛ : Cg ≤ Λ)
    (hdl : ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - Tc / R n ≤ v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              ((seedTrace n).point ((K n).toHistory.activeStage v)
                  ((K n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvs)) ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
                (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (j' : Fin (K n).eventCount) (v : ℝ) (hv1 : (K n).time j'.castSucc < v)
    (hv2 : v < (K n).time j'.succ) (hvT : (σ n : ℝ) - Tc / R n ≤ v) (hvσ : v ≤ σ n)
    (x₁ : ((K n).toHistory.stage ((K n).toHistory.activeStage (σ n))).Carrier)
    (hx₁ : x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
      (σ n)) (y n) (Dw / Real.sqrt (R n)))
    (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
    (tr : BackwardPointTrace (K n).toHistory j'.castSucc ((K n).toHistory.activeStage (σ n)) hjσ
      x₁)
    (x : ((K n).stage j'.castSucc).Carrier)
    (hx : x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt (R n)))
    (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
    (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n))
    (v' : Icc (0 : ℝ) (K n).toHistory.horizon) (hv'v : (v' : ℝ) = v)
    (z : ((K n).toHistory.stageAt v').Carrier) (hzx : HEq z x)
    (hRz : Λ * R n ≤
      metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v') v') z) :
    (K n).toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v' z := by
  have hL0 : 0 ≤ L n := by linarith
  have hs : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hLR : Tc / R n ≤ L n ^ 2 / R n := div_le_div_of_nonneg_right hTL hRn.le
  have hv'1 : (K n).time j'.castSucc < v' := by rw [hv'v]; exact hv1
  have hv'2 : (v' : ℝ) < (K n).time j'.succ := by rw [hv'v]; exact hv2
  have hav' : aSeed n ≤ v' := by
    change (aSeed n : ℝ) ≤ v'
    linarith
  have hvs' : v' ≤ σ n := by
    change (v' : ℝ) ≤ σ n
    linarith
  have hvL' : (σ n : ℝ) - L n ^ 2 / R n ≤ (v' : ℝ) := by linarith
  have hd : riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v')
      ((seedTrace n).point j'.castSucc h1 h2) x ≤
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    rw [hv'v]
    exact (seedDist_slice_P6PS (haT := haT) (hsT := hsT) (has := has) n hRn hL0 hDc hdl haS
      j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx h1 h2).trans
        (add_le_add le_rfl (ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (by linarith) hs.le)))
  exact hasSCTC_of_seedDist_P6PS hgood n j' v' hv'1 hv'2 hav' hvs' hvL' h1 h2 x hd z hzx
    ((mul_le_mul_of_nonneg_right hΛ hRn.le).trans hRz)

/-- **中心 footprint（`_P6PS`，PROVED；输入 = top gate `hdσ` + 端点 Ricci 点形 `hRic`）**：中心区域点 `x`、
窗口时刻 `τ ∈ [v − θ/R_n, v]`、`time j′⁻ < τ` ⇒ `d_τ(O, x) < A·r`（宏观 footprint，κ 只要这个）。
`d_τ ≤ d_v + (8/ℓ)(v − τ)`（I.8.3(b)，`smooth_distance_distortion_C11D`，stage `j′⁻`）、
`d_v(O, x) ≤ dσ + (L/4 + Dc)/√R_n`（`seedDist_slice_P6PS`）、`(8/ℓ)(v − τ) ≤ (8θ/(ℓ√R_n))/√R_n`；
门槛 `4(Dc + 8θ/(ℓ√R_n)) ≤ 3L` ⇒ 和 `≤ dσ + L/√R_n < dσ + (L + 1)/√R_n ≤ A·r`
（`hdσ` = J11 / PBKAPPA 同式）。
**`ℓ` 自由**：取 `ℓ ~ 1/(L√R_n)` 时 `hRic` 只要 `Ric ≲ L²·R_n`（见文件头 §3）。 -/
theorem pickedCenterFootprint_P6PS (n : ℕ) {Dw Dc Tc θ ℓ A r : ℝ} (hRn : 0 < R n)
    (hDc : 0 ≤ Dc) (hθ : 0 ≤ θ) (hℓ : 0 < ℓ)
    (hLR : 4 * (Dc + 8 * θ / (ℓ * Real.sqrt (R n))) ≤ 3 * L n)
    (hdσ : riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
      ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (A * r))
    (hdl : ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - Tc / R n ≤ v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              ((seedTrace n).point ((K n).toHistory.activeStage v)
                  ((K n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvs)) ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
                (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (haS : (aSeed n : ℝ) ≤ (σ n : ℝ) - Tc / R n)
    (j' : Fin (K n).eventCount) (v : ℝ) (hv1 : (K n).time j'.castSucc < v)
    (hv2 : v < (K n).time j'.succ) (hvT : (σ n : ℝ) - Tc / R n ≤ v) (hvσ : v ≤ σ n)
    (x₁ : ((K n).toHistory.stage ((K n).toHistory.activeStage (σ n))).Carrier)
    (hx₁ : x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
      (σ n)) (y n) (Dw / Real.sqrt (R n)))
    (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
    (tr : BackwardPointTrace (K n).toHistory j'.castSucc ((K n).toHistory.activeStage (σ n)) hjσ
      x₁)
    (x : ((K n).stage j'.castSucc).Carrier)
    (hx : x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt (R n)))
    (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
    (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n))
    (hRic : ∀ t : ℝ, v - θ / R n < t → t < v → (K n).time j'.castSucc < t →
      ∀ (yy : ((K n).stage j'.castSucc).Carrier) (ξ : TangentSpace ThreeModel yy),
        (riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric t)
            ((seedTrace n).point j'.castSucc h1 h2) yy < ENNReal.ofReal ℓ ∨
          riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric t) x yy <
            ENNReal.ofReal ℓ) →
        ricciTensor (((K n).toHistory.event j').incoming.flow.base.metric t) yy ξ ξ ≤
          (3 / ℓ ^ 2) * (((K n).toHistory.event j').incoming.flow.base.metric t).inner yy ξ ξ)
    (τ : ℝ) (hτ1 : v - θ / R n ≤ τ) (hτ2 : τ ≤ v) (hτ3 : (K n).time j'.castSucc < τ) :
    riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric τ)
        ((seedTrace n).point j'.castSucc h1 h2) x < ENNReal.ofReal (A * r) := by
  have hs : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hX0 : 0 ≤ 8 * θ / (ℓ * Real.sqrt (R n)) :=
    div_nonneg (by linarith) (mul_pos hℓ hs).le
  have hL0 : 0 ≤ L n := by linarith
  have hslice := seedDist_slice_P6PS (haT := haT) (hsT := hsT) (has := has) n hRn hL0 hDc hdl
    haS j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx h1 h2
  have hnext : ∀ e : Fin (K n).toHistory.eventCount, j'.castSucc = e.castSucc →
      v < (K n).toHistory.time e.succ := by
    intro e he
    obtain rfl := Fin.castSucc_injective _ he
    exact hv2
  have hhor : v ≤ (K n).toHistory.horizon := hvσ.trans (σ n).2.2
  have hRic' : ∀ t ∈ Ioo τ v, ∀ yy : ((K n).toHistory.stage j'.castSucc).Carrier,
      ∀ ξ : TangentSpace ThreeModel yy,
      (riemannianEDistOf ((K n).toHistory.stageMetric j'.castSucc t)
          ((seedTrace n).point j'.castSucc h1 h2) yy < ENNReal.ofReal ℓ ∨
        riemannianEDistOf ((K n).toHistory.stageMetric j'.castSucc t) x yy <
          ENNReal.ofReal ℓ) →
      ricciTensor ((K n).toHistory.stageMetric j'.castSucc t) yy ξ ξ ≤
        (3 / ℓ ^ 2) * ((K n).toHistory.stageMetric j'.castSucc t).inner yy ξ ξ := by
    intro t ht yy ξ hyy
    rw [ObservedHistory.stageMetric_castSucc_apply] at hyy ⊢
    exact hRic t (lt_of_le_of_lt hτ1 ht.1) ht.2 (lt_trans hτ3 ht.1) yy ξ hyy
  have hdist := ObservedHistory.smooth_distance_distortion_C11D (K n).toHistory j'.castSucc hℓ
    hτ2 hτ3.le hnext hhor ((seedTrace n).point j'.castSucc h1 h2) x hRic'
  rw [ObservedHistory.stageMetric_castSucc_apply,
    ObservedHistory.stageMetric_castSucc_apply] at hdist
  have hlen : 8 / ℓ * (v - τ) ≤ 8 * θ / (ℓ * Real.sqrt (R n)) / Real.sqrt (R n) := by
    have hsR : Real.sqrt (R n) * Real.sqrt (R n) = R n := Real.mul_self_sqrt hRn.le
    have hvτ : v - τ ≤ θ / R n := by linarith
    rw [div_div, mul_assoc, hsR]
    calc 8 / ℓ * (v - τ) ≤ 8 / ℓ * (θ / R n) :=
          mul_le_mul_of_nonneg_left hvτ (div_nonneg (by norm_num) hℓ.le)
      _ = 8 * θ / (ℓ * R n) := by ring
  have hfin : (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
                    (σ n))
                  ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                    ((K n).toHistory.activeStage_mono (has n))
                    ((K n).toHistory.activeStage_mono (hsT n))) (y n)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_self_add.trans hdσ)
  have ha0 : 0 ≤ (L n / 4 + Dc) / Real.sqrt (R n) := div_nonneg (by linarith) hs.le
  have hc0 : 0 ≤ 8 * θ / (ℓ * Real.sqrt (R n)) / Real.sqrt (R n) := div_nonneg hX0 hs.le
  have hsum : (L n / 4 + Dc) / Real.sqrt (R n) +
      8 * θ / (ℓ * Real.sqrt (R n)) / Real.sqrt (R n) < (L n + 1) / Real.sqrt (R n) := by
    rw [← add_div]
    exact div_lt_div_of_pos_right (by linarith) hs
  calc riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric τ)
        ((seedTrace n).point j'.castSucc h1 h2) x
      ≤ riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric v)
          ((seedTrace n).point j'.castSucc h1 h2) x + ENNReal.ofReal (8 / ℓ * (v - τ)) := hdist
    _ ≤ (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal ((L n / 4 + Dc) / Real.sqrt (R n))) +
        ENNReal.ofReal (8 * θ / (ℓ * Real.sqrt (R n)) / Real.sqrt (R n)) :=
        add_le_add hslice (ENNReal.ofReal_le_ofReal hlen)
    _ = riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal ((L n / 4 + Dc) / Real.sqrt (R n) +
            8 * θ / (ℓ * Real.sqrt (R n)) / Real.sqrt (R n)) := by
        rw [add_assoc, ← ENNReal.ofReal_add ha0 hc0]
    _ < riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
            (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) :=
        ENNReal.add_lt_add_left hfin
          ((ENNReal.ofReal_lt_ofReal_iff (div_pos (by linarith) hs)).2 hsum)
    _ ≤ ENNReal.ofReal (A * r) := hdσ

/-- **中心 κ 字段 ⇐ FRESH supply（原 seed，`_P6PS`，PROVED；输入 = `hdσ` + 端点 Ricci 点形）**：
`PickedCenterNeighborhood_C11PT` 第 (3) 项在固定 `(j′, v, x₁, tr, x)` 处的体。FRESH window-zero supply
`KappaSeedWindowFwd_C11PK`（PBKAPPA，producer `kappaSeedWindowFwd_of_retention_C11PK`）在**原 seed**
`(Tn, pT, r, aSeed, seedTrace)`（与 hgood 同一 prefix）上直接打中心球 × 窗：`τ ∈ [v − θ/R_n, v]` 落在
`[Tn − r²/2, Tn]`（`hwinF`）、`x` 的 footprint `< A·r`（`pickedCenterFootprint_P6PS`）、`b ≤ ρ < r/100`。
**不需 hpick / `PickedBallTop_C11PB`**（PBKAPPA 的 picked-ball 版需要，见 ANCHOR3 top 点循环）。 -/
theorem pickedCenterKappa_of_fresh_P6PS (n : ℕ) {Dw Dc Tc θ ρ κ ℓ A r Tκ : ℝ}
    {nr : ℝ → ℝ} (hRn : 0 < R n) (hDc : 0 ≤ Dc) (hθ : 0 ≤ θ) (hℓ : 0 < ℓ)
    (hLR : 4 * (Dc + 8 * θ / (ℓ * Real.sqrt (R n))) ≤ 3 * L n)
    (hdσ : riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
      ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (A * r))
    (hdl : ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - Tc / R n ≤ v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              ((seedTrace n).point ((K n).toHistory.activeStage v)
                  ((K n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvs)) ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
                (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (haS : (aSeed n : ℝ) ≤ (σ n : ℝ) - Tc / R n)
    (hW : KappaSeedWindowFwd_C11PK nr A κ Tκ (K n).toHistory) (hTκ : Tκ ≤ (Tn n : ℝ))
    (htime : 2 * r ^ 2 < (Tn n : ℝ))
    (hsmall : GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hvol : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnr : ∀ w : ℝ, (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r)
    (hclock : (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (hwinF : (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - (Tc + θ) / R n)
    (hρ : ρ < r / 100) (hκ : 0 ≤ κ)
    (j' : Fin (K n).eventCount) (v : ℝ) (hv1 : (K n).time j'.castSucc < v)
    (hv2 : v < (K n).time j'.succ) (hvT : (σ n : ℝ) - Tc / R n ≤ v) (hvσ : v ≤ σ n)
    (x₁ : ((K n).toHistory.stage ((K n).toHistory.activeStage (σ n))).Carrier)
    (hx₁ : x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
      (σ n)) (y n) (Dw / Real.sqrt (R n)))
    (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
    (tr : BackwardPointTrace (K n).toHistory j'.castSucc ((K n).toHistory.activeStage (σ n)) hjσ
      x₁)
    (x : ((K n).stage j'.castSucc).Carrier)
    (hx : x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt (R n)))
    (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
    (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n))
    (hRic : ∀ t : ℝ, v - θ / R n < t → t < v → (K n).time j'.castSucc < t →
      ∀ (yy : ((K n).stage j'.castSucc).Carrier) (ξ : TangentSpace ThreeModel yy),
        (riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric t)
            ((seedTrace n).point j'.castSucc h1 h2) yy < ENNReal.ofReal ℓ ∨
          riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric t) x yy <
            ENNReal.ofReal ℓ) →
        ricciTensor (((K n).toHistory.event j').incoming.flow.base.metric t) yy ξ ξ ≤
          (3 / ℓ ^ 2) * (((K n).toHistory.event j').incoming.flow.base.metric t).inner yy ξ ξ) :
    ∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon),
      v - θ / R n ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
      (K n).time j'.castSucc < τ → (τ : ℝ) < (K n).time j'.succ →
      ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz x →
      ∀ b : ℝ, 0 < b → b ≤ ρ → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
            (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
              zz b) := by
  intro τ hτ1 hτ2 hτ3 hτ4 zz hzz b hb hbρ hball
  have hr2 := sq_nonneg r
  have hθR : (Tc + θ) / R n = Tc / R n + θ / R n := add_div _ _ _
  have hσT : (σ n : ℝ) ≤ (Tn n : ℝ) := hsT n
  have hav : aSeed n ≤ τ := by
    change (aSeed n : ℝ) ≤ (τ : ℝ)
    linarith
  have hvt : τ ≤ Tn n := by
    change (τ : ℝ) ≤ (Tn n : ℝ)
    linarith
  have hact := (K n).activeStage_eq_castSucc_C11PB j' τ hτ3 hτ4
  have key : ∀ (k : Fin ((K n).toHistory.eventCount + 1))
      (_hk : (K n).toHistory.activeStage τ = k)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n))
      (z' : ((K n).toHistory.stage k).Carrier), HEq zz z' →
      riemannianEDistOf ((K n).toHistory.stageMetric k τ) ((seedTrace n).point k h1' h2') z' <
        ENNReal.ofReal (A * r) →
      zz ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
        ((seedTrace n).point ((K n).toHistory.activeStage τ)
          ((K n).toHistory.activeStage_mono hav) ((K n).toHistory.activeStage_mono hvt))
        (A * r) := by
    intro k hk
    subst hk
    intro h1' h2' z' hzz' hd'
    rw [eq_of_heq hzz']
    exact hd'
  have hd' : riemannianEDistOf ((K n).toHistory.stageMetric j'.castSucc τ)
      ((seedTrace n).point j'.castSucc h1 h2) x < ENNReal.ofReal (A * r) := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact pickedCenterFootprint_P6PS (haT := haT) (hsT := hsT) (has := has) n hRn hDc hθ hℓ hLR
      hdσ hdl (by linarith) j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx h1 h2 hRic τ hτ1 hτ2 hτ3
  have hx' := key j'.castSucc hact h1 h2 x hzz hd'
  have h := hW (Tn n) (pT n) r hTκ htime hsmall hvol hnr (aSeed n) (haT n) hclock (seedTrace n)
    τ hav hvt (by linarith) zz hx' b hb.le (by linarith) hball
  rw [ENNReal.ofReal_mul hκ, ENNReal.ofReal_pow hb.le] at h
  exact h

/-- **G1 主定理之二：中心邻域合同 ⇐ hgood + 窗口 seed closure + FRESH 中心 κ（`_P6PS`，
PROVISIONAL[`hWS` = `PickedCenterWindowSeed_C11PT`；`hRic` = 中心端点 Ricci，OPEN owner DIST]）**：
`PickedCenterNeighborhood_C11PT` 逐字。三项：
(1) witness（slice 时刻，`R > qthr ≥ Cg·R_n`）⇐ hgood + `hdl`（`seedDist_slice_P6PS`）——
**PROVED，无 binder**；
(2) 梯度（窗口 `v′ < v`）⇐ hgood + `hWS` + `C2 ≤ Cgrad`（witness 的 `gradient` 字段）；
(3) κ ⇐ FRESH supply（原 seed）+ top gate `hdσ`（J11 同式）+ 中心 footprint（`hdl` + I.8.3(b) + `hRic`）。
`hRic` 的 `ℓ` 自由（门槛 `hLR`）；`Λ`、hpick、`PickedBallTop_C11PB` 均不出现。 -/
theorem pickedCenterNeighborhood_of_hgood_fresh_P6PS
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctime)
    (n : ℕ) {Dw Dc Tc θ qthr ρ κ ℓ A r Tκ : ℝ} {nr : ℝ → ℝ} {Cgrad : ℝ≥0}
    (hRn : 0 < R n) (hDc : 0 ≤ Dc) (hθ : 0 ≤ θ) (hℓ : 0 < ℓ)
    (hLR : 4 * (Dc + 8 * θ / (ℓ * Real.sqrt (R n))) ≤ 3 * L n)
    (hTL : Tc + θ ≤ L n ^ 2) (haS : (aSeed n : ℝ) ≤ (σ n : ℝ) - (Tc + θ) / R n)
    (hq : Cg * R n ≤ qthr) (hC2 : C2 ≤ (Cgrad : ℝ))
    (hdl : ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
          (σ n : ℝ) - Tc / R n ≤ v →
        ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
            ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              ((seedTrace n).point ((K n).toHistory.activeStage v)
                  ((K n).toHistory.activeStage_mono hav)
                ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
              (tr.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvs)) ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
                (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n)))
    (O : ∀ j' : Fin (K n).eventCount, ((K n).stage j'.castSucc).Carrier)
    (hO : ∀ (j' : Fin (K n).eventCount)
      (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      O j' = (seedTrace n).point j'.castSucc h1 h2)
    (hWS : PickedCenterWindowSeed_C11PT Dw Dc Tc θ (R n) qthr (K n) (σ n) (y n) O
      (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
           (σ n))
         ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
           ((K n).toHistory.activeStage_mono (has n))
           ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal (L n / Real.sqrt (R n))))
    (hW : KappaSeedWindowFwd_C11PK nr A κ Tκ (K n).toHistory) (hTκ : Tκ ≤ (Tn n : ℝ))
    (htime : 2 * r ^ 2 < (Tn n : ℝ))
    (hsmall : GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hvol : ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnr : ∀ w : ℝ, (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r)
    (hclock : (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (hwinF : (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - (Tc + θ) / R n)
    (hρ : ρ < r / 100) (hκ : 0 ≤ κ)
    (hdσ : riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
      ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (A * r))
    (hRic : ∀ (j' : Fin (K n).eventCount) (v : ℝ), (K n).time j'.castSucc < v →
        v < (K n).time j'.succ → (σ n : ℝ) - Tc / R n ≤ v → v ≤ σ n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory j'.castSucc
          ((K n).toHistory.activeStage (σ n)) hjσ x₁),
      ∀ x ∈ riemannianBallOf (((K n).toHistory.event j').incoming.flow.base.metric v)
          (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt (R n)),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      ∀ t : ℝ, v - θ / R n < t → t < v → (K n).time j'.castSucc < t →
      ∀ (yy : ((K n).stage j'.castSucc).Carrier) (ξ : TangentSpace ThreeModel yy),
        (riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric t)
            ((seedTrace n).point j'.castSucc h1 h2) yy < ENNReal.ofReal ℓ ∨
          riemannianEDistOf (((K n).toHistory.event j').incoming.flow.base.metric t) x yy <
            ENNReal.ofReal ℓ) →
        ricciTensor (((K n).toHistory.event j').incoming.flow.base.metric t) yy ξ ξ ≤
          (3 / ℓ ^ 2) * (((K n).toHistory.event j').incoming.flow.base.metric t).inner yy ξ ξ) :
    PickedCenterNeighborhood_C11PT Dw Dc Tc θ (R n) qthr ρ κ eps C1 C2 Cgrad (K n) (σ n)
      (y n) := by
  intro j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx
  have hs : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hX0 : 0 ≤ 8 * θ / (ℓ * Real.sqrt (R n)) :=
    div_nonneg (by linarith) (mul_pos hℓ hs).le
  have hL0 : 0 ≤ L n := by linarith
  have hTR : Tc / R n ≤ (Tc + θ) / R n := div_le_div_of_nonneg_right (by linarith) hRn.le
  have hθR : (Tc + θ) / R n = Tc / R n + θ / R n := add_div _ _ _
  have hLR' : (Tc + θ) / R n ≤ L n ^ 2 / R n := div_le_div_of_nonneg_right hTL hRn.le
  have hvh : v ≤ (K n).toHistory.horizon := hvσ.trans (σ n).2.2
  let vI : Icc (0 : ℝ) (K n).toHistory.horizon :=
    ⟨v, ((K n).toHistory.time_nonneg _).trans hv1.le, hvh⟩
  have hact : (K n).toHistory.activeStage vI = j'.castSucc :=
    (K n).activeStage_eq_castSucc_C11PB j' vI hv1 hv2
  have hav : aSeed n ≤ vI := by
    change (aSeed n : ℝ) ≤ v
    linarith
  have hvs : vI ≤ σ n := by
    change v ≤ (σ n : ℝ)
    exact hvσ
  have h1 : (K n).toHistory.activeStage (aSeed n) ≤ j'.castSucc := by
    rw [← hact]
    exact (K n).toHistory.activeStage_mono hav
  have h2 : j'.castSucc ≤ (K n).toHistory.activeStage (Tn n) := by
    rw [← hact]
    exact (K n).toHistory.activeStage_mono (hvs.trans (hsT n))
  have hslice := seedDist_slice_P6PS (haT := haT) (hsT := hsT) (has := has) n hRn hL0 hDc hdl
    (by linarith) j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx h1 h2
  refine ⟨fun hqx => ?_, fun v' hv' hv'θ hqx ξ => ?_, ?_⟩
  · have hvL : (σ n : ℝ) - L n ^ 2 / R n ≤ (vI : ℝ) := by
      change (σ n : ℝ) - L n ^ 2 / R n ≤ v
      linarith
    exact witness_of_seedDist_P6PS hgood n j' vI hv1 hv2 hav hvs hvL h1 h2 x
      (hslice.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (by linarith) hs.le)))) (hq.trans hqx.le)
  · have hv'2 : v' < (K n).time j'.succ := hv'.2.trans hv2
    let τ : Icc (0 : ℝ) (K n).toHistory.horizon :=
      ⟨v', ((K n).toHistory.time_nonneg _).trans hv'.1.le,
        hv'2.le.trans ((K n).toHistory.time_le_horizon_at _)⟩
    have hav' : aSeed n ≤ τ := by
      change (aSeed n : ℝ) ≤ v'
      linarith
    have hvs' : τ ≤ σ n := by
      change v' ≤ (σ n : ℝ)
      linarith [hv'.2]
    have hvL' : (σ n : ℝ) - L n ^ 2 / R n ≤ (τ : ℝ) := by
      change (σ n : ℝ) - L n ^ 2 / R n ≤ v'
      linarith
    have hd := hWS j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx v' hv' hv'θ hqx
    rw [hO j' h1 h2] at hd
    obtain ⟨W, -⟩ := witness_of_seedDist_P6PS hgood n j' τ hv'.1 hv'2 hav' hvs' hvL' h1 h2 x hd
      (hq.trans hqx.le)
    have hR0 : 0 ≤ ((K n).toHistory.event j').incoming.flow.scalar v' x := W.Q_pos.le
    exact (W.gradient ξ).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC2 hR0) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
  · exact pickedCenterKappa_of_fresh_P6PS (haT := haT) (hsT := hsT) (has := has) n hRn hDc hθ hℓ
      hLR hdσ hdl (by linarith) hW hTκ htime hsmall hvol hnr hclock hwinF hρ hκ j' v hv1 hv2 hvT
      hvσ x₁ hx₁ hjσ tr x hx h1 h2
      (hRic j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx h1 h2)

end PerCenter

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
