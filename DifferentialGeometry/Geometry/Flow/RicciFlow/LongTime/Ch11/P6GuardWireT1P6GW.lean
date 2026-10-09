import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardWireKSWP6GW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ShallowPointPickC11PT

/-!
# GUARDWIRE G3b：PICKT1 中心邻域合同 (2)(3) 的 guarded 副本（O-CH11-GUARDWIRE，后缀 `_P6GW`）

* `PickedCenterNeighborhoodGuarded_P6GW`：PICKT1 合同逐字，(2) 梯度 / (3) κ 加 guard；弱化
  `PickedCenterNeighborhood_C11PT.guarded_P6GW`（旧 ⇒ 新）。
* `kswHUGuarded_of_pickedCenter_P6GW`：guarded 合同逐点付 guarded KSW `hU`（PROVED）。
* `ObservedHistory.hsliceR_lateHI_core_pickedCenter_guarded_P6GW`：T1 核心形，`hK` ⇐
`kswGuarded_P6GW`（无 binder），
  合同族换 guarded 形。结论 = PICKT1 `hsliceR_lateHI_core_pickedCenter_C11PT` 逐字。
**guarded 合同的 producer（PICKSEL neighborhood guarded 版）**：(1) witness ⇐ hgood + hdl（PICKSEL 已
PROVED）；
(2) 梯度 ⇐ hgood + WSBASE `pickedCenterWindowSeed_guardKX_C11WB`（guard 点 seed localization，PROVED，替
`hWS`）；
(3) κ ⇐ FRESH supply + `hdσ` + footprint `pickedCenterFootprint_twoScale_C11WB`（guard 后缀 ⊆ 点自身窗，替
`hRic`）。
见 state G3 段（DESIGN：PICKSEL 证明体改接点逐条列出）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

section GuardedPickT1

/-- **guarded 中心邻域合同（`_P6GW`）**：PICKT1 `PickedCenterNeighborhood_C11PT` 逐字，(2) 梯度 / (3) κ 的求值点
加 KSWEXIT guard `GuardKX_C11KX (R(v, ·)) qthr Ct v v′ x`（WSBASE G3 §2c）。(1) witness 不变。 -/
def PickedCenterNeighborhoodGuarded_P6GW (Dw Dc Tc θ Rn qthr ρ κ ε C1 C2 : ℝ) (Ct Cgrad : ℝ≥0)
    (K : RetainedCoreHistory.{u}) (σ : Icc (0 : ℝ) K.toHistory.horizon)
    (y : (K.toHistory.stageAt σ).Carrier) : Prop :=
  ∀ (j' : Fin K.eventCount) (v : ℝ), K.time j'.castSucc < v → v < K.time j'.succ →
    (σ : ℝ) - Tc / Rn ≤ v → v ≤ σ →
  ∀ x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
      (Dw / Real.sqrt Rn),
  ∀ (hjσ : j'.castSucc ≤ K.toHistory.activeStage σ)
    (tr : BackwardPointTrace K.toHistory j'.castSucc (K.toHistory.activeStage σ) hjσ x₁),
  ∀ x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) (Dc / Real.sqrt Rn),
    (qthr < (K.toHistory.event j').incoming.flow.scalar v x →
      ∃ W : SpatialCanonicalWitness ((K.toHistory.event j').incoming.flow.base.metric v)
        ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
    (∀ v' ∈ Ioo (K.time j'.castSucc) v, v - θ / Rn ≤ v' →
      qthr < (K.toHistory.event j').incoming.flow.scalar v' x →
      GuardKX_C11KX ((K.toHistory.event j').incoming.flow.scalar v) qthr Ct v v' x →
      ∀ ξ : TangentSpace ThreeModel x,
        |scalarDifferential (K.toHistory.event j').incoming.flow v' x ξ| ≤
          Cgrad * (K.toHistory.event j').incoming.flow.scalar v' x *
            Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v' x) *
            Real.sqrt (((K.toHistory.event j').incoming.flow.base.metric v').inner x ξ ξ)) ∧
    (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
      v - θ / Rn ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
      K.time j'.castSucc < τ → (τ : ℝ) < K.time j'.succ →
      GuardKX_C11KX ((K.toHistory.event j').incoming.flow.scalar v) qthr Ct v τ x →
      ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz x →
      ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
            (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
            (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b))

/-- **弱化 / inhabitant（`_P6GW`，PROVED）**：未 guard 的中心邻域合同 ⇒ guarded（丢 guard）。 -/
theorem PickedCenterNeighborhood_C11PT.guarded_P6GW {Dw Dc Tc θ Rn qthr ρ κ ε C1 C2 : ℝ}
    (Ct : ℝ≥0) {Cgrad : ℝ≥0} {K : RetainedCoreHistory.{u}} {σ : Icc (0 : ℝ) K.toHistory.horizon}
    {y : (K.toHistory.stageAt σ).Carrier}
    (h : PickedCenterNeighborhood_C11PT Dw Dc Tc θ Rn qthr ρ κ ε C1 C2 Cgrad K σ y) :
    PickedCenterNeighborhoodGuarded_P6GW Dw Dc Tc θ Rn qthr ρ κ ε C1 C2 Ct Cgrad K σ y := by
  intro j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx
  obtain ⟨h1, h2, h3⟩ := h j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x hx
  exact ⟨h1, fun v' hv' hw hq _ ξ => h2 v' hv' hw hq ξ,
    fun τ t1 t2 t3 t4 _ zz hzz b hb hbρ hc => h3 τ t1 t2 t3 t4 zz hzz b hb hbρ hc⟩

/-- **guarded 合同逐点付 guarded KSW `hU`（`_P6GW`，PROVED）**：`kswHU_of_pickedCenter_C11PT` 的孪生（guard
只透传）；证明体逐字。 -/
theorem kswHUGuarded_of_pickedCenter_P6GW {Dw Dd Rad Tc θ₀ Rn Cg ρ κ ε C1 C2 : ℝ}
    {Ct Cgrad : ℝ≥0}
    {K : RetainedCoreHistory.{u}} {σ : Icc (0 : ℝ) K.toHistory.horizon}
    {y : (K.toHistory.stageAt σ).Carrier} (hθ₀ : 0 ≤ θ₀) (hRn : 0 < Rn)
    (hPC : PickedCenterNeighborhoodGuarded_P6GW Dw (Dd + Rad) Tc θ₀ Rn (Cg * Rn) ρ κ ε C1 C2 Ct
      Cgrad K σ y)
    (j' : Fin K.eventCount) (v : ℝ) (hv1 : K.time j'.castSucc < v) (hv2 : v < K.time j'.succ)
    (hvT : (σ : ℝ) - Tc / Rn ≤ v) (hvσ : v ≤ σ)
    (x₁ : (K.toHistory.stage (K.toHistory.activeStage σ)).Carrier)
    (hx₁ : x₁ ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) y
      (Dw / Real.sqrt Rn))
    (hjσ : j'.castSucc ≤ K.toHistory.activeStage σ)
    (tr : BackwardPointTrace K.toHistory j'.castSucc (K.toHistory.activeStage σ) hjσ x₁)
    (w : (K.stage j'.castSucc).Carrier)
    (hzw : riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt Rn))
    (hRw : Rn ≤ (K.toHistory.event j').incoming.flow.scalar v w) :
    (∀ x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v) w
          (Rad / Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v w)),
      Cg * Rn < (K.toHistory.event j').incoming.flow.scalar v x →
      ∃ W : SpatialCanonicalWitness ((K.toHistory.event j').incoming.flow.base.metric v)
        ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
    (∀ x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v) w
          (Rad / Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v w)),
      ∀ v' ∈ Ioo (K.time j'.castSucc) v,
      v - θ₀ / (K.toHistory.event j').incoming.flow.scalar v w ≤ v' →
      Cg * Rn < (K.toHistory.event j').incoming.flow.scalar v' x →
      GuardKX_C11KX ((K.toHistory.event j').incoming.flow.scalar v) (Cg * Rn) Ct v v' x →
      ∀ ξ : TangentSpace ThreeModel x,
        |scalarDifferential (K.toHistory.event j').incoming.flow v' x ξ| ≤
          Cgrad * (K.toHistory.event j').incoming.flow.scalar v' x *
            Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v' x) *
            Real.sqrt (((K.toHistory.event j').incoming.flow.base.metric v').inner x ξ ξ)) ∧
    (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
      v - θ₀ / (K.toHistory.event j').incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
      K.time j'.castSucc < τ → (τ : ℝ) < K.time j'.succ →
      ∀ z ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v w)),
      GuardKX_C11KX ((K.toHistory.event j').incoming.flow.scalar v) (Cg * Rn) Ct v τ z →
      ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
      ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
            (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
            (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b)) := by
  have hθq : θ₀ / (K.toHistory.event j').incoming.flow.scalar v w ≤ θ₀ / Rn :=
    div_le_div_of_nonneg_left hθ₀ hRn hRw
  have hsub : ∀ x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v) w
      (Rad / Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v w)),
      x ∈ riemannianBallOf ((K.toHistory.event j').incoming.flow.base.metric v)
        (tr.point j'.castSucc le_rfl hjσ) ((Dd + Rad) / Real.sqrt Rn) := by
    intro x hx
    have hx' : riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v) w x <
        ENNReal.ofReal (Rad / Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v w)) := hx
    have hRad : 0 < Rad / Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v w) :=
      ENNReal.ofReal_pos.mp (zero_le.trans_lt hx')
    have hRad0 : 0 ≤ Rad := by
      by_contra hneg
      have : Rad / Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v w) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (not_le.mp hneg).le (Real.sqrt_nonneg _)
      linarith
    have hDd : 0 < Dd / Real.sqrt Rn := ENNReal.ofReal_pos.mp (zero_le.trans_lt hzw)
    have hRq : Rad / Real.sqrt ((K.toHistory.event j').incoming.flow.scalar v w) ≤
        Rad / Real.sqrt Rn :=
      div_le_div_of_nonneg_left hRad0 (Real.sqrt_pos.2 hRn) (Real.sqrt_le_sqrt hRw)
    change riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) x < ENNReal.ofReal ((Dd + Rad) / Real.sqrt Rn)
    calc riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
          (tr.point j'.castSucc le_rfl hjσ) x
        ≤ riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w +
          riemannianEDistOf ((K.toHistory.event j').incoming.flow.base.metric v) w x :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal (Dd / Real.sqrt Rn) + ENNReal.ofReal (Rad / Real.sqrt Rn) :=
          ENNReal.add_lt_add hzw (hx'.trans_le (ENNReal.ofReal_le_ofReal hRq))
      _ = ENNReal.ofReal ((Dd + Rad) / Real.sqrt Rn) := by
          rw [← ENNReal.ofReal_add hDd.le (hRad.le.trans hRq), add_div]
  refine ⟨fun x hx hC => (hPC j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x (hsub x hx)).1 hC,
    fun x hx v' hv' hθ' hC hg =>
      (hPC j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr x (hsub x hx)).2.1 v' hv' (by linarith) hC hg,
    fun τ hτ1 hτ2 hτ3 hτ4 z hz hg zz hzz b hb hbρ hctl =>
      (hPC j' v hv1 hv2 hvT hvσ x₁ hx₁ hjσ tr z (hsub z hz)).2.2 τ (by linarith) hτ2 hτ3 hτ4 hg
        zz hzz b hb hbρ hctl⟩

/-- **G3 T1 核心形 ⇐ guarded 中心邻域合同（`_P6GW`，PROVISIONAL[合同族 `hPC` guarded 形]）**：PICKT1
`hsliceR_lateHI_core_pickedCenter_C11PT` 的孪生：`hK` 由 `kswGuarded_P6GW`（无 binder，KSWEXIT guarded
ShortSLT）付，
中心邻域合同换 `PickedCenterNeighborhoodGuarded_P6GW`（(2)(3) 只在 guard 点，guard 常数 = `Ctime`、阈值 `Cg·R_n`）。
新增 `θ₀ ≤ 1/2`（K-SW CWP 年龄条件，原版经 `ksw_pos_C11KS2` 的单调性吸收）。结论逐字。 -/
theorem ObservedHistory.hsliceR_lateHI_core_pickedCenter_guarded_P6GW
    {θ₀ : ℝ} (hθ₀ : 0 < θ₀) (hθ₀2 : θ₀ ≤ 1 / 2)
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {Cg : ℝ} (hCg : 1 ≤ Cg) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
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
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt
        (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
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
 :
    ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ Rad : ℝ, 0 ≤ QB ∧
      Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
      ∀ l : Filter ℕ, l ≤ atTop → ∀ σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw : ℝ, 0 < Dw →
      (∀ᶠ n in l,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) + σ₁ / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
                ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
                ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                  ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) →
      (∀ᶠ n in l, PickedCenterNeighborhoodGuarded_P6GW Dw (Dd + Rad) (-σ₁) θ₀ (R n) (Cg * R n)
        (ρV n) κ ε C1 C2 Ctime Cgrad (K n) (σ n) (y n)) →
      ∀ᶠ n in l,
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hvt : v ≤ σ n), (σ n : ℝ) + σ₁ / R n ≤ v →
        (v : ℝ) ≤ σ n + σ₂ / R n → (K n).toHistory.time ((K n).toHistory.activeStage v) < v →
      ∀ tr₁ : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvt) x₁,
        metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          (tr₁.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono hvt))
              ≤ A * R n →
        ∃ CWP : ((K n).toHistory.stage ((K n).toHistory.activeStage v)).Carrier → Prop,
          (∀ w, riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₁.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → ¬ CWP w →
            R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
                w → ∀ x,
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) w x <
              ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
                Real.sqrt (metricScalarAt ((K n).toHistory.stageMetric
                    ((K n).toHistory.activeStage v) v) w)) →
            metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) x ≤
              QB * metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
                  w) ∧
          (∀ w, riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
              (tr₁.point ((K n).toHistory.activeStage v) le_rfl
                  ((K n).toHistory.activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → CWP w →
            ∃ (Ξ : standardCapWindow D₂ → ((K n).toHistory.stage
                ((K n).toHistory.activeStage v)).Carrier)
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
  obtain ⟨QB, Dcap, D₂, Rad, hQB, hD₂, hcore⟩ :=
    ObservedHistory.hsliceR_lateHI_core_short_guarded_P6GW (C1 := C1) (C2 := C2) (Cgrad := Cgrad)
      (kswGuarded_P6GW hθ₀ hθ₀2) hεle hκ hphi hCg hη₃ hLc htj recordsF hHI hcanK hδF hacc hrad hord
      hscaleK hbirthA hpinchK0 hslabK (fun n => (K n).toHistory) rfl σ y R hσ hRpos hqR hT₀ Tn
      aSeed haT hsT has pT seedTrace L hL hwin ρV hρV A Dd hA hDd
  refine ⟨QB, Dcap, D₂, Rad, hQB, hD₂, fun l hl σ₁ σ₂ h12 hσ₂ Dw hDw hdl hPC => ?_⟩
  refine hcore l hl σ₁ σ₂ h12 hσ₂ Dw hDw hdl ?_
  filter_upwards [hPC] with n hn
  intro j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr _ _ w _ hzw hRw
  have hσ2R : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ (hRpos n)
  have hvT : (σ n : ℝ) - -σ₁ / R n ≤ v := by
    rw [neg_div, sub_neg_eq_add]
    exact hvσ1
  exact kswHUGuarded_of_pickedCenter_P6GW hθ₀.le (hRpos n) hn j' v hv1 hv2 hvT (by linarith) x₁ hx₁
    hjσ tr w hzw hRw

end GuardedPickT1

/-- consumer（G3b，`_P6GW`）：PICKT1 `hsliceR_lateHI_core_pickedCenter_C11PT` 的合同族（未 guard）经弱化即喂 guarded
核心形——guarded 链严格覆盖原链，且 `hK` 无 binder。 -/
example {Dw Dc Tc θ Rn qthr ρ κ ε C1 C2 : ℝ} (Ct : ℝ≥0) {Cgrad : ℝ≥0}
    {K : RetainedCoreHistory.{u}} {σ : Icc (0 : ℝ) K.toHistory.horizon}
    {y : (K.toHistory.stageAt σ).Carrier}
    (h : PickedCenterNeighborhood_C11PT Dw Dc Tc θ Rn qthr ρ κ ε C1 C2 Cgrad K σ y) :
    PickedCenterNeighborhoodGuarded_P6GW Dw Dc Tc θ Rn qthr ρ κ ε C1 C2 Ct Cgrad K σ y :=
  h.guarded_P6GW Ct

/-- consumer（G3b，`_P6GW`）：guarded T1 核心形。 -/
example := @ObservedHistory.hsliceR_lateHI_core_pickedCenter_guarded_P6GW.{u}

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
