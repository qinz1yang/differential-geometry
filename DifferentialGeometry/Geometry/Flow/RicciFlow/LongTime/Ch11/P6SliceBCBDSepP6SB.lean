import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDCeilP6SB

/-!
# 切片 BCBD：surgery 避让由 cap 出生时刻 ceiling + (SEP′) 型分离付清（O-CH11-SLICE-BCBD G7，后缀 `_P6SB`）

G5 `sliceBCBD_kernel_fresh_theta_ev_P6SB` 的 kernel 帧 `hnotK`（eventually、年龄 `≤ θ₀/scale`）在本文件
**不再作前提**：
* G6 `capCeiling_of_firstExit_P6SB`（CXJD 跨 slab ceiling，PROVED ⇐ CXJD 结构输入族 + `hwin` + `hsepT`）
  给出 cap 出生时刻 `R_out(A(i⁺)) ≤ 2·Qb·R`；
* 树内 `exists_capWindow_scalar_lower_C11G` 给出 `scale/2 ≤ R_out(window x)`（records 精度 eventually
  `≤ ε₀`，由 kernel `hacc : accuracy ≤ 1/(n+1)` 推出；阶 `≥ 2` 由 `hord` 推出）；
* `hsep4 : 4·Qb·R < scale` 推出矛盾。
主定理 **`ObservedHistory.sliceBCBD_kernel_fresh_sep_P6SB`**：结论 = G3d 结论逐字（验收终点形）。与 G5 的差别：
删去 `hnotK`，加 (SEP′) 型分离 `hsepT`、`hsep4`（新近 record 的尺度 ≫ `R`，常数显式），kernel `hrad`
加强一格为 `n + 2 ≤ modelRadius`（`hnotK` 窗口半径 `‖x‖ < n+2` 要落在 canonical window 的精度区内）。
生成器 `build-logs/scratch/O-CH11-SLICE-BCBD/gen/gen7.py`（G5 binder 块切片 + assert 替换）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **切片 BCBD，surgery 避让 ⇐ (SEP′)（`_P6SB`）**：G5 主定理去掉 `hnotK`，换成 `hsepT` + `hsep4`
（kernel `hrad` 加强为 `n+2 ≤ radius`）。PROVISIONAL[hgood、CXJD 结构输入族、`hdistW`、FRESH seed 数据、
kernel 帧 binder（`hacc / hrad₂ / hord / hpinchK0 / recordsK / hcanK / hT₀ / hRlt / hwin`）、(SEP′) 型
`hsepT / hsep4`]。 -/
theorem sliceBCBD_kernel_fresh_sep_P6SB
    {ε C1' C2' : ℝ} {Ctime' : ℝ≥0} (hεcone : ε ≤ coneAccuracy) (hC20 : 0 ≤ C2')
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad2 : ∀ n : ℕ, ((n : ℝ) + 1) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hσ : ∀ n, (σ n : ℝ) = t n)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRlt : ∀ n : ℕ, (n : ℝ) + 1 < R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) {Cg : ℝ} (hCg : 2 ≤ Cg)
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
        (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistW : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
            ENNReal.ofReal (L n / Real.sqrt (R n)))
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon)
      (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (qX : ℕ → CutoffParameters) (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (recordsX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      GeometricCutoffRecord (Kh n) e (qX n))
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hcanX : ∀ n (e : Fin (Kh n).eventCount) (he : T₀X n ≤ (Kh n).time e.succ) b,
      ((recordsX n e he).static b).hasCanonicalWindow)
    (haccX : ∀ n, (qX n).modelAccuracy ≤ 1 / 2)
    (hDmX : ∀ n, StandardCap.transitionEnd + 10 < (qX n).modelRadius)
    (hprotC : ∀ n (v' : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v')
      (hvs : v' ≤ σ n) (z'' : ((Kh n).stageAt (σ n)).Carrier)
      (A : BackwardPointTrace (Kh n) ((Kh n).activeStage v')
          ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono hvs) z'')
      (e : Fin (Kh n).eventCount) (h1 : (Kh n).activeStage (aSeed n) ≤ e.castSucc)
      (h2 : e.succ ≤ (Kh n).activeStage (Tn n))
      (h3 : (Kh n).activeStage v' ≤ e.castSucc)
      (h4 : e.succ ≤ (Kh n).activeStage (σ n))
      (he : T₀X n ≤ (Kh n).time e.succ),
      (∀ (w : Icc (0 : ℝ) (Kh n).horizon) (hw : v' ≤ w) (hwσ : w ≤ σ n),
        (Kh n).time e.succ ≤ (w : ℝ) →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage w) w)
            ((seedTrace n).point ((Kh n).activeStage w)
              ((Kh n).activeStage_mono (hav.trans hw))
              ((Kh n).activeStage_mono (hwσ.trans (hsT n))))
            (A.point ((Kh n).activeStage w) ((Kh n).activeStage_mono hw)
              ((Kh n).activeStage_mono hwσ)) <
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n))
                ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n))) → ∀ b,
      (seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
          ((recordsX n e he).static b).window ''
            {w : standardCapWindow (qX n).modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} ∧
        A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
          ((recordsX n e he).static b).window ''
            {w : standardCapWindow (qX n).modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10})
    (hdσ : ∀ n, riemannianEDistOf ((Kh n).stageMetric
        ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤)
    {nr : ℝ → ℝ} {Aκ κ Tκ : ℝ} (hκ : 0 < κ)
    (hWK : ∀ n, KappaSeedWindowFwd_C11PK nr Aκ κ Tκ (Kh n))
    (hTκ : ∀ n, Tκ ≤ (Tn n : ℝ)) (htimeS : ∀ n, 2 * r ^ 2 < (Tn n : ℝ))
    (hvolS : ∀ n, ENNReal.ofReal (Aκ⁻¹ * r ^ 3) ≤ Geometry.Collapse.ballVolume
      ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) r)
    (hnrS : ∀ n (w : ℝ), (Tn n : ℝ) - r ^ 2 / 2 ≤ w → w ≤ (Tn n : ℝ) → nr w ≤ r)
    (hwinF : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r ^ 2 / 2 ≤ (σ n : ℝ) - T / R n)
    (hgate : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r))
    (hsepT : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      θ₀ * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) / max (max 1 Cg) 1 *
        ((recordsK n i hi).static b).neck.scale)
    (hsep4 : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      2 * (2 * (max (max 1 Cg) 1 * R n)) < ((recordsK n i hi).static b).neck.scale) :
    ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n))
          (yG n)
          (A / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          Q * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) := by
  subst hKh
  have hR1 : ∀ n, 1 ≤ R n := fun n => by
    have h1 := hRlt n
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  obtain ⟨ε₀, hε₀, hlow⟩ := exists_capWindow_scalar_lower_C11G.{u}
  have hceil := ObservedHistory.capCeiling_of_firstExit_P6SB hC20 hjt htj σ hσ y yG hyG R hRpos
    hR1 hRn Tn aSeed haT hsT has pT seedTrace L hL hgood hr hsmall hclock a₀ ha₀ hpin hRa qX T₀X
    hT₀X recordsX hOldX hcanX haccX hDmX hprotC hdσ hwin recordsK hsepT
  have haccE : ∀ᶠ n in atTop, (p n).modelAccuracy ≤ ε₀ := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [h0.eventually (ge_mem_nhds hε₀)] with n hn
    exact (hacc n).trans hn
  have hnotKev : ∀ᶠ n in atTop, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (hl : i.succ ≤ (j n).castSucc)
      (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
        ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
        t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
    filter_upwards [hceil, haccE] with n hc ha
    rintro ⟨i, hi, hl, A, b, x, h1, h2, h3⟩
    have hx : ‖x.val‖ < (p n).modelRadius := lt_of_lt_of_le h2 (hrad2 n)
    have hS := hlow ((K n).toHistory.event i) ha (le_trans (by omega) (hord n))
      ((recordsK n i hi).static b) (hcanK n i hi b) x hx
    rw [← h1] at hS
    have hC := hc i hi hl A b h3
    have hP := hsep4 n i hi b hl h3
    linarith
  exact ObservedHistory.sliceBCBD_kernel_fresh_theta_ev_P6SB (hεcone := hεcone) (hC20 := hC20)
    (hphi := hphi) (hθ₀ := hθ₀) (hjt := hjt) (htj := htj) (hcanK := hcanK) (hacc := hacc)
    (hrad := fun n => le_trans (by linarith) (hrad2 n)) (hord := hord) (hpinchK0 := hpinchK0)
    (hnotK := hnotKev) (Kh := fun n => (K n).toHistory) (hKh := rfl) (σ := σ) (hσ := hσ) (y := y)
    (hyG := hyG) (R := R) (hRpos := hRpos) (hRn := hRn) (hRlt := hRlt) (hT₀ := hT₀) (Tn := Tn)
    (aSeed := aSeed) (haT := haT) (hsT := hsT) (has := has) (pT := pT) (seedTrace := seedTrace)
    (L := L) (hL := hL) (hCg := hCg) (hgood := hgood) (hwin := hwin) (hdistW := hdistW) (hr := hr)
    (hsmall := hsmall) (hclock := hclock) (a₀ := a₀) (ha₀ := ha₀) (hpin := hpin) (hRa := hRa)
    (qX := qX) (T₀X := T₀X) (hT₀X := hT₀X) (recordsX := recordsX) (hOldX := hOldX) (hcanX := hcanX)
    (haccX := haccX) (hDmX := hDmX) (hprotC := hprotC) (hdσ := hdσ) (hκ := hκ) (hWK := hWK)
    (hTκ := hTκ) (htimeS := htimeS) (hvolS := hvolS) (hnrS := hnrS) (hwinF := hwinF)
    (hgate := hgate)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
