import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.SliceDichotomyBranches_P6L2

/-!
# 窗口切片二分的序列层生产：`hsliceR`（O-CH11-P6ANCH2 G3，后缀 `_P6M2`）

设计段 1b / 第 1 项（state-O-CH11-P6ANCH）的落地：Kdata `hslice`（G2v `hsliceW` / G2w `hW` (ii) 同一事实）在
**开 slab 切片**上的生产。单切片装配 = `Local/SliceDichotomyBranches_P6L2`（SLT 窗口版 + G2p）；本文件做序列层：
slab 指标 `j'`（`activeStage v = j'.castSucc`，`v < σ < time (j n).succ ≤ time last`）、seed 点的 `HEq`、
数据前提 eventually（`hpar`、birth 比较 ⇐ `hscaleK`）、`Λ ≤ R v` ⇐ `R σ → ∞`。
**形的改动**（相对 Kdata `hslice`）：(i) 切片 `v` 只在开 slab（`time (activeStage v) < v`，O3：SLT 要正年龄）；
(ii) `σ'` 换成区间一致 `[σ₁, σ₂]`（O3 的右移要在 `(v, v+e)` 上一致取切片）。consumer 见
`Local/BoundedCurvatureAtDistanceAnchorOpen_P6L2`（`hbcad` ⇐ `hsliceR`，event 时刻切片用右移）。
**显式前提**：`hdistQ`（相对 hdist，余量 `L/4`；S-CH11-HDISTC `hdistC_of_traced_C11G3` 同形可给）、`hUV`
（O1 `hdistV` + `hgood` 与 O2 `hκV` = KAPPA2 `RegionalKappa_C11Q3` 的合并出口，Good 区半径 `L/2`）、初始
Hamilton–Ivey `a₀`（G2p）。
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

/-- backward trace 的点在相等 stage 指标间 `HEq`。 -/
theorem point_heq_of_eq_P6M2 {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)}
    {hle : first ≤ last} {x : (H.stage last).Carrier} (A : BackwardPointTrace H first last hle x)
    {m m' : Fin (H.eventCount + 1)} (h : m = m') (h1 : first ≤ m) (h2 : m ≤ last)
    (h1' : first ≤ m') (h2' : m' ≤ last) : HEq (A.point m h1 h2) (A.point m' h1' h2') := by
  subst h
  rfl

/-- **`hsliceR`（窗口切片二分，开 slab、`σ'` 区间一致形）⇐ 数据 + Good 区 U 侧 + 相对 `hdist`（余量 `L/4`）**
（O-CH11-P6ANCH2 G3）：对每个开 slab 切片 `v ∈ [σ + σ₁/R, σ + σ₂/R]`（`time (activeStage v) < v`）、每个
base-ball 点的 trace 点 `z = tr₁(v)`，`CWP := K.CapWindowPoint recordsK j'.castSucc · v Dcap (1/2)`
给出 Kdata
`hslice` 的两条（非 CWP：SLT 窗口版；CWP：G2p）。显式前提：K 层数据（Kdata 形）+ 初始 Hamilton–Ivey `a₀`
（G2p 的 birth 比较由 `hscaleK` eventually 推出）+ `hdistQ`（Kdata `hdist` 形，余量 `L/4`）+ `hUV`（seed
Good 区 `d_v(seed, w) ≤ d_σ + L/(2√R)` 的高曲率点 `w` 的 `Rad/√R(w)`-球上：witness / 梯度 / 区域 κ；
= O1 `hdistV` + selection `hgood` 与 O2 `hκV` 的合并出口）。event 时刻切片（`time (activeStage v) = v`）不在本形，
见 `hbcad_of_slice_dichotomy_open_P6L2`（右移）。 -/
theorem ObservedHistory.hsliceR_of_slice_data_P6M2
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc)
    {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (htj : ∀ n, t n < (K n).time (j n).succ)
    {D qcan : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
    {recordsK : ∀ n i, GeometricCutoffRecord (K n).toHistory i (p n)}
    (hrecK : ∀ n, (K n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (recordsK n))
    (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n)
    (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscaleK : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * qcan n ≤ ((recordsK n i).static b).neck.scale)
    (hpinchK0 : ∀ n, (K n).EventSlabsPinched phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime (qcan n) (Fin.last (K n).eventCount))
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI0 : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) a₀ x)
    (hlow0 : ∀ n x, -3 / a₀ ≤ metricScalarAt ((K n).initialMetric 0) x)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n) (hqR : ∀ n, qcan n ≤ R n)
    (hRt : Tendsto (fun n => R n * σ n) atTop atTop)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistQ : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hUV : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ᶠ n in atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            4 * R n < ((Kh n).event j').incoming.flow.scalar v x →
            ∃ W : SpatialCanonicalWitness (((Kh n).event j').incoming.flow.base.metric v)
              ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((Kh n).time j'.castSucc) v,
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            4 * R n < ((Kh n).event j').incoming.flow.scalar v' x →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential ((Kh n).event j').incoming.flow v' x ξ| ≤
                Cgrad * ((Kh n).event j').incoming.flow.scalar v' x *
                  Real.sqrt (((Kh n).event j').incoming.flow.scalar v' x) *
                  Real.sqrt ((((Kh n).event j').incoming.flow.base.metric v').inner x ξ ξ)) ∧
          (∀ (τ : Icc (0 : ℝ) (Kh n).horizon),
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (Kh n).time j'.castSucc < τ → (τ : ℝ) < (Kh n).time j'.succ →
            ∀ z ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                  (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                  ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                  (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))) :
    ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
      Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
      ∀ σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ᶠ n in atTop,
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) + σ₁ / R n ≤ v →
        (v : ℝ) ≤ σ n + σ₂ / R n → (Kh n).time ((Kh n).activeStage v) < v →
      ∀ tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₁,
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
        ∃ CWP : ((Kh n).stage ((Kh n).activeStage v)).Carrier → Prop,
          (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → ¬ CWP w →
            R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w → ∀ x,
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v) w x <
              ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
                Real.sqrt (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w)) →
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) x ≤
              QB * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) w) ∧
          (∀ w, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) w <
              ENNReal.ofReal (Dd / Real.sqrt (R n)) → CWP w →
            ∃ (Ξ : standardCapWindow D₂ → ((Kh n).stage ((Kh n).activeStage v)).Carrier)
              (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
              Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
              ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
                τw ∈ Icc (0 : ℝ) (1 / 2) ∧
                ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
                  metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                      ((Kh n).stageMetric ((Kh n).activeStage v) v)) Ξ hΞ)
                    ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                    (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃) := by
  intro A Dd hA hDd
  obtain ⟨Cbirth, hCbirth, hP⟩ := RetainedCoreHistory.slice_dichotomy_P6L2 hεle κ C1 C2 hκ Ctime
    Cgrad hphi hη₃ hLc
  obtain ⟨QB, Dcap, D₂, hQB, hD₂, Λ, Rad, Bw, Rmin, ζmin, δ₀, m₀, hΛ, -, hζ, hδ₀, hmain⟩ :=
    hP A Dd hA hDd
  refine ⟨QB, Dcap, D₂, hQB, hD₂, fun σ₁ σ₂ h12 hσ₂ Dw hDw => ?_⟩
  subst hKh
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hR : Tendsto R atTop atTop := tendsto_atTop_mono (fun n => (hqcan n).trans (hqR n)) hnat
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hδ : ∀ᶠ n in atTop, δb n ≤ δ₀ :=
    (h0.eventually (ge_mem_nhds hδ₀)).mono fun n hn => (hpar n).2.2.2.2.trans hn
  have hacc : ∀ᶠ n in atTop, (p₀ n).modelAccuracy ≤ ζmin :=
    (h0.eventually (ge_mem_nhds hζ)).mono fun n hn => (hpar n).1.trans hn
  have hrad : ∀ᶠ n in atTop, Rmin ≤ (p₀ n).modelRadius :=
    (hnat.eventually_ge_atTop Rmin).mono fun n hn => hn.trans ((hpar n).2.1.trans (hpar n).2.2.1)
  have hord : ∀ᶠ n in atTop, m₀ ≤ (p₀ n).modelOrder :=
    (eventually_ge_atTop m₀).mono fun n hn => le_trans (by omega) (hpar n).2.2.2.1
  have hbirth : ∀ᶠ n in atTop, ∀ i b, qcan n ≤ Cbirth * ((recordsK n i).static b).neck.scale ∧
      1 ≤ a₀ * ((recordsK n i).static b).neck.scale := by
    filter_upwards [hnat.eventually_ge_atTop (1 / Cbirth), hnat.eventually_ge_atTop (1 / a₀)]
      with n hn1 hn2 i b
    have hs := hscaleK n i b
    have hq := hqcan n
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    have hC1 : 1 ≤ ((n : ℝ) + 1) * Cbirth := (div_le_iff₀ hCbirth).1 hn1
    have ha1 : 1 ≤ ((n : ℝ) + 1) * a₀ := (div_le_iff₀ ha₀).1 hn2
    constructor
    · calc qcan n = qcan n * 1 := by ring
        _ ≤ qcan n * (((n : ℝ) + 1) * Cbirth) := mul_le_mul_of_nonneg_left hC1 (by linarith)
        _ = ((n : ℝ) + 1) * qcan n * Cbirth := by ring
        _ ≤ ((recordsK n i).static b).neck.scale * Cbirth :=
          mul_le_mul_of_nonneg_right hs hCbirth.le
        _ = Cbirth * ((recordsK n i).static b).neck.scale := by ring
    · have hq1 : (1 : ℝ) ≤ qcan n := by linarith
      calc (1 : ℝ) ≤ ((n : ℝ) + 1) * a₀ := ha1
        _ ≤ ((n : ℝ) + 1) * qcan n * a₀ := by nlinarith
        _ ≤ ((recordsK n i).static b).neck.scale * a₀ := mul_le_mul_of_nonneg_right hs ha₀.le
        _ = a₀ * ((recordsK n i).static b).neck.scale := by ring
  have hT1 : 0 < -σ₁ := by linarith
  filter_upwards [hδ, hrad, hord, hacc, hbirth, hR.eventually_ge_atTop Λ,
    hRt.eventually_ge_atTop (Λ - σ₁), hρV.eventually_ge_atTop Λ, hL.eventually_ge_atTop (4 * Dd),
    hwin (-σ₁) hT1, hdistQ Dw (-σ₁) hDw hT1, hUV Rad Bw σ₁ σ₂ h12 hσ₂]
    with n e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
  intro x₁ hx₁ v hvt hv1 hv2 hage tr₁ _
  have hvwin : (σ n : ℝ) - -σ₁ / R n ≤ v := by
    rw [neg_div, sub_neg_eq_add]
    exact hv1
  have hav : aSeed n ≤ v := show (aSeed n : ℝ) ≤ v from e10.trans hvwin
  have hlast : (K n).toHistory.activeStage v ≠ Fin.last (K n).eventCount := by
    intro h
    have h1 := ObservedHistory.activeStage_time_le (K n).toHistory v
    rw [h] at h1
    have h2 : (K n).time (j n).succ ≤ (K n).time (Fin.last (K n).eventCount) :=
      (K n).toHistory.time_strictMono.monotone (Fin.le_last _)
    have h3 : (v : ℝ) ≤ t n := by rw [← hσ n]; exact hvt
    have h4 := htj n
    change (K n).time (Fin.last (K n).eventCount) ≤ (v : ℝ) at h1
    linarith
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
  refine hmain (K n) (p₀ n) (δb n) (ρb n) (recordsK n) (hrecK n) e1 e2 e3 e4 (hpinchK0 n) (qcan n)
    a₀ (by have := hqcan n; have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith) (hHI0 n) (hlow0 n) e5
    j' (fun i _ => hslabK n i (Fin.castSucc_lt_last i)) v ht1 ht2
    (fun y' t' ht hR' => hslabK n j' (Fin.castSucc_lt_last j') y' t' ⟨ht.1, ht.2.trans ht2⟩ hR')
    (R n) (ρV n) (hRpos n) (by linarith [hqR n, hRpos n]) e6 hΛv e8 _ hj'.symm
    (tr₁.point _ le_rfl _) _ _ hs _ (e11 x₁ hx₁ v hav hvt hvwin tr₁) ?_
  intro w hw hRw
  refine e12 j' v ht1 ht2 hv1 hv2 h1 h2 w (hw.trans ?_) hRw
  rw [add_assoc]
  refine add_le_add le_rfl ?_
  rw [← ENNReal.ofReal_add hL0 (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsq : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 (hRpos n)
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by linarith) hsq.le

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
