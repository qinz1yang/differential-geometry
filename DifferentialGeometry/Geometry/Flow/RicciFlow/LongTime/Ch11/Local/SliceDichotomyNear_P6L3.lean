import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.SliceDichotomyBranches_P6L2

/-!
# 窗口切片二分（单切片）的 near-trace 形（O-CH11-P6ANCH3 G1，后缀 `_P6L3`）

`RetainedCoreHistory.slice_dichotomy_P6L2` 的副本，证明体逐字；唯一改动：U 侧前提 `hU` 多收一个
**near-trace** 条件 `d_v(zj, w) < Dd/√Rn`（`zj` = 基点 `z` 在 `K.stage j.castSucc` 里的 `HEq` 像）。
原证明只在 `w` 满足 `d(z, w) < Dd/√Rn`（非 CWP 分支的 `hzw`）时取 `hU`，故条件可直接透传。
用途（P6ANCH3 G1/G2）：条件形 `hUVC` 只能在 traced region 覆盖的范围内生产（survival 要 `w` 靠近
trace 点），near-trace 形把这一信息交给生产方；seed Good 区条件 `d(sj, w) ≤ d1 + Dd/√Rn` 保留。
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

/-- **切片二分（单切片，near-trace 形，`_P6L3`）**：`slice_dichotomy_P6L2` + `hU` 收
`d(zj, w) < Dd/√Rn`。event slab `j` 内部切片 `v`、stage 变量 `k = j.castSucc`（`subst`；
供序列层取 `k := activeStage v`）、基点 `z`（trace 点）与 seed 点 `sk`（`HEq sk sj`）、`d(sk, z) ≤ d1`；
U 侧前提（Good 区 `d(sj, w) ≤ d1 + Dd/√Rn`、`Rn ≤ R(w)` 的每个 `w` 上：witness / 梯度 / 区域 κ，阈值 `4Rn`）
+ slab 导数数据（同时喂 SLT 的 `hslabs`/`hder` 与 G2p）+ CWP 分支数据 ⇒ Kdata `hslice` 的二分体
（`CWP := K.CapWindowPoint records j.castSucc · v Dcap (1/2)`）。 -/
theorem RetainedCoreHistory.slice_dichotomy_near_P6L3
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc) :
    ∃ Cbirth : ℝ, 0 < Cbirth ∧ ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
    Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
    ∃ (Λ Rad Bw Rmin ζmin δ₀ : ℝ) (m₀ : ℕ), 1 ≤ Λ ∧ 0 < Bw ∧ 0 < ζmin ∧ 0 < δ₀ ∧
    ∀ (K : RetainedCoreHistory.{u}) (p₀ : CutoffParameters) (δb ρb : ℝ) {p : CutoffParameters}
      (records : ∀ i, GeometricCutoffRecord K.toHistory i p),
      K.IsCanonicalCutoffRecordFamily p₀ δb ρb records →
      δb ≤ δ₀ → Rmin ≤ p₀.modelRadius → m₀ ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζmin →
      K.EventSlabsPinched phi →
    ∀ (qcan a₀ : ℝ), 0 < qcan →
      (∀ x, InFixedHamiltonIveyRegion (K.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (K.initialMetric 0) x) →
      (∀ i b, qcan ≤ Cbirth * ((records i).static b).neck.scale ∧
        1 ≤ a₀ * ((records i).static b).neck.scale) →
    ∀ (j : Fin K.eventCount), K.EventSlabsDerivative Ctime qcan j.castSucc →
    ∀ v : ℝ, K.time j.castSucc < v → v < K.time j.succ →
      (K.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan v →
    ∀ (Rn ρ : ℝ), 0 < Rn → qcan ≤ 4 * Rn → Λ ≤ Rn → Λ ≤ Rn * v → Λ ≤ ρ * Real.sqrt Rn →
    ∀ (k : Fin (K.eventCount + 1)), k = j.castSucc →
    ∀ (z sk : (K.toHistory.stage k).Carrier) (sj : (K.stage j.castSucc).Carrier), HEq sk sj →
    ∀ d1 : ENNReal, riemannianEDistOf (K.toHistory.stageMetric k v) sk z ≤ d1 →
    ∀ zj : (K.stage j.castSucc).Carrier, HEq z zj →
    (∀ w : (K.stage j.castSucc).Carrier,
      riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v) sj w ≤
        d1 + ENNReal.ofReal (Dd / Real.sqrt Rn) →
      riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v) zj w <
        ENNReal.ofReal (Dd / Real.sqrt Rn) →
      Rn ≤ (K.toHistory.event j).incoming.flow.scalar v w →
        (∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
              (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
          4 * Rn < (K.toHistory.event j).incoming.flow.scalar v x →
          ∃ W : SpatialCanonicalWitness ((K.toHistory.event j).incoming.flow.base.metric v)
            ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
        (∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
              (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
          ∀ v' ∈ Ioo (K.time j.castSucc) v,
          v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
          4 * Rn < (K.toHistory.event j).incoming.flow.scalar v' x →
          ∀ ξ : TangentSpace ThreeModel x,
            |scalarDifferential (K.toHistory.event j).incoming.flow v' x ξ| ≤
              Cgrad * (K.toHistory.event j).incoming.flow.scalar v' x *
                Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v' x) *
                Real.sqrt (((K.toHistory.event j).incoming.flow.base.metric v').inner x ξ ξ)) ∧
        (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
          v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
          K.time j.castSucc < τ → (τ : ℝ) < K.time j.succ →
          ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
                (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
          ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
                (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
                (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b))) →
    ∃ CWP : (K.toHistory.stage k).Carrier → Prop,
      (∀ w, riemannianEDistOf (K.toHistory.stageMetric k v)
          z w <
          ENNReal.ofReal (Dd / Real.sqrt Rn) → ¬ CWP w →
        Rn ≤ metricScalarAt (K.toHistory.stageMetric k v) w → ∀ x,
        riemannianEDistOf (K.toHistory.stageMetric k v) w x <
          ENNReal.ofReal ((2 * Dd * Real.sqrt A + 1) /
            Real.sqrt (metricScalarAt (K.toHistory.stageMetric k v) w)) →
        metricScalarAt (K.toHistory.stageMetric k v) x ≤
          QB * metricScalarAt (K.toHistory.stageMetric k v) w) ∧
      (∀ w, riemannianEDistOf (K.toHistory.stageMetric k v)
          z w <
          ENNReal.ofReal (Dd / Real.sqrt Rn) → CWP w →
        ∃ (Ξ : standardCapWindow D₂ → (K.toHistory.stage k).Carrier)
          (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
          Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dcap + 1 ∧
          ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
            τw ∈ Icc (0 : ℝ) (1 / 2) ∧
            ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
              metricDerivNorm m (localPullMetric (scaleMetric lam hlam
                  (K.toHistory.stageMetric k v)) Ξ hΞ)
                ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
                (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃) := by
  obtain ⟨Cbirth, hCbirth, hCWP⟩ := RetainedCoreHistory.capWindow_branch_of_records_P6M.{u} Ctime
  refine ⟨Cbirth, hCbirth, fun A Dd hA hDd => ?_⟩
  have hAB : 0 < 2 * Dd * Real.sqrt A + 1 := by positivity
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hD, -, hζ₀, hBw, hmain⟩ :=
    RetainedCoreHistory.slice_scalar_bound_of_not_capWindowPoint_P6L2 hεle κ C1 C2 hκ Ctime Cgrad
      hphi (2 * Dd * Real.sqrt A + 1) hAB 4
  have hDpos : 0 < Dcap := StandardCap.transitionEnd_pos.trans hD
  have hDD₂ : Dcap < Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) := by
    have : 0 ≤ 2 * Dd * Lc * Real.sqrt (2 * A) := by positivity
    linarith
  obtain ⟨Rr, -, m₀, -, ζ₁, δ₀, hζ₁, hδ₀, hcap⟩ :=
    hCWP Dcap (Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1)) η₃ hDpos hDD₂ hη₃
  refine ⟨Q, Dcap, Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1), by linarith, le_rfl, Λ, Rad,
    Bw, max Rr Rrad, min ζ₀ ζ₁, δ₀, max m₀ 2, hΛ, hBw, lt_min hζ₀ hζ₁, hδ₀, ?_⟩
  intro K p₀ δb ρb p records hrec hδ hRad hord hacc hpinch qcan a₀ hq0 hHI hlow hbirth j hslab v hv1
    hv2 hder Rn ρ hRn hqR hΛRn hΛv hΛρ k hk z sk sj hs d1 hzd zj hzj hU
  subst hk
  obtain rfl := eq_of_heq hs
  obtain rfl := eq_of_heq hzj
  have hv0 : 0 ≤ v := (K.toHistory.time_nonneg _).trans hv1.le
  refine ⟨fun w => K.CapWindowPoint records j.castSucc w v Dcap (1 / 2), ?_, ?_⟩
  · intro w hzw hncw hRw x hx
    rw [ObservedHistory.stageMetric_castSucc_apply] at hzd hzw hRw hx ⊢
    have hw : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v) sk w ≤
        d1 + ENNReal.ofReal (Dd / Real.sqrt Rn) :=
      (riemannianEDistOf_triangle _ _ _ _).trans (add_le_add hzd hzw.le)
    obtain ⟨h1, h4, h5⟩ := hU w hw hzw hRw
    have hRw2 : Rn ≤ (K.toHistory.event j).incoming.flow.scalar v w := hRw
    have hρ0 : 0 < ρ := by
      by_contra hneg
      have : ρ * Real.sqrt Rn ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) (Real.sqrt_nonneg _)
      linarith
    exact hmain K j (v - Bw / (K.toHistory.event j).incoming.flow.scalar v w) (fun i _ => records i)
      (fun i _ b => (hrec).2.2.2.2.2.1 i b)
      (by rw [hrec.2.1]; exact (le_max_right _ _).trans hRad)
      (by rw [hrec.2.2.1]; exact le_trans (by simp) hord)
      (by rw [hrec.2.2.2.1]; exact hacc.trans (min_le_left _ _)) hpinch v hv1 hv2 w (4 * Rn) ρ
      le_rfl (by positivity) (by linarith [hRw2]) (hΛRn.trans hRw)
      (hΛv.trans (mul_le_mul_of_nonneg_right hRw hv0))
      (hΛρ.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hRw) hρ0.le)) _ (fun _ h => h) h1
      qcan hqR hslab hder h4 h5
      (by
        rintro ⟨i, -, hl, B, b, x', e1, e2, e3⟩
        exact hncw ⟨i, hl, B, b, x', e1, e2, e3⟩) x hx
  · intro w _ hcw
    exact hcap K p₀ δb ρb records hrec hδ ((le_max_left _ _).trans hRad)
      ((le_max_left _ _).trans hord) (hacc.trans (min_le_right _ _)) qcan a₀ hq0 hHI hlow hbirth
      j hslab v hv1 hv2 hder w hcw

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
