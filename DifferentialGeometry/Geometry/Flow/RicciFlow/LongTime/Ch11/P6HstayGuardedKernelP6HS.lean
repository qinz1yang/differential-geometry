import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TerminalBCDLocalKernelP6F3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KSWGuardedCone3C11KX

/-!
# FOOT3 slice kernel 的 guarded 孪生（HSTAY-A4 G1，后缀 `_P6HS`；R-C11-21 D-21-8 第三路线）

FOOT3 kernel `RetainedCoreHistory.slice_scalar_bound_localDeriv_P6F3` 走 P6WB
（`…_terminal_window_P6WB`，反证取 `Bw n = n + 1 + θ`，∃ 窗口深度 `Bw`），U 侧导数 / 梯度要在整窗
`v − Bw/R(v, w) ≤ v′` 上给。本文件把 SLT 核换成 KSWEXIT G8 的 guarded ShortSLT
`shortSLT_guarded_C11KX : 0 < θ → ShortSLTGuarded_C11KX θ`（PROVED，无 binder），`θ := 1/2`：
* **`RetainedCoreHistory.slice_scalar_bound_localDeriv_guarded_P6HS`**（PROVED）：P6F3 kernel 证明体逐字
  （prefix 化同 P6F3），差别只有三处：
  1. 常数 `∃ Q Λ Dcap Rrad ζ₀ Rad`（不再 ∃ `Bw`）；窗口深度固定为 `θ = 1/2`：`v − 1/2/R(v, w) ≤ v′`；
  2. `hslabL`（前 slab 沿 U 出发 trace，guard 按 trace 的终端点 `z` 计）、`hderL`、`hgrad` 的每个求值点多一个
     逐点 guard `GuardKX_C11KX (R(v, ·)) q Ctime v v′ z`（`2·Ctime·max(R(v, z), q)·(v − v′) ≤ 1`）——
     **只要求自适应短窗**；
  3. κ（`hnc`）、pinching、`hW`、records、`hnot`（`1/2·scale⁻¹`）与 P6F3 逐字（κ 不加 guard，严格更强的前提）。
  结论与 P6F3 逐字。
生成：build-logs/scratch/HSTAY-A4/gen/gen1.py（P6F3 l.47–142 切文本 + 断言替换）。
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

/-- **guarded slice kernel（`_P6HS`，PROVED ⇐ `shortSLT_guarded_C11KX`）**：P6F3
`slice_scalar_bound_localDeriv_P6F3` 的孪生；窗口 `θ = 1/2`、U 侧导数 / 梯度只在 KX guard 上要求。 -/
theorem RetainedCoreHistory.slice_scalar_bound_localDeriv_guarded_P6HS
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq : ℝ) :
    ∃ Q Λ Dcap Rrad ζ₀ Rad : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
    Dcap ≤ Rrad ∧ 0 < ζ₀ ∧
    ∀ (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount) {p : CutoffParameters} (T₀ : ℝ)
      (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        GeometricCutoffRecord K.toHistory i p),
      (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
      Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
      (∀ i : Fin K.eventCount, Perelman.PhiAlmostNonnegative
        (K.toHistory.event i).incoming.flow
        (Ico (K.time i.castSucc) (K.time i.succ) ∩ Ici T₀) phi) →
    ∀ (v : ℝ), K.time j.castSucc < v → v < K.time j.succ →
    ∀ (w : (K.stage j.castSucc).Carrier) (q ρ : ℝ),
      T₀ ≤ v - 1 / 2 / (K.toHistory.event j).incoming.flow.scalar v w →
      0 < q → q ≤ Cq * (K.toHistory.event j).incoming.flow.scalar v w →
      Λ ≤ (K.toHistory.event j).incoming.flow.scalar v w →
      Λ ≤ (K.toHistory.event j).incoming.flow.scalar v w * v →
      Λ ≤ ρ * Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w) →
    ∀ U : Set (K.stage j.castSucc).Carrier,
      (∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
        (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)), x ∈ U) →
      (∀ x ∈ U, q < (K.toHistory.event j).incoming.flow.scalar v x →
        ∃ W : SpatialCanonicalWitness ((K.toHistory.event j).incoming.flow.base.metric v)
          ε C1 C2 x, W.capTubeHasNeckChart ε) →
      (∀ (first : Fin (K.eventCount + 1)) (hfl : first ≤ j.castSucc),
        ∀ z ∈ U, ∀ (B : BackwardPointTrace K.toHistory first j.castSucc hfl z)
          (i : Fin K.eventCount) (hf : first ≤ i.castSucc) (hij : i.castSucc < j.castSucc),
        ∀ v' ∈ Ioo (K.time i.castSucc) (K.time i.succ),
          v - 1 / 2 / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
          q < (K.toHistory.event i).incoming.flow.scalar v' (B.point i.castSucc hf hij.le) →
          GuardKX_C11KX ((K.toHistory.event j).incoming.flow.scalar v) q Ctime v v' z →
          |derivWithin (fun w' => (K.toHistory.event i).incoming.flow.scalar w'
              (B.point i.castSucc hf hij.le)) (Iic v') v'| ≤
            Ctime * (K.toHistory.event i).incoming.flow.scalar v'
              (B.point i.castSucc hf hij.le) ^ 2) →
      (∀ x ∈ U, ∀ v' ∈ Ioo (K.time j.castSucc) v,
        v - 1 / 2 / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
        q < (K.toHistory.event j).incoming.flow.scalar v' x →
        GuardKX_C11KX ((K.toHistory.event j).incoming.flow.scalar v) q Ctime v v' x →
        |derivWithin (fun w' => (K.toHistory.event j).incoming.flow.scalar w' x) (Iic v') v'| ≤
          Ctime * (K.toHistory.event j).incoming.flow.scalar v' x ^ 2) →
      (∀ x ∈ U, ∀ v' ∈ Ioo (K.time j.castSucc) v,
        v - 1 / 2 / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
        q < (K.toHistory.event j).incoming.flow.scalar v' x →
        GuardKX_C11KX ((K.toHistory.event j).incoming.flow.scalar v) q Ctime v v' x →
        ∀ ξ : TangentSpace ThreeModel x,
          |scalarDifferential (K.toHistory.event j).incoming.flow v' x ξ| ≤
            Cgrad * (K.toHistory.event j).incoming.flow.scalar v' x *
              Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v' x) *
              Real.sqrt (((K.toHistory.event j).incoming.flow.base.metric v').inner x ξ ξ)) →
      (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
        v - 1 / 2 / (K.toHistory.event j).incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
        K.time j.castSucc < τ → (τ : ℝ) < K.time j.succ →
        ∀ z ∈ U, ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
              (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
              (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b)) →
      (¬ ∃ (i : Fin K.eventCount) (hT : T₀ ≤ K.time i.succ) (hl : i.succ ≤ j.castSucc)
        (B : BackwardPointTrace K.toHistory i.succ j.castSucc hl w)
        (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        B.point i.succ le_rfl hl = ((records i hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
          v - K.time i.succ ≤ 1 / 2 * (((records i hT).static b).neck.scale)⁻¹) →
      ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
          (A / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
        (K.toHistory.event j).incoming.flow.scalar v z ≤
          Q * (K.toHistory.event j).incoming.flow.scalar v w := by
  have hS : ShortSLTGuarded_C11KX.{u} (1 / 2) := shortSLT_guarded_C11KX (by norm_num)
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, hQ, hΛ, hD, hDR, hζ₀, hmain⟩ :=
    hS hεle κ C1 C2 hκ Ctime Cgrad hphi A hA Cq
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, hQ, hΛ, hD, hDR, hζ₀, ?_⟩
  intro K j p T₀ records hcan hR hord hacc hpinch v hv1 hv2 w q ρ hT₀ hq hqC hΛR hΛt hΛρ U hU hW
    hslabL hderL hgrad hnc hnot
  have hncB := K.tested_noncollapse_eventPrefix_P6M j (κ := κ) (ρ := ρ)
    (a := v - 1 / 2 / (K.toHistory.event j).incoming.flow.scalar v w) (t := v) U hnc
    (K.prefixAt_time_last _)
  exact hmain (K.prefixAt j.castSucc) (K.prefixAt_time_last _) (K.toHistory.event j).incoming
    (K.event_initial j) hv1 hv2 w q ρ hq hqC hΛR hΛt
    T₀ hT₀ (fun i hT => K.geometricCutoffRecordOfPrefix j.castSucc
      (records (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) hT))
    (fun i hT b => hcan (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) hT b) hR hord hacc U hU
    hW
    (fun i first hf z hz Btr v' hv' hwin hRv' hg =>
      hslabL _ _ z hz (K.backwardPointTraceOfPrefix j.castSucc Btr)
        (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i)
        (Fin.le_def.mpr (Fin.le_def.mp hf)) (Fin.lt_def.mpr i.isLt) v' hv' hwin hRv' hg)
    (fun x hx v' hv' hwin hRv' hg => hderL x hx v' hv' hwin hRv' hg) hgrad
    (fun i v' hv' ξ => hpinch (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) v'
      ⟨hv'.1, hT₀.trans hv'.2⟩ ξ)
    (fun v' hv' ξ => hpinch j v' ⟨hv'.1, hT₀.trans hv'.2⟩ ξ)
    (fun T hT hTs hTt haT z hz _ => hncB T hT hTs hTt haT z hz) hΛρ
    (by
      rintro ⟨i, hT, hl, Btr, b, x, h1, h2, h3⟩
      exact hnot ⟨Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i, hT,
        Fin.le_def.mpr (Fin.le_def.mp hl), K.backwardPointTraceOfPrefix j.castSucc Btr, b, x, h1,
        h2, h3⟩)

/-- consumer（G1）：guarded kernel ⇒ P6F3 kernel 形的同一结论（guard 丢掉即得旧前提的特例）。 -/
example {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq : ℝ) : ∃ Q : ℝ, 1 ≤ Q := by
  obtain ⟨Q, -, -, -, -, -, hQ, -⟩ :=
    RetainedCoreHistory.slice_scalar_bound_localDeriv_guarded_P6HS.{u} hεle κ C1 C2 hκ Ctime Cgrad
      hphi A hA Cq
  exact ⟨Q, hQ⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
