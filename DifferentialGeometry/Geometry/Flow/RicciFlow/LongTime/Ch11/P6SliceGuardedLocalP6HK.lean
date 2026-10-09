import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceDichotomyLocalP6SD

/-!
# 切片二分局部孪生的 U 侧 guard 版（A1 续 HARNACK N4-a，后缀 `_P6HK`）

SLICEDICH G1（`P6SliceDichotomyLocalP6SD`）的 L1 / L2 只在 D1（前 slab trace Dt）上带 guard
`(v − v′)·max(q, R(v, z)) ≤ c⋆`（`c⋆ = 1/(2·max(Ctime, 1))`），D2 / 梯度 / κ 在整个短窗 `[v − Bw/R(v,w), v]`
上要求——这正是 `hclosC`（U 点整窗 seed stay）被消费的原因。底层 KSWEXIT `shortSLT_guarded_C11KX` 本来只在
guard 点要 U 侧数据。本文件把 guard 一路保留到 D2 / 梯度 / κ：
* `hWBlocStarG_of_shortSLT_guarded_P6HK`（PROVED，无 binder）：WBADAPT
  `hWBlocStar_of_shortSLT_guarded_P6WA2` 逐字，D2 / 梯度 / κ 加 c⋆ guard
  （GuardKX ⇒ c⋆ 由 `mul_max_le_cstar_of_guard_P6WA2`）。
* `slice_scalar_bound_of_not_capWindowPoint_window_local_starG_P6HK`（PROVED）：L1 逐字 + guard；κ 的
  extendHorizon 形逐个 `T` 在区域 `U ∩ {guard(T, ·)}` 上调 `tested_noncollapse_eventPrefix_P6M`（guard 后缀封闭，
  GUARDWIRE G3a 同法）。
* `slice_dichotomy_late_Cg_window_localG_P6HK`（PROVED）：L2 逐字 + guard（q := Cg·R_n）。
U 侧 guard 点上的 seed stay 由 WSBASE `windowSeed_pointAnchor_C11WB` 逐点付（PROVED，无 binder），见 N4-c。
生成器 `build-logs/scratch/O-CH11-HARNACK/gen2/g2a.py`（从 tracked 源逐字切片 + 断言替换）。
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

/-- c⋆ guard 的后缀封闭（`_P6HK`）：`0 ≤ M`、`(t − a)·M ≤ c`、`a ≤ b` ⇒ `(t − b)·M ≤ c`。 -/
theorem cstar_guard_mono_P6HK {M t a b c : ℝ} (hM : 0 ≤ M) (h : (t - a) * M ≤ c) (hab : a ≤ b) :
    (t - b) * M ≤ c := by
  nlinarith

/-- **`hWBlocStar` guard 版 ⇐ guarded ShortSLT（`_P6HK`，PROVED，无 binder）**：WBADAPT
`hWBlocStar_of_shortSLT_guarded_P6WA2` 逐字，D2 / 梯度 / κ 三槽保留 KSWEXIT guard（c⋆ 形）。 -/
theorem hWBlocStarG_of_shortSLT_guarded_P6HK :
    ∀ (ε : ℝ), ε ≤ coneAccuracy → ∀ (κ C1 C2 : ℝ), 0 < κ → ∀ (Ctime Cgrad : ℝ≥0)
      (phi : ℝ → ℝ), Perelman.AdmissiblePinchingFunction phi → ∀ (A : ℝ), 0 < A →
      ∀ (Cq θ : ℝ), 0 < θ →
      ∃ Q Λ Dcap Rrad ζ₀ Rad Bw : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
      Dcap ≤ Rrad ∧ 0 < ζ₀ ∧ 0 < Bw ∧
      ∀ (H : RetainedCoreHistory.{u})
        (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount))
        {t : ℝ} (_ : H.time (Fin.last H.eventCount) < t) (_ : t < s)
          (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
        0 < q → q ≤ Cq * G.flow.scalar t y → Λ ≤ G.flow.scalar t y →
        Λ ≤ G.flow.scalar t y * t →
        ∀ {p : CutoffParameters} (T₀ : ℝ), T₀ ≤ t - Bw / G.flow.scalar t y →
        ∀ (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
          GeometricCutoffRecord H.toHistory i p),
        (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
        Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
        ∀ (U : Set (H.stage (Fin.last H.eventCount)).Carrier),
        (∀ w ∈ riemannianBallOf (G.flow.base.metric t) y (Rad / Real.sqrt (G.flow.scalar t y)),
          w ∈ U) →
        (∀ x ∈ U, q < G.flow.scalar t x →
          ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 x,
            W.capTubeHasNeckChart ε) →
        (∀ j : Fin H.eventCount,
          ∀ (first : Fin (H.eventCount + 1)) (hf : first ≤ j.castSucc),
          ∀ z ∈ U, ∀ B : BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
            (Fin.le_last first) z,
          ∀ v ∈ Ioo (H.time j.castSucc) (H.time j.succ), t - Bw / G.flow.scalar t y ≤ v →
          (t - v) * max q (G.flow.scalar t z) ≤ 1 / (2 * max (Ctime : ℝ) 1) →
          q < (H.toHistory.event j).incoming.flow.scalar v
            (B.point j.castSucc hf (Fin.le_last _)) →
          |derivWithin (fun w => (H.toHistory.event j).incoming.flow.scalar w
            (B.point j.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
            Ctime * (H.toHistory.event j).incoming.flow.scalar v
              (B.point j.castSucc hf (Fin.le_last _)) ^ 2) →
        (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
          q < G.flow.scalar v x →
          (t - v) * max q (G.flow.scalar t x) ≤
            1 / (2 * max (Ctime : ℝ) 1) →
          |derivWithin (fun w => G.flow.scalar w x) (Iic v) v| ≤ Ctime * G.flow.scalar v x ^ 2) →
        (∀ x ∈ U, ∀ v ∈ Ioo (H.time (Fin.last H.eventCount)) t, t - Bw / G.flow.scalar t y ≤ v →
          q < G.flow.scalar v x →
          (t - v) * max q (G.flow.scalar t x) ≤
            1 / (2 * max (Ctime : ℝ) 1) →
          ∀ w : TangentSpace ThreeModel x,
            |scalarDifferential G.flow v x w| ≤
              Cgrad * G.flow.scalar v x * Real.sqrt (G.flow.scalar v x) *
                Real.sqrt ((G.flow.base.metric v).inner x w w)) →
        (∀ j : Fin H.eventCount, Perelman.PhiAlmostNonnegative (H.toHistory.event j).incoming.flow
          (Ico (H.time j.castSucc) (H.time j.succ) ∩ Ici (t - Bw / G.flow.scalar t y)) phi) →
        Perelman.PhiAlmostNonnegative G.flow
          (Ico (H.time (Fin.last H.eventCount)) s ∩ Ici (t - Bw / G.flow.scalar t y)) phi →
        (∀ (T : ℝ) (hT : H.time (Fin.last H.eventCount) < T) (hTs : T < s), T ≤ t →
          t - Bw / G.flow.scalar t y ≤ T →
          let B := H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG
          let tm : Icc (0 : ℝ) B.horizon := ⟨T, H.horizon_nonneg.trans (hend ▸ hT.le), le_rfl⟩
          ∀ z ∈ U,
          (t - T) * max q (G.flow.scalar t z) ≤
            1 / (2 * max (Ctime : ℝ) 1) →
          ∀ (yy : (B.toHistory.stageAt tm).Carrier), HEq yy z →
          ∀ (b : ℝ), 0 < b → b ≤ ρ →
            B.toHistory.isParabolicallyRmControlledBall tm yy b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel (B.toHistory.stageAt tm).Carrier
                  (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                  (riemannianBallOf (B.toHistory.stageMetric (B.toHistory.activeStage tm) tm)
                    yy b)) →
        Λ ≤ ρ * Real.sqrt (G.flow.scalar t y) →
        (¬ ∃ (j : Fin H.eventCount) (hT : T₀ ≤ H.time j.succ) (hl : j.succ ≤ Fin.last H.eventCount)
          (B : BackwardPointTrace H.toHistory j.succ (Fin.last H.eventCount) hl y)
          (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
          B.point j.succ le_rfl hl = ((records j hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
            t - H.time j.succ ≤ θ * (((records j hT).static b).neck.scale)⁻¹) →
        ∀ z ∈ riemannianBallOf (G.flow.base.metric t) y (A / Real.sqrt (G.flow.scalar t y)),
          G.flow.scalar t z ≤ Q * G.flow.scalar t y := by
  intro ε hεle κ C1 C2 hκ Ctime Cgrad phi hphi A hA Cq θ hθ
  have hC1 : (1 : ℝ) ≤ ((max Ctime 1 : ℝ≥0) : ℝ) := by exact_mod_cast le_max_right Ctime 1
  have hC0 : (0 : ℝ) < ((max Ctime 1 : ℝ≥0) : ℝ) := zero_lt_one.trans_le hC1
  have hS : ShortSLTGuarded_C11KX.{u} θ := shortSLT_guarded_C11KX hθ
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, hQ, hΛ, hD, hDR, hζ, hmain⟩ :=
    hS hεle κ C1 C2 hκ (max Ctime 1) Cgrad hphi A hA Cq
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, θ, hQ, hΛ, hD, hDR, hζ, hθ, ?_⟩
  intro H hend s G hG t ht hts y q ρ hq hqy hΛ1 hΛ2 p T₀ hT₀ records hcan hRrad hord hζ' U hUy hW
    hslabs hder hgrad hpinch hpinchG hnc hρ hnot
  refine hmain H hend G hG ht hts y q ρ hq hqy hΛ1 hΛ2 T₀ hT₀ records hcan hRrad hord hζ' U hUy hW
    ?_ ?_ ?_ hpinch hpinchG ?_ hρ hnot
  · intro j first hf z hz B v hv hvw hqv hg
    have hc := mul_max_le_cstar_of_guard_P6WA2 hC0 hg
    rw [coe_max_one_P6WA2] at hc
    exact abs_le_maxOne_mul_sq_P6WA2 (hslabs j first hf z hz B v hv hvw hc hqv)
  · intro x hx v hv hvw hqv hg
    have hc := mul_max_le_cstar_of_guard_P6WA2 hC0 hg
    rw [coe_max_one_P6WA2] at hc
    exact abs_le_maxOne_mul_sq_P6WA2 (hder x hx v hv hvw hqv hc)
  · intro x hx v hv hvw hqv hg
    have hc := mul_max_le_cstar_of_guard_P6WA2 hC0 hg
    rw [coe_max_one_P6WA2] at hc
    exact hgrad x hx v hv hvw hqv hc
  · intro T hT hTs hTt hTw _ _ z hz hg
    have hc := mul_max_le_cstar_of_guard_P6WA2 hC0 hg
    rw [coe_max_one_P6WA2] at hc
    exact hnc T hT hTs hTt hTw z hz hc

/-- **L1 guard 版（`_P6HK`，PROVED，无 binder）**：SLICEDICH L1
`slice_scalar_bound_of_not_capWindowPoint_window_local_star_P6SD` 逐字，D2 / 梯度 / κ 加 c⋆ guard。 -/
theorem RetainedCoreHistory.slice_scalar_bound_of_not_capWindowPoint_window_local_starG_P6HK
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq : ℝ) :
    ∃ Q Λ Dcap Rrad ζ₀ Rad Bw : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
    Dcap ≤ Rrad ∧ 0 < ζ₀ ∧ 0 < Bw ∧
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
      T₀ ≤ v - Bw / (K.toHistory.event j).incoming.flow.scalar v w →
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
      (∀ i : Fin (K.prefixAt j.castSucc).eventCount,
        ∀ (first : Fin ((K.prefixAt j.castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
        ∀ z ∈ U, ∀ Btr : BackwardPointTrace (K.prefixAt j.castSucc).toHistory first
          (Fin.last (K.prefixAt j.castSucc).eventCount) (Fin.le_last first) z,
        ∀ v' ∈ Ioo ((K.prefixAt j.castSucc).time i.castSucc)
          ((K.prefixAt j.castSucc).time i.succ),
        v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
        (v - v') * max q ((K.toHistory.event j).incoming.flow.scalar v z) ≤
          1 / (2 * max (Ctime : ℝ) 1) →
        q < ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar v'
          (Btr.point i.castSucc hf (Fin.le_last _)) →
        |derivWithin (fun s => ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar s
          (Btr.point i.castSucc hf (Fin.le_last _))) (Iic v') v'| ≤
          Ctime * ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar v'
            (Btr.point i.castSucc hf (Fin.le_last _)) ^ 2) →
      (∀ x ∈ U, ∀ v' ∈ Ioo (K.time j.castSucc) v,
        v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
        q < (K.toHistory.event j).incoming.flow.scalar v' x →
        (v - v') * max q ((K.toHistory.event j).incoming.flow.scalar v x) ≤
          1 / (2 * max (Ctime : ℝ) 1) →
        |derivWithin (fun s => (K.toHistory.event j).incoming.flow.scalar s x) (Iic v') v'| ≤
          Ctime * (K.toHistory.event j).incoming.flow.scalar v' x ^ 2) →
      (∀ x ∈ U, ∀ v' ∈ Ioo (K.time j.castSucc) v,
        v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
        q < (K.toHistory.event j).incoming.flow.scalar v' x →
        (v - v') * max q ((K.toHistory.event j).incoming.flow.scalar v x) ≤
          1 / (2 * max (Ctime : ℝ) 1) →
        ∀ ξ : TangentSpace ThreeModel x,
          |scalarDifferential (K.toHistory.event j).incoming.flow v' x ξ| ≤
            Cgrad * (K.toHistory.event j).incoming.flow.scalar v' x *
              Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v' x) *
              Real.sqrt (((K.toHistory.event j).incoming.flow.base.metric v').inner x ξ ξ)) →
      (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
        v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
        K.time j.castSucc < τ → (τ : ℝ) < K.time j.succ →
        ∀ z ∈ U,
        (v - τ) * max q ((K.toHistory.event j).incoming.flow.scalar v z) ≤
          1 / (2 * max (Ctime : ℝ) 1) →
        ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
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
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hD, hDR, hζ₀, hBw, hmain⟩ :=
    hWBlocStarG_of_shortSLT_guarded_P6HK.{u} ε hεle κ C1 C2 hκ Ctime Cgrad phi hphi A hA Cq
      (1 / 2) (by norm_num)
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hD, hDR, hζ₀, hBw, ?_⟩
  intro K j p T₀ records hcan hR hord hacc hpinch v hv1 hv2 w q ρ hT₀ hq hqC hΛR hΛt hΛρ U hU hW
    hslabs hder hgrad hnc hnot
  refine hmain (K.prefixAt j.castSucc) (K.prefixAt_time_last _) (K.toHistory.event j).incoming
    (K.event_initial j) hv1 hv2 w q ρ hq hqC hΛR hΛt
    T₀ hT₀ (fun i hT => K.geometricCutoffRecordOfPrefix j.castSucc
      (records (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) hT))
    (fun i hT b => hcan (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) hT b) hR hord hacc U hU
    hW hslabs hder hgrad
    (fun i v' hv' ξ => hpinch (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) v'
      ⟨hv'.1, hT₀.trans hv'.2⟩ ξ)
    (fun v' hv' ξ => hpinch j v' ⟨hv'.1, hT₀.trans hv'.2⟩ ξ) ?_ hΛρ
    (by
      rintro ⟨i, hT, hl, Btr, b, x, h1, h2, h3⟩
      exact hnot ⟨Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i, hT,
        Fin.le_def.mpr (Fin.le_def.mp hl), K.backwardPointTraceOfPrefix j.castSucc Btr, b, x, h1,
        h2, h3⟩)
  intro T hT hTs hTt hTa _ _ z hz hg
  have hncT := K.tested_noncollapse_eventPrefix_P6M j (κ := κ) (ρ := ρ) (a := T) (t := v)
    {x | x ∈ U ∧ (v - T) * max q ((K.toHistory.event j).incoming.flow.scalar v x) ≤
      1 / (2 * max (Ctime : ℝ) 1)}
    (fun τ h1 h2 h3 h4 z' hz' => hnc τ (hTa.trans h1) h2 h3 h4 z' hz'.1
      (cstar_guard_mono_P6HK (hq.le.trans (le_max_left _ _)) hz'.2 h1))
    (K.prefixAt_time_last _)
  exact hncT T hT hTs hTt le_rfl z ⟨hz, hg⟩

/-- **L2 guard 版（`_P6HK`，PROVED，无 binder）**：SLICEDICH L2
`slice_dichotomy_late_Cg_window_local_P6SD` 逐字，U 侧梯度 / κ / D2 合取加 c⋆ guard
`(v − v′)·max(Cg·R_n, R(v, x)) ≤ c⋆`（与 D1 同形）。 -/
theorem RetainedCoreHistory.slice_dichotomy_late_Cg_window_localG_P6HK
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0) (Cg : ℝ)
    (hCg : 0 < Cg) {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc) :
    ∃ Cbirth : ℝ, 0 < Cbirth ∧ ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
    Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
    ∃ (Λ Rad Bw Rmin ζmin δ₀ : ℝ) (m₀ : ℕ), 1 ≤ Λ ∧ 0 < Bw ∧ 0 < ζmin ∧ 0 < δ₀ ∧
    ∀ (K : RetainedCoreHistory.{u}) {p : CutoffParameters} (T₀ : ℝ)
      (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        GeometricCutoffRecord K.toHistory i p),
      (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
      Rmin ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζmin →
      (∀ i : Fin K.eventCount, Perelman.PhiAlmostNonnegative
        (K.toHistory.event i).incoming.flow
        (Ico (K.time i.castSucc) (K.time i.succ) ∩ Ici T₀) phi) →
    ∀ {pF : CutoffParameters}, (∀ i, GeometricCutoffRecord K.toHistory i pF) →
    ∀ δbound : ℝ, (∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        pF.delta (K.time i.succ) ≤ δbound) →
      δbound ≤ δ₀ →
    ∀ (qcan a₀ : ℝ), 0 < qcan →
      (∀ x, InFixedHamiltonIveyRegion (K.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (K.initialMetric 0) x) →
      (∀ i hT b, qcan ≤ Cbirth * ((records i hT).static b).neck.scale ∧
        1 ≤ a₀ * ((records i hT).static b).neck.scale) →
    ∀ (j : Fin K.eventCount), K.EventSlabsDerivative Ctime qcan j.castSucc →
    ∀ v : ℝ, K.time j.castSucc < v → v < K.time j.succ →
      (K.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan v →
    ∀ (Rn ρ : ℝ), 0 < Rn → Λ ≤ Rn → Λ ≤ Rn * v → Λ ≤ ρ * Real.sqrt Rn →
      T₀ ≤ v - Bw / Rn →
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
          Cg * Rn < (K.toHistory.event j).incoming.flow.scalar v x →
          ∃ W : SpatialCanonicalWitness ((K.toHistory.event j).incoming.flow.base.metric v)
            ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
        (∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
              (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
          ∀ v' ∈ Ioo (K.time j.castSucc) v,
          v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
          Cg * Rn < (K.toHistory.event j).incoming.flow.scalar v' x →
          (v - v') * max (Cg * Rn) ((K.toHistory.event j).incoming.flow.scalar v x) ≤
            1 / (2 * max (Ctime : ℝ) 1) →
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
          (v - τ) * max (Cg * Rn)
              ((K.toHistory.event j).incoming.flow.scalar v z) ≤
                1 / (2 * max (Ctime : ℝ) 1) →
          ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
                (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
                (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b)) ∧
        (∀ x ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
              (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
          ∀ v' ∈ Ioo (K.time j.castSucc) v,
          v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
          Cg * Rn < (K.toHistory.event j).incoming.flow.scalar v' x →
          (v - v') * max (Cg * Rn) ((K.toHistory.event j).incoming.flow.scalar v x) ≤
            1 / (2 * max (Ctime : ℝ) 1) →
          |derivWithin (fun s => (K.toHistory.event j).incoming.flow.scalar s x) (Iic v') v'| ≤
            Ctime * (K.toHistory.event j).incoming.flow.scalar v' x ^ 2) ∧
        (∀ i : Fin (K.prefixAt j.castSucc).eventCount,
          ∀ (first : Fin ((K.prefixAt j.castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
          ∀ z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric v) w
              (Rad / Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v w)),
          ∀ Btr : BackwardPointTrace (K.prefixAt j.castSucc).toHistory first
            (Fin.last (K.prefixAt j.castSucc).eventCount) (Fin.le_last first) z,
          ∀ v' ∈ Ioo ((K.prefixAt j.castSucc).time i.castSucc)
            ((K.prefixAt j.castSucc).time i.succ),
          v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
          (v - v') * max (Cg * Rn) ((K.toHistory.event j).incoming.flow.scalar v z) ≤
            1 / (2 * max (Ctime : ℝ) 1) →
          Cg * Rn < ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar v'
            (Btr.point i.castSucc hf (Fin.le_last _)) →
          |derivWithin (fun s =>
              ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf (Fin.le_last _))) (Iic v') v'| ≤
            Ctime * ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf (Fin.le_last _)) ^ 2)) →
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
  obtain ⟨Cbirth, hCbirth, hCWP⟩ := RetainedCoreHistory.capWindow_branch_late_P6L3.{u} Ctime
  refine ⟨Cbirth, hCbirth, fun A Dd hA hDd => ?_⟩
  have hAB : 0 < 2 * Dd * Real.sqrt A + 1 := by positivity
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hD, -, hζ₀, hBw, hmain⟩ :=
    RetainedCoreHistory.slice_scalar_bound_of_not_capWindowPoint_window_local_starG_P6HK hεle κ
      C1 C2
      hκ Ctime Cgrad hphi (2 * Dd * Real.sqrt A + 1) hAB Cg
  have hDpos : 0 < Dcap := StandardCap.transitionEnd_pos.trans hD
  have hDD₂ : Dcap < Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) := by
    have : 0 ≤ 2 * Dd * Lc * Real.sqrt (2 * A) := by positivity
    linarith
  obtain ⟨Rr, -, m₀, -, ζ₁, δ₀, hζ₁, hδ₀, hcap⟩ :=
    hCWP Dcap (Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1)) η₃ hDpos hDD₂ hη₃
  refine ⟨Q, Dcap, Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1), by linarith, le_rfl, Λ, Rad,
    Bw, max Rr Rrad, min ζ₀ ζ₁, δ₀, max m₀ 2, hΛ, hBw, lt_min hζ₀ hζ₁, hδ₀, ?_⟩
  intro K p T₀ records hcan hRad hord hacc hpinch pF recordsF δb hdelta hδ qcan a₀ hq0 hHI hlow
    hbirth j hslab v hv1 hv2 hder Rn ρ hRn hΛRn hΛv hΛρ hT₀ k hk z sk sj hs d1 hzd zj hzj hU
  subst hk
  obtain rfl := eq_of_heq hs
  obtain rfl := eq_of_heq hzj
  have hv0 : 0 ≤ v := (K.toHistory.time_nonneg _).trans hv1.le
  refine ⟨fun w => ∃ (i : Fin K.eventCount) (hT : T₀ ≤ K.time i.succ) (hl : i.succ ≤ j.castSucc)
      (B : BackwardPointTrace K.toHistory i.succ j.castSucc hl w)
      (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      B.point i.succ le_rfl hl = ((records i hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
        v - K.time i.succ ≤ 1 / 2 * (((records i hT).static b).neck.scale)⁻¹, ?_, ?_⟩
  · intro w hzw hncw hRw x hx
    rw [ObservedHistory.stageMetric_castSucc_apply] at hzd hzw hRw hx ⊢
    have hw : riemannianEDistOf ((K.toHistory.event j).incoming.flow.base.metric v) sk w ≤
        d1 + ENNReal.ofReal (Dd / Real.sqrt Rn) :=
      (riemannianEDistOf_triangle _ _ _ _).trans (add_le_add hzd hzw.le)
    obtain ⟨h1, h4, h5, h6, h7⟩ := hU w hw hzw hRw
    have hRw2 : Rn ≤ (K.toHistory.event j).incoming.flow.scalar v w := hRw
    have hρ0 : 0 < ρ := by
      by_contra hneg
      have : ρ * Real.sqrt Rn ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) (Real.sqrt_nonneg _)
      linarith
    have hT₀w : T₀ ≤ v - Bw / (K.toHistory.event j).incoming.flow.scalar v w :=
      hT₀.trans (by linarith [div_le_div_of_nonneg_left hBw.le hRn hRw2])
    exact hmain K j T₀ records hcan ((le_max_right _ _).trans hRad) ((le_max_right _ _).trans hord)
      (hacc.trans (min_le_left _ _)) hpinch v hv1 hv2 w (Cg * Rn) ρ
      hT₀w (mul_pos hCg hRn) (mul_le_mul_of_nonneg_left hRw2 hCg.le) (hΛRn.trans hRw)
      (hΛv.trans (mul_le_mul_of_nonneg_right hRw hv0))
      (hΛρ.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hRw) hρ0.le)) _ (fun _ h => h) h1
      h7 h6 h4 h5 hncw x hx
  · intro w _ hcw
    exact hcap K records hcan ((le_max_left _ _).trans hRad) ((le_max_left _ _).trans hord)
      (hacc.trans (min_le_right _ _)) recordsF δb hdelta hδ qcan a₀ hq0 hHI hlow hbirth
      j hslab v hv1 hv2 hder w hcw

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
