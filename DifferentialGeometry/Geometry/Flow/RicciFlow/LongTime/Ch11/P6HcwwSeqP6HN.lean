import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HcwwUniformP6HN
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedBufferedCanonical
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalToleranceMonotone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessProjection

/-!
# (CWW) witness `hcww`，年龄 `θ n → 1` 形（O-CH11-HNOT-LOCALDT / HNOT-A3 G7，后缀 `_P6HN`）

G6 `capWindow_trace_spatialWitness_theta_P6HN` 的常数 `Cs = Cs(ε, Θ)` 依赖年龄上界 `Θ`。本文件把 `Cs` 提到
`Θ` 之前（对 `θcap → 1` 一致），不加 stage-age 前提：
* 年轻 cap（`T = q·(t − tᵢ) ≤ Θ₃`，`Θ₃ = 2τ*/(c₀ + 2τ*)`，`τ* = max τQ δ⁻¹`）：G6 在固定 `Θ₃` 处。
* 老 cap（`Θ₃ ≤ T ≤ θcap`）：窗口流 `S`（`closed 0 T` 上的 `SolutionOn`，P6LL late comparison）在 `(z, T)` 处的
  `OrientedWitness`（`exists_uniform_orientedWitness_of_standard_close_endpoint`；cap 年龄
  `τQ ≤ T·R_S` 由 `exists_standard_scalar_lower_bound` 与 `le_mul_of_half_standard_scalar_lower` 给），
  直接在 `S` 上调一般流形版 `exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts`
  （正则窗 `Ioo (T − (δR_S)⁻¹) T ⊆ Ioo 0 T` 只要 `δ⁻¹ ≤ T·R_S`）——不把 witness 推到 `Gk.flow`，
  故 UCWC:29 的 stage-age 条件 `τmin ≤ R·(t − time k)` 不出现；`toSpatial` 后经 G6 的
  `pushforwardOfInjectiveULift` + `scaleMetric q⁻¹` 推回 `g(t)`。
主定理：`capWindow_trace_spatialWitness_P6HN`（单 history，`Cs` 在 `Θ` 之前）、
`hcww_of_uniformCapWindow_seq_P6HN`（diagonal，年龄序列 `θ n < 1`，结论 = G2 主形 `hcww` 槽逐字）、
`hnotK_of_capWindow_seq_P6HN`（G2 主形 + 上一条：θ n 形 hnotK 不再带 `hcww` binder）。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance capWindowSigmaCompactP6HN7 (D : ℝ) :
    SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

namespace RetainedCoreHistory

universe u

/-- **cap-window trace 点的 spatial witness，`Cs` 在年龄上界 `Θ` 之前（`_P6HN`，PROVED）**。 -/
theorem capWindow_trace_spatialWitness_P6HN {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ (Θ : ℝ), 0 < Θ → Θ < 1 →
    ∀ C : ℝ≥0, ∃ Cbirth : ℝ, 0 < Cbirth ∧ ∀ D : ℝ, 0 < D →
    ∃ R : ℝ, D + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧ ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ 0 < δ₀ ∧
    ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters} {T₀ : ℝ}
      (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        GeometricCutoffRecord H.toHistory i p),
      (∀ i hi b, ((records i hi).static b).hasCanonicalWindow) →
      R ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
    ∀ {pF : CutoffParameters}, (∀ i, GeometricCutoffRecord H.toHistory i pF) →
    ∀ δbound : ℝ, (∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        pF.delta (H.time i.succ) ≤ δbound) →
      δbound ≤ δ₀ →
    ∀ (qcan a₀ θcap : ℝ), 0 < qcan → θcap ≤ Θ →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative C qcan k →
    ∀ t : ℝ, H.time k < t → t < s → Gk.DerivativeBoundBefore C qcan t →
    ∀ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ k)
      (y : (H.stage k).Carrier)
      (A : BackwardPointTrace H.toHistory j.succ k hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hj).static b).window x →
      t - H.time j.succ ≤ θcap * (((records j hj).static b).neck.scale)⁻¹ →
      ‖x.val‖ < D + 1 →
      qcan ≤ Cbirth * ((records j hj).static b).neck.scale →
      1 ≤ a₀ * ((records j hj).static b).neck.scale →
    ∀ C1 C2 : ℝ, Cs ≤ C1 → Cs ≤ C2 →
      ∃ W : SpatialCanonicalWitness (Gk.flow.base.metric t) ε C1 C2 y,
        W.capTubeHasNeckChart ε := by
  obtain ⟨Cb, δb, hCb, hδb, -, hbuf⟩ :=
    exists_uniform_windowed_bufferedCanonical_with_cap_neck_charts.{0} hε hε' 1
  set δ := min δb (1 / 4) with hδdef
  have hδ : 0 < δ := lt_min hδb (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨τQ, hτQ, hL6⟩ := exists_uniform_orientedWitness_of_standard_close_endpoint hδ hδ1
  obtain ⟨c₀, hc₀, hQlow⟩ := exists_standard_scalar_lower_bound
  set τs := max τQ δ⁻¹ with hτsdef
  have hτs : 0 < τs := hτQ.trans_le (le_max_left _ _)
  set Θ₃ := 2 * τs / (c₀ + 2 * τs) with hΘ₃def
  have hΘ₃ : 0 < Θ₃ := by positivity
  have hΘ₃1 : Θ₃ < 1 := by rw [hΘ₃def, div_lt_one (by positivity)]; linarith
  obtain ⟨Cy, hCy, hY⟩ := capWindow_trace_spatialWitness_theta_P6HN.{u} hε hε' Θ₃ hΘ₃ hΘ₃1
  refine ⟨max Cb Cy, hCb.trans (le_max_left _ _), fun Θ hΘ hΘ1 C => ?_⟩
  obtain ⟨eta, heta, hlower⟩ := exists_uniform_standard_metric_scalar_lower_comparison Θ hΘ.le hΘ1
  obtain ⟨Λ, hΛ, hplace⟩ := StandardSolution.exists_window_ball_placement (Θ := Θ) hΘ1
  set L := 4 * Cb + 1 with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hΛL : 0 ≤ Λ * (L + 1) := by positivity
  obtain ⟨P, Creset, Cb1, -, -, hCb1, hbridge⟩ :=
    exists_standard_comparison_of_cap_window_trace_late_P6LL.{u} Θ C hΘ hΘ1
  obtain ⟨Cb2, hCb2, hY2⟩ := hY C
  refine ⟨min Cb1 Cb2, lt_min hCb1 hCb2, fun D hD => ?_⟩
  obtain ⟨DW, NW, eW, hrD, heW, hwit⟩ := hL6 Θ (D + 1 + Λ * (L + 1)) hΘ1
  obtain ⟨R1, hR1, m1, hm1, ζ1, δ1, hζ1, -, hδ1', hbr⟩ :=
    hbridge DW eW eta (by linarith) heW heta NW
  obtain ⟨R2, hR2, m2, hm2, ζ2, δ2, hζ2, hδ2, hyc⟩ := hY2 D hD
  refine ⟨max R1 R2, by linarith [le_max_right R1 R2], max m1 m2, hm1.trans (le_max_left _ _),
    min ζ1 ζ2, min δ1 δ2, lt_min hζ1 hζ2, lt_min hδ1' hδ2, ?_⟩
  intro H p T₀ records hcan hrad hord hacc pF recordsF δbound hdelta hδb qcan a₀ θcap hqcan hθ
    hHI hlow k s Gk hGk hderiv t hkt hts hcur j hj hl y A b x hanchor hage hxD hbirth haq
    C1 C2 hC1 hC2
  set q := ((records j hj).static b).neck.scale with hqdef
  have hq : 0 < q := ((records j hj).static b).neck.scale_pos
  have hbirth1 : qcan ≤ Cb1 * q :=
    hbirth.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hq.le)
  have hbirth2 : qcan ≤ Cb2 * q :=
    hbirth.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hq.le)
  by_cases hyng : t - H.time j.succ ≤ Θ₃ * q⁻¹
  · exact hyc H records hcan ((le_max_right _ _).trans hrad) ((le_max_right _ _).trans hord)
      (hacc.trans (min_le_right _ _)) recordsF δbound hdelta (hδb.trans (min_le_right _ _))
      qcan a₀ Θ₃ hqcan le_rfl hHI hlow k s Gk hGk hderiv t hkt hts hcur j hj hl y A b x
      hanchor hyng hxD hbirth2 haq C1 C2 ((le_max_right _ _).trans hC1)
      ((le_max_right _ _).trans hC2)
  have hxW : ‖x.val‖ < DW + 1 := by linarith
  obtain ⟨G, L', hG, -, hL, -, -, -, -, -, -, -, z, hzx, hy, Ξ, hΞs, -, hΞmark, hΞ, gflow, S,
      -, hS2, hS3, -, hS5, -, -, Q, -, hclose⟩ :=
    hbr H records hcan ((le_max_left _ _).trans hrad) ((le_max_left _ _).trans hord)
      (hacc.trans (min_le_left _ _)) recordsF δbound hdelta (hδb.trans (min_le_left _ _))
      qcan a₀ θcap hqcan hθ hHI hlow k s Gk hGk hderiv t hkt hts hcur
      j hj hl y A b x hanchor hage hxW hbirth1 haq
  have hyz : (Ξ z).val.val = y := congrArg Subtype.val hΞmark
  have hba : H.time j.succ ≤ H.time k := H.time_strictMono.monotone hl
  set T := q * (t - H.time j.succ) with hTdef
  have hjt : H.time j.succ < t := hba.trans_lt hkt
  have hT0 : 0 ≤ T := mul_nonneg hq.le (by linarith)
  have hTθ : T ≤ θcap := by
    have h1 := mul_le_mul_of_nonneg_left hage hq.le
    rwa [mul_comm θcap, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] at h1
  have hTΘ : T ∈ Icc 0 Θ := ⟨hT0, hTθ.trans hθ⟩
  have hT1 : T < 1 := hTΘ.2.trans_lt hΘ1
  have hTΘ₃ : Θ₃ ≤ T := by
    have h1 := mul_le_mul_of_nonneg_left (not_le.mp hyng).le hq.le
    rwa [mul_comm Θ₃, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] at h1
  have hTmem : T ∈ Icc 0 T := ⟨hT0, le_rfl⟩
  have htT : H.time j.succ + T / q = t := by
    rw [hTdef, mul_div_cancel_left₀ _ hq.ne']
    ring
  have hST := H.capWindow_flow_metric_eq Gk hl hΞ hq hG hL hS2 hS5 T hTmem
    (by rw [htT]; linarith)
  rw [htT] at hST
  have hΦ := H.toHistory.isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val j.succ k hl G hΞ
  have hinj := H.toHistory.injective_backwardSurvivorIncomingDomain_val_val j.succ k hl G
    hΞs.isEmbedding.injective
  have hclT := hclose T hTmem
  have hlow' : ∀ y' : standardCapWindow DW,
      (∀ v : TangentSpace (𝓡 3) y',
        (1 / 2) * ((Q.val.metric T).restrictOpen (standardCapWindow DW)).inner y' v v ≤
          (S.base.metric T).inner y' v v) ∧
      (1 / 2) * metricScalarAt ((Q.val.metric T).restrictOpen (standardCapWindow DW)) y' ≤
        metricScalarAt (S.base.metric T) y' := fun y' =>
    hlower Q _ _ T hTΘ y' fun i hi => (hclT.2 i hi y').le
  have hlowz := (hlow' z).2
  rw [metricScalarAt_restrictOpen] at hlowz
  have hτ : τs ≤ T * S.scalar T z :=
    le_mul_of_half_standard_scalar_lower hτs.le hc₀ hT1 (hQlow Q z.val T ⟨hT0, hT1⟩) hlowz hTΘ₃
  have hz : ‖z.val‖ < D + 1 := by rw [hzx]; exact hxD
  have hOW := hwit Q T hT0 hTΘ.2 S hS3 (fun τ hτ' => (hclose τ hτ').1)
    ((H.stage k).orientation.pullback hΦ) z (by linarith) ((le_max_left _ _).trans hτ)
  have hQ1 : 1 ≤ metricScalarAt (Q.val.metric T) z.val :=
    Q.val.one_le_scalar T (Q.mem_domain_of_mem_Icc hΘ1 hTΘ) z.val
  have hRS : 1 / 2 ≤ metricScalarAt (S.base.metric T) z := by
    linarith only [hlowz, hQ1]
  have hRS' : 0 < S.scalar T z := lt_of_lt_of_le (by norm_num) hRS
  have hreg : Ioo (T - (δ * S.scalar T z)⁻¹) T ⊆
      (RealTimeInterval.closed 0 T hT0).regular := by
    have hinv : (δ * S.scalar T z)⁻¹ ≤ T := by
      rw [inv_le_iff_one_le_mul₀ (mul_pos hδ hRS')]
      have h1 : δ⁻¹ ≤ T * S.scalar T z := (le_max_right _ _).trans hτ
      have h2 := mul_le_mul_of_nonneg_left h1 hδ.le
      rw [mul_inv_cancel₀ hδ.ne'] at h2
      linarith only [h2]
    intro v hv
    exact ⟨by linarith only [hv.1, hinv], hv.2⟩
  obtain ⟨B, hB⟩ := hbuf standardModelKappa (standardCapWindow DW) _ S hS3 δ
    ((H.stage k).orientation.pullback hΦ) z T (min_le_left _ _) hreg hOW
  set K := B.canonicalWitnessMono B.tolerance_lt.le hε' with hKdef
  have hK : K.capTubeHasNeckChart ε := hB.mono_eps B.tolerance_lt.le hε'
  have hzr : ‖(z : EuclideanSpace ℝ (Fin 3))‖ + Λ * (L + 1) < DW + 1 := by linarith
  obtain ⟨hcpt, -⟩ := hplace DW L z hL0 hzr Q T hTΘ (S.base.metric T) (fun y' v => (hlow' y').1 v)
  subst hyz
  have key : ∃ W : SpatialCanonicalWitness (localPullMetric (scaleMetric q hq
      (Gk.flow.base.metric t)) (fun v => (Ξ v).val.val) hΦ) ε Cb Cb z,
      W.capTubeHasNeckChart ε ∧ 2 * W.radius < L := by
    rw [← hST]
    refine ⟨K.toSpatial, K.capTubeHasNeckChart_toSpatial hK, ?_⟩
    have hs : 1 / 2 ≤ Real.sqrt (metricScalarAt (S.base.metric T) z) := by
      have h := Real.sqrt_le_sqrt (show (1 / 2 : ℝ) ^ 2 ≤
        metricScalarAt (S.base.metric T) z by linarith only [hRS])
      rwa [Real.sqrt_sq (by norm_num)] at h
    have hr0 : 0 ≤ K.toSpatial.radius :=
      (inv_nonneg.mpr (Real.sqrt_nonneg _)).trans K.toSpatial.radius_lower
    have hup := K.toSpatial.radius_upper
    rw [le_div_iff₀ (Real.sqrt_pos.mpr (by linarith only [hRS]))] at hup
    linarith only [mul_le_mul_of_nonneg_left hs hr0, hup, hLdef]
  obtain ⟨W, hW, hWr⟩ := key
  rw [hST] at hcpt
  have hscale : scaleMetric q⁻¹ (inv_pos.mpr hq) (scaleMetric q hq (Gk.flow.base.metric t)) =
      Gk.flow.base.metric t :=
    SmoothRiemannianMetric.ext_inner fun v w₁ w₂ => by
      simp only [scaleMetric_inner]
      field_simp
  have hC1' : Cb ≤ C1 := (le_max_left _ _).trans hC1
  have hC2' : Cb ≤ C2 := (le_max_left _ _).trans hC2
  rw [← hscale]
  exact ⟨((W.pushforwardOfInjectiveULift hΦ hinj hWr hcpt).scaleMetric q⁻¹
      (inv_pos.mpr hq)).enlargeConstants hC1' hC2',
    (SpatialCanonicalWitness.capTubeHasNeckChart.scaleMetric q⁻¹ (inv_pos.mpr hq)
      (hW.pushforwardOfInjectiveULift hΦ hinj hWr hcpt)).enlarge_constants hC1' hC2'⟩

/-- **`hcww_of_uniformCapWindow_seq_P6HN`（PROVED，年龄序列 `θ n < 1` 形）**：diagonal 序列（`D = n+1`），
结论 = G2 主形 `hnotK_of_capWindowWitness_theta_P6HN` 的 `hcww` 槽逐字（任意 `θ n < 1`，含
`θ n = 1 − 1/(n+2)`）。常数 `Cs` 只依赖 `ε`，在 `θ` 与 `C` 之前；birth 尺度 `Cb n` 与 persistence 参数逐 `n`
（同 G2 主形）。导数前提仍是前缀 Dt。 -/
theorem hcww_of_uniformCapWindow_seq_P6HN {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ (C : ℝ≥0) {θ : ℕ → ℝ}, (∀ n, θ n < 1) →
    ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n) ∧ (∀ n : ℕ, ((n : ℝ) + 1) + 1 < Rn n) ∧ (∀ n, 0 < ζ n) ∧
      (∀ n, 0 < δ₀ n) ∧
    ∀ {C1' C2' : ℝ}, Cs ≤ C1' → Cs ≤ C2' →
    ∀ {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ},
      (∀ n, (K n).time (j n).castSucc < t n) → (∀ n, t n < (K n).time (j n).succ) →
    ∀ {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)},
      (∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) → ∀ {a₀ : ℝ},
      (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ δ₀ n) →
      (∀ n, (p n).modelAccuracy ≤ ζ n) → (∀ n, Rn n ≤ (p n).modelRadius) →
      (∀ n, m₀ n ≤ (p n).modelOrder) → (∀ n, 0 < Q n) →
      (∀ n, (K n).EventSlabsDerivative C (Q n) (j n).castSucc) →
      (∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore C (Q n) (t n)) →
      (∀ n i hi b, i.succ ≤ (j n).castSucc →
        t n - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        Q n ≤ Cb n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n i hi b, i.succ ≤ (j n).castSucc →
        t n - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
    ∀ {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
      (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier),
      (∀ n, (σ n : ℝ) = t n) → (∀ n, HEq (y n) (yG n)) →
    ∀ n, (∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹) →
      ∃ W : SpatialCanonicalWitness ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n)) ε C1' C2' (y n), W.capTubeHasNeckChart ε := by
  obtain ⟨Cs, hCs, hall⟩ := capWindow_trace_spatialWitness_P6HN.{u} hε hε'
  refine ⟨Cs, hCs, fun C θ hθ => ?_⟩
  choose Cb hCb hD using fun n : ℕ =>
    hall (max (θ n) (1 / 2)) (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
      (max_lt (hθ n) (by norm_num)) C
  choose Rn hRn m₀ _hm₀ ζ δ₀ hζ hδ h4 using fun n : ℕ => hD n ((n : ℝ) + 1) (by positivity)
  refine ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hRn, hζ, hδ, ?_⟩
  intro C1' C2' hC1 hC2 K j t hjt htj Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF hacc hrad hord
    hQ hder hcur hbirth hbirthA yG σ y hσ hyG n hC
  obtain ⟨i, hi, hl, A, b, x, hx, hxn, hage⟩ := hC
  have hjt' : (K n).time (j n).castSucc < (σ n : ℝ) := by
    rw [hσ n]
    exact hjt n
  have htj' : (σ n : ℝ) < (K n).time (j n).succ := by
    rw [hσ n]
    exact htj n
  have hact : (K n).toHistory.activeStage (σ n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6X (j n) (σ n) hjt'.le htj'
  have hW := h4 n (K n) (recordsK n) (hcanK n) (hrad n) (hord n) (hacc n) (recordsF n) (δ₀ n)
    (hδF n) le_rfl (Q n) a₀ (θ n) (hQ n) (le_max_left _ _) (fun x => (hHI n x).1)
    (fun x => (hHI n x).2)
    (j n).castSucc ((K n).time (j n).succ) ((K n).toHistory.event (j n)).incoming
    ((K n).event_initial (j n)) (hder n) (t n) (hjt n) (htj n) (hcur n) i hi hl (yG n) A b x hx
    hage hxn (hbirth n i hi b hl hage) (hbirthA n i hi b hl hage) C1' C2' hC1 hC2
  have hW' : ∃ W : SpatialCanonicalWitness
      (((K n).toHistory.event (j n)).incoming.flow.base.metric (σ n : ℝ)) ε C1' C2' (yG n),
      W.capTubeHasNeckChart ε := by
    rw [hσ n]
    exact hW
  exact (K n).spatialWitness_stage_of_incoming_P6HN (j n) hact.symm (σ n) (y n) (yG n) (hyG n) hW'

/-- **`hnotK_of_capWindow_seq_P6HN`（年龄序列 `θ n < 1` 形 hnotK，(CWW) 已付）**：G2 主形
`hnotK_of_capWindowWitness_theta_P6HN` 的 `hcww` binder 由 `hcww_of_uniformCapWindow_seq_P6HN` 付清；
`Ctime₀`、`Cs` 在 `C, θ` 之前，逐 `n` 参数取两边的 min / max。剩余前提 = 前缀 Dt 两条、birth 尺度两条、
records 精度 / 半径 / 阶、late δ、`hsel`（与 G2 主形同）。 -/
theorem hnotK_of_capWindow_seq_P6HN {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ (Ctime₀ : ℝ≥0) (Cs : ℝ), 0 < Ctime₀ ∧ 1 ≤ Cs ∧
    ∀ (C : ℝ≥0) {θ : ℕ → ℝ}, (∀ n, θ n < 1) →
    ∃ (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n, 0 < Cb n) ∧ (∀ n : ℕ, ((n : ℝ) + 1) + 1 < Rn n) ∧ (∀ n, 0 < ζ n) ∧
      (∀ n, 0 < δ₀ n) ∧
    ∀ {C1' C2' : ℝ} {Ctime' : ℝ≥0}, Cs ≤ C1' → Cs ≤ C2' → Ctime₀ ≤ Ctime' →
    ∀ {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ},
      (∀ n, (K n).time (j n).castSucc < t n) → (∀ n, t n < (K n).time (j n).succ) →
    ∀ {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
      {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (p n)},
      (∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n)) → ∀ {a₀ : ℝ},
      (∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((K n).initialMetric 0) x) →
      (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        (pF n).delta ((K n).time i.succ) ≤ δ₀ n) →
      (∀ n, (p n).modelAccuracy ≤ ζ n) → (∀ n, Rn n ≤ (p n).modelRadius) →
      (∀ n, m₀ n ≤ (p n).modelOrder) → (∀ n, 0 < Q n) →
      (∀ n, (K n).EventSlabsDerivative C (Q n) (j n).castSucc) →
      (∀ n, ((K n).toHistory.event (j n)).incoming.DerivativeBoundBefore C (Q n) (t n)) →
      (∀ n i hi b, i.succ ≤ (j n).castSucc →
        t n - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        Q n ≤ Cb n * ((recordsK n i hi).static b).neck.scale) →
      (∀ n i hi b, i.succ ≤ (j n).castSucc →
        t n - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
    ∀ {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
      {Kh : ℕ → ObservedHistory.{u}}, Kh = (fun n => (K n).toHistory) →
    ∀ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier),
      (∀ n, (σ n : ℝ) = t n) → (∀ n, HEq (y n) (yG n)) →
      (∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl ε C1' C2' Ctime' (σ n) (y n)) →
    ∀ n, ¬ ∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
  obtain ⟨Ct₀, hCt₀, hG2⟩ := hnotK_of_capWindowWitness_theta_P6HN.{u}
  obtain ⟨Cs, hCs, hS⟩ := hcww_of_uniformCapWindow_seq_P6HN.{u} hε hε'
  refine ⟨Ct₀, Cs, hCt₀, hCs, fun C θ hθ => ?_⟩
  obtain ⟨Cb1, R1, ζ1, δ1, m1, hCb1, hR1, hζ1, hδ1, h1⟩ := hG2 C hθ
  obtain ⟨Cb2, R2, ζ2, δ2, m2, hCb2, hR2, hζ2, hδ2, h2⟩ := hS C hθ
  refine ⟨fun n => min (Cb1 n) (Cb2 n), fun n => max (R1 n) (R2 n), fun n => min (ζ1 n) (ζ2 n),
    fun n => min (δ1 n) (δ2 n), fun n => max (m1 n) (m2 n), fun n => lt_min (hCb1 n) (hCb2 n),
    fun n => (hR1 n).trans_le (le_max_left _ _), fun n => lt_min (hζ1 n) (hζ2 n),
    fun n => lt_min (hδ1 n) (hδ2 n), ?_⟩
  intro C1' C2' Ctime' hC1 hC2 hCt K j t hjt htj Q T₀ p pF recordsK recordsF a₀ hHI hcanK hδF
    hacc hrad hord hQ hder hcur hbirth hbirthA yG Kh hKh σ y hσ hyG hsel
  have hδF1 : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ δ1 n :=
    fun n i hi => (hδF n i hi).trans (min_le_left _ _)
  have hδF2 : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ δ2 n :=
    fun n i hi => (hδF n i hi).trans (min_le_right _ _)
  have hb1 : ∀ n i hi b, i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      Q n ≤ Cb1 n * ((recordsK n i hi).static b).neck.scale := fun n i hi b hl ha =>
    (hbirth n i hi b hl ha).trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
      ((recordsK n i hi).static b).neck.scale_pos.le)
  have hb2 : ∀ n i hi b, i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ θ n * (((recordsK n i hi).static b).neck.scale)⁻¹ →
      Q n ≤ Cb2 n * ((recordsK n i hi).static b).neck.scale := fun n i hi b hl ha =>
    (hbirth n i hi b hl ha).trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
      ((recordsK n i hi).static b).neck.scale_pos.le)
  subst hKh
  have hcww := h2 hC1 hC2 hjt htj recordsF hHI hcanK hδF2
    (fun n => (hacc n).trans (min_le_right _ _)) (fun n => (le_max_right _ _).trans (hrad n))
    (fun n => (le_max_right _ _).trans (hord n)) hQ hder hcur hb2 hbirthA (yG := yG)
  exact h1 hCt hjt htj recordsF hHI hcanK hδF1 (fun n => (hacc n).trans (min_le_left _ _))
    (fun n => (le_max_left _ _).trans (hrad n)) (fun n => (le_max_left _ _).trans (hord n)) hQ
    hder hcur hb1 hbirthA rfl σ y hσ hyG hsel (hcww σ y hσ hyG)

end RetainedCoreHistory

/-- consumer（`_P6HN`）：`θ n = 1 − 1/(n+2)`（P6R2 / closed 主形 (CWW) 年龄）满足 `θ n < 1`，同一 `Cs`
服务整个序列；结论喂 G2 主形 `hcww` 槽。 -/
example {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) (C : ℝ≥0) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧ ∃ (Cb : ℕ → ℝ), ∀ n, 0 < Cb n := by
  obtain ⟨Cs, hCs, hall⟩ := RetainedCoreHistory.hcww_of_uniformCapWindow_seq_P6HN.{0} hε hε'
  have hθ : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) < 1 := fun n => by
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  obtain ⟨Cb, -, -, -, -, hCb, -⟩ := hall C hθ
  exact ⟨Cs, hCs, Cb, hCb⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
