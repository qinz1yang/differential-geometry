import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CapWitnessUniformP6HN

/-!
# (CWW) witness `hcww` 的 producer（θ₀ 形）：cap-window trace 点的 spatial canonical witness
（O-CH11-HNOT-LOCALDT G6，后缀 `_P6HN`）

* `capWindow_trace_spatialWitness_theta_P6HN`（PROVED）：late records cap-window trace 点 `(t, y)`（年龄
  `≤ θcap/scale`，`θcap ≤ Θ < 1`，`‖x‖ < D + 1`）上，`Gk.flow.base.metric t` 的 spatial canonical witness
  `(ε, C1, C2)`、`capTubeHasNeckChart ε`。常数 `Cs` 只依赖 `(ε, Θ)`，选在 Dt 输入 `C` 与窗口半径 `D` 之前。
  证明是 P6CW（age 0）的 time-T 孪生：
  1. G6a `exists_window_spatialCanonicalWitness_uniform_P6HN` 在 `S.base.metric T` 上给 witness；
  2. P6LL comparison 给 closeness、`capWindow_flow_metric_eq` 给 `S(T) = Φ^*(q·g(t))`；
  3. 梯度前提来自 G1 θ 版的梯度子句（scale-invariant：
     `abs_mfderiv_metricScalarAt_localPullMetric_scaleMetric_le`）；
  4. `exists_window_ball_placement` 给紧球，`pushforwardOfInjectiveULift` 加 `scaleMetric q⁻¹` 推回 `g(t)`。
* `spatialWitness_stage_of_incoming_P6HN`：incoming 形转成 `stageMetric` 形（经 `HEq`）。
* `hcww_of_uniformCapWindow_P6HN`（PROVED）：diagonal 序列（`D = n+1`，θ₀ 固定），结论 = G2 主形的
  `hcww` 槽逐字（θ ≡ θ₀）。导数前提仍是前缀 Dt。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance capWindowSigmaCompactP6HN6 (D : ℝ) :
    SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel (standardCapWindow D).isOpen)

namespace RetainedCoreHistory

universe u

/-- **cap-window trace 点的 spatial witness（`_P6HN`，PROVED，固定 Θ）**。 -/
theorem capWindow_trace_spatialWitness_theta_P6HN {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11)
    (Θ : ℝ) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ C : ℝ≥0, ∃ Cbirth : ℝ, 0 < Cbirth ∧ ∀ D : ℝ, 0 < D →
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
  obtain ⟨cg, Cg, hcg, hCg, hDt⟩ := capWindow_trace_localDt_theta_P6HN.{u} Θ hΘ hΘ1
  obtain ⟨Cw, hCw, hM4⟩ := exists_window_spatialCanonicalWitness_uniform_P6HN (Θ := Θ) hε hε' hΘ1
  obtain ⟨Λ, hΛ, hplace⟩ := StandardSolution.exists_window_ball_placement (Θ := Θ) hΘ1
  obtain ⟨eta, heta, hlower⟩ := exists_uniform_standard_metric_scalar_lower_comparison Θ hΘ.le hΘ1
  set L := 4 * Cw + 1 with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hΛL : 0 ≤ Λ * (L + 1) := by positivity
  refine ⟨max Cw Cg, hCw.trans (le_max_left _ _), fun C => ?_⟩
  obtain ⟨P, Creset, Cb1, -, -, hCb1, hbridge⟩ :=
    exists_standard_comparison_of_cap_window_trace_late_P6LL.{u} Θ C hΘ hΘ1
  obtain ⟨Cb2, hCb2, hDg⟩ := hDt C
  refine ⟨min Cb1 Cb2, lt_min hCb1 hCb2, fun D hD => ?_⟩
  obtain ⟨DW, NW, eW, hrD, heW, hwin⟩ := hM4 (D + 1) (Λ * (L + 1))
  obtain ⟨R1, hR1, m1, hm1, ζ1, δ1, hζ1, -, hδ1, hbr⟩ :=
    hbridge DW eW eta (by linarith) heW heta NW
  obtain ⟨R2, hR2, m2, hm2, ζ2, δ2, hζ2, -, hδ2, hyc⟩ := hDg D hD
  refine ⟨max R1 R2, by linarith [le_max_left R1 R2], max m1 m2, hm1.trans (le_max_left _ _),
    min ζ1 ζ2, min δ1 δ2, lt_min hζ1 hζ2, lt_min hδ1 hδ2, ?_⟩
  intro H p T₀ records hcan hrad hord hacc pF recordsF δbound hdelta hδb qcan a₀ θcap hqcan hθ
    hHI hlow k s Gk hGk hderiv t hkt hts hcur j hj hl y A b x hanchor hage hxD hbirth haq
    C1 C2 hC1 hC2
  set q := ((records j hj).static b).neck.scale with hqdef
  have hq : 0 < q := ((records j hj).static b).neck.scale_pos
  have hbirth1 : qcan ≤ Cb1 * q :=
    hbirth.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hq.le)
  have hbirth2 : qcan ≤ Cb2 * q :=
    hbirth.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hq.le)
  have hxW : ‖x.val‖ < DW + 1 := by linarith
  obtain ⟨G, L', hG, -, hL, -, -, -, -, -, -, -, z, hzx, hy, Ξ, hΞs, -, hΞmark, hΞ, gflow, S,
      -, hS2, -, -, hS5, -, -, Q, -, hclose⟩ :=
    hbr H records hcan ((le_max_left _ _).trans hrad) ((le_max_left _ _).trans hord)
      (hacc.trans (min_le_left _ _)) recordsF δbound hdelta (hδb.trans (min_le_left _ _))
      qcan a₀ θcap hqcan hθ hHI hlow k s Gk hGk hderiv t hkt hts hcur
      j hj hl y A b x hanchor hage hxW hbirth1 haq
  obtain ⟨hcR, -, hgradG⟩ := hyc H records hcan ((le_max_right _ _).trans hrad)
    ((le_max_right _ _).trans hord) (hacc.trans (min_le_right _ _)) recordsF δbound hdelta
    (hδb.trans (min_le_right _ _)) qcan a₀ θcap hqcan hθ hHI hlow k s Gk hGk hderiv t hkt hts
    hcur j hj hl y A b x hanchor hage hxD hbirth2 haq
  have hyz : (Ξ z).val.val = y := congrArg Subtype.val hΞmark
  have hba : H.time j.succ ≤ H.time k := H.time_strictMono.monotone hl
  set T := q * (t - H.time j.succ) with hTdef
  have hjt : H.time j.succ < t := hba.trans_lt hkt
  have hT0 : 0 ≤ T := mul_nonneg hq.le (by linarith)
  have hTθ : T ≤ θcap := by
    have h1 := mul_le_mul_of_nonneg_left hage hq.le
    rwa [mul_comm θcap, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] at h1
  have hTΘ : T ∈ Icc 0 Θ := ⟨hT0, hTθ.trans hθ⟩
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
  have hz : ‖z.val‖ < D + 1 := by rw [hzx]; exact hxD
  have hzr : ‖(z : EuclideanSpace ℝ (Fin 3))‖ + Λ * (L + 1) < DW + 1 := by linarith
  obtain ⟨hcpt, -⟩ := hplace DW L z hL0 hzr Q T hTΘ (S.base.metric T) (fun y' v => (hlow' y').1 v)
  have hCgC2 : Cg ≤ C2 := (le_max_right _ _).trans hC2
  have hCwC2 : Cw ≤ C2 := (le_max_left _ _).trans hC2
  have hR0 : 0 ≤ Gk.flow.scalar t y := le_trans (mul_nonneg hcg.le hq.le) hcR
  subst hyz
  have hgradOut : ∀ w : TangentSpace I3 ((fun v => (Ξ v).val.val) z),
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt (Gk.flow.base.metric t))
          ((fun v => (Ξ v).val.val) z) w)| ≤
        C2 * metricScalarAt (Gk.flow.base.metric t) ((fun v => (Ξ v).val.val) z) *
          Real.sqrt (metricScalarAt (Gk.flow.base.metric t) ((fun v => (Ξ v).val.val) z)) *
          Real.sqrt ((Gk.flow.base.metric t).inner ((fun v => (Ξ v).val.val) z) w w) := by
    intro w
    refine (hgradG w).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCgC2 hR0) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hgradS := abs_mfderiv_metricScalarAt_localPullMetric_scaleMetric_le
    (Gk.flow.base.metric t) (fun v => (Ξ v).val.val) hΦ hq z hgradOut
  have key : ∃ W : SpatialCanonicalWitness (localPullMetric (scaleMetric q hq
      (Gk.flow.base.metric t)) (fun v => (Ξ v).val.val) hΦ) ε Cw C2 z,
      W.capTubeHasNeckChart ε ∧ 2 * W.radius < L := by
    rw [← hST] at hgradS ⊢
    obtain ⟨W, hW⟩ := hwin Q T hTΘ (S.base.metric T) (fun i hi v => hclT.1 i hi v) z hz C2
      hCwC2 hgradS
    refine ⟨W, hW, ?_⟩
    have hQ1 : 1 ≤ metricScalarAt (Q.val.metric T) z.val :=
      Q.val.one_le_scalar T (Q.mem_domain_of_mem_Icc hΘ1 hTΘ) z.val
    have hlowz := (hlow' z).2
    rw [metricScalarAt_restrictOpen] at hlowz
    have hRS : 1 / 2 ≤ metricScalarAt (S.base.metric T) z := by
      linarith only [hlowz, hQ1]
    have hs : 1 / 2 ≤ Real.sqrt (metricScalarAt (S.base.metric T) z) := by
      have h := Real.sqrt_le_sqrt (show (1 / 2 : ℝ) ^ 2 ≤
        metricScalarAt (S.base.metric T) z by linarith only [hRS])
      rwa [Real.sqrt_sq (by norm_num)] at h
    have hr0 : 0 ≤ W.radius :=
      (inv_nonneg.mpr (Real.sqrt_nonneg _)).trans W.radius_lower
    have hup := W.radius_upper
    rw [le_div_iff₀ (Real.sqrt_pos.mpr (by linarith only [hRS]))] at hup
    linarith only [mul_le_mul_of_nonneg_left hs hr0, hup, hLdef]
  obtain ⟨W, hW, hWr⟩ := key
  rw [hST] at hcpt
  have hscale : scaleMetric q⁻¹ (inv_pos.mpr hq) (scaleMetric q hq (Gk.flow.base.metric t)) =
      Gk.flow.base.metric t :=
    SmoothRiemannianMetric.ext_inner fun v w₁ w₂ => by
      simp only [scaleMetric_inner]
      field_simp
  have hC1' : Cw ≤ C1 := (le_max_left _ _).trans hC1
  rw [← hscale]
  exact ⟨((W.pushforwardOfInjectiveULift hΦ hinj hWr hcpt).scaleMetric q⁻¹
      (inv_pos.mpr hq)).enlargeConstants hC1' le_rfl,
    (SpatialCanonicalWitness.capTubeHasNeckChart.scaleMetric q⁻¹ (inv_pos.mpr hq)
      (hW.pushforwardOfInjectiveULift hΦ hinj hWr hcpt)).enlarge_constants hC1' le_rfl⟩

/-- incoming 形 spatial witness ⇒ `stageMetric` 形（`_P6HN`；`m = j.castSucc`，`HEq z zG`）。 -/
theorem spatialWitness_stage_of_incoming_P6HN (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) {m : Fin (K.eventCount + 1)} (hm : j.castSucc = m) (v : ℝ)
    (z : (K.stage m).Carrier) (zG : (K.stage j.castSucc).Carrier) (hz : HEq z zG)
    {ε C1 C2 : ℝ}
    (h : ∃ W : SpatialCanonicalWitness ((K.toHistory.event j).incoming.flow.base.metric v)
      ε C1 C2 zG, W.capTubeHasNeckChart ε) :
    ∃ W : SpatialCanonicalWitness (K.toHistory.stageMetric m v) ε C1 C2 z,
      W.capTubeHasNeckChart ε := by
  subst hm
  obtain rfl := eq_of_heq hz
  rw [ObservedHistory.stageMetric_castSucc_apply]
  exact h

/-- **`hcww_of_uniformCapWindow_P6HN`（PROVED，θ₀ 形）**：diagonal 序列（`D = n+1`），结论 = G2 主形
`hnotK_of_capWindowWitness_theta_P6HN` 的 `hcww` 槽（`θ ≡ θ₀`，`Kh n = (K n).toHistory`）。常数 `Cs` 只依赖
`(ε, θ₀)`；导数前提仍是前缀 Dt（与 G2 主形同一对）。 -/
theorem hcww_of_uniformCapWindow_P6HN {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) {θ₀ : ℝ}
    (hθ₀ : 0 < θ₀) (hθ₀1 : θ₀ < 1) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ C : ℝ≥0, ∃ Cbirth : ℝ, 0 < Cbirth ∧
    ∃ (Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ),
      (∀ n : ℕ, ((n : ℝ) + 1) + 1 < Rn n) ∧ (∀ n, 0 < ζ n) ∧ (∀ n, 0 < δ₀ n) ∧
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
        t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
        Q n ≤ Cbirth * ((recordsK n i hi).static b).neck.scale) →
      (∀ n i hi b, i.succ ≤ (j n).castSucc →
        t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹ →
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
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
      ∃ W : SpatialCanonicalWitness ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n)) ε C1' C2' (y n), W.capTubeHasNeckChart ε := by
  obtain ⟨Cs, hCs, hall⟩ := capWindow_trace_spatialWitness_theta_P6HN.{u} hε hε' θ₀ hθ₀ hθ₀1
  refine ⟨Cs, hCs, fun C => ?_⟩
  obtain ⟨Cb, hCb, hD⟩ := hall C
  choose Rn hRn m₀ _hm₀ ζ δ₀ hζ hδ h4 using fun n : ℕ => hD ((n : ℝ) + 1) (by positivity)
  refine ⟨Cb, hCb, Rn, ζ, δ₀, m₀, hRn, hζ, hδ, ?_⟩
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
    (hδF n) le_rfl (Q n) a₀ θ₀ (hQ n) le_rfl (fun x => (hHI n x).1) (fun x => (hHI n x).2)
    (j n).castSucc ((K n).time (j n).succ) ((K n).toHistory.event (j n)).incoming
    ((K n).event_initial (j n)) (hder n) (t n) (hjt n) (htj n) (hcur n) i hi hl (yG n) A b x hx
    hage hxn (hbirth n i hi b hl hage) (hbirthA n i hi b hl hage) C1' C2' hC1 hC2
  have hW' : ∃ W : SpatialCanonicalWitness
      (((K n).toHistory.event (j n)).incoming.flow.base.metric (σ n : ℝ)) ε C1' C2' (yG n),
      W.capTubeHasNeckChart ε := by
    rw [hσ n]
    exact hW
  exact (K n).spatialWitness_stage_of_incoming_P6HN (j n) hact.symm (σ n) (y n) (yG n) (hyG n) hW'

end RetainedCoreHistory

/-- consumer（`_P6HN`）：`hcww_of_uniformCapWindow_P6HN` 的结论逐字 = G2 主形 `hcww` 槽在 `θ := fun _ => θ₀`、
`Kh := fun n => (K n).toHistory` 处的形（β 等同）。 -/
example {ε C1' C2' θ₀ : ℝ} {K : ℕ → RetainedCoreHistory.{0}} {j : ∀ n, Fin (K n).eventCount}
    {t T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    {Kh : ℕ → ObservedHistory.{0}} (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (h : ∀ (σ' : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
      (y' : ∀ n, ((K n).toHistory.stageAt (σ' n)).Carrier),
      ∀ n, (∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ∃ W : SpatialCanonicalWitness ((K n).toHistory.stageMetric
          ((K n).toHistory.activeStage (σ' n)) (σ' n)) ε C1' C2' (y' n),
          W.capTubeHasNeckChart ε) :
    ∀ n, (∃ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (hl : i.succ ≤ (j n).castSucc)
        (A : BackwardPointTrace (K n).toHistory i.succ (j n).castSucc hl (yG n))
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          t n - (K n).time i.succ ≤
            (fun _ : ℕ => θ₀) n * (((recordsK n i hi).static b).neck.scale)⁻¹) →
      ∃ W : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ε C1' C2' (y n), W.capTubeHasNeckChart ε := by
  subst hKh
  exact h σ y

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
