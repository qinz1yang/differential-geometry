import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowSliceComparison

/-!
# standard comparison 与 G2p 的 late-records + hybrid 形（O-CH11-P6LATE G1，后缀 `_P6LL`）

`CapWindowStandardComparison:20`（`exists_standard_comparison_of_cap_window_trace`）与
`CapWindowSliceComparison:17`（G2p `exists_capWindow_embedding_standard_close`）的局部化副本：

* records 改 late 形 `records : ∀ i, T₀ ≤ H.time i.succ → GeometricCutoffRecord H.toHistory i p`，
  `hcan` / birth 比较同形；原证明只在 cap event `j`（加 `hj : T₀ ≤ H.time j.succ`）上用
  `records j` / `hcanonical j`；`p₀` 去掉，`R ≤ p.modelRadius`、`m₀ ≤ p.modelOrder`、
  `p.modelAccuracy ≤ ζ₀` 直接加在 `p` 上；
* **hybrid**：`StandardCap/WindowPersistence:1029` 的 `parameters records` 形参要**全体** events 的
  records，但只用 `(records i).delta c ≤ δ₀`（`j.succ ≤ i.castSucc`、`i.succ ≤ k`，全是 late event）
  且与 cap witness `w` 独立 ⇒ 换成另给的 full family `recordsF`（参数 `pF`，固定窗口即可）+ late delta 界
  `∀ i, T₀ ≤ H.time i.succ → pF.delta (H.time i.succ) ≤ δbound`；
* G2p 的 `CapWindowPoint` 前提 / 结论里的 record 指标换成 late 展开形（`∃ j (hj : T₀ ≤ …) …`）。
其余证明逐字。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

/-- **`_P6LL`（standard comparison，late records + hybrid）**：`CapWindowStandardComparison:20` 的
副本，records late、WindowPersistence 吃 full family `recordsF`（只用其 late delta 界）。 -/
theorem exists_standard_comparison_of_cap_window_trace_late_P6LL
    (Θ : ℝ) (C : ℝ≥0) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ P Creset Cbirth : ℝ, 0 < P ∧ 0 < Creset ∧ 0 < Cbirth ∧
    ∀ (D ε η : ℝ) (hD : 0 < D), 0 < ε → 0 < η → ∀ N : ℕ,
    ∃ R : ℝ, D + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
    ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
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
    ∀ (t : ℝ) (hkt : H.time k < t), t < s → Gk.DerivativeBoundBefore C qcan t →
    ∀ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ k)
      (y : (H.stage k).Carrier)
      (A : BackwardPointTrace H.toHistory j.succ k hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hj).static b).window x →
      t - H.time j.succ ≤ θcap * (((records j hj).static b).neck.scale)⁻¹ →
      ‖x.val‖ < D + 1 →
      qcan ≤ Cbirth * ((records j hj).static b).neck.scale →
      1 ≤ a₀ * ((records j hj).static b).neck.scale →
    ∃ (G : (H.stage k).IncomingSlab (H.time k) t) (L : G.TerminalLimitMetric),
      (∀ v, G.flow.base.metric v = Gk.flow.base.metric v) ∧
      G.terminalRegularRegion = univ ∧
      L.metric = (Gk.flow.base.metric t).restrictOpen G.terminalRegularOpen ∧
    ∃ (x₀ : (H.toHistory.event j).incoming.terminalRegularOpen) (δ : ℝ) (kd : ℕ)
      (d : normalizedDatum (H.toHistory.event j).terminal.metric x₀ δ kd)
      (w : StandardCap.CanonicalStaticInsertionWitness d p.fixed.collarLength p.fixed.collar_pos
        p.modelRadius p.modelOrder p.modelAccuracy),
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        ((records j hj).static b).neck.scale * (H.initialMetric j.succ).inner
          (((records j hj).static b).window x)
          (mfderiv ThreeModel ThreeModel ((records j hj).static b).window x v)
          (mfderiv ThreeModel ThreeModel ((records j hj).static b).window x z)) ∧
    ∃ hDD : D ≤ p.modelRadius,
    ∃ z : standardCapWindow D, z.val = x.val ∧
    ∃ hy : y ∈ G.terminalRegularRegion,
    ∃ Ξ : standardCapWindow D →
        H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G,
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
      (∀ v, H.toHistory.backwardSurvivorMap j.succ k hl j.succ le_rfl hl (Ξ v).val =
        ((records j hj).static b).window
          (TopologicalSpace.Opens.inclusion
            (show standardCapWindow D ≤ standardCapWindow p.modelRadius from fun w hv =>
              (show ‖w‖ < D + 1 from hv).trans_le (add_le_add hDD (le_refl 1))) v)) ∧
      H.toHistory.backwardSurvivorIncomingMap j.succ k hl G (Ξ z) = ⟨y, hy⟩ ∧
      ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
        (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          (H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G))
        (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
          (RealTimeInterval.closed 0
            (((records j hj).static b).neck.scale * (t - H.time j.succ))
            (mul_nonneg ((records j hj).static b).neck.scale_pos.le
              (sub_nonneg.mpr ((H.time_strictMono.monotone hl).trans hkt.le))))),
        (∀ (i : Fin H.eventCount) (hf : j.succ ≤ i.castSucc) (hi : i.succ ≤ k),
          ∀ τ ∈ Icc (H.time i.castSucc) (H.time i.succ),
            gflow τ = (H.toHistory.backwardSurvivorSlabMetric j.succ k hl i hf hi τ).restrictOpen
              (H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G)) ∧
        (∀ τ ∈ Icc (H.time k) t,
          gflow τ = H.toHistory.backwardSurvivorIncomingMetric j.succ k hl G L τ) ∧
        IsSolutionOn S ∧ S.base.metric 0 = (w.restrictWindow hD hDD).windowMetric ∧
        (∀ τ, S.base.metric τ =
          localPullMetric (scaleMetric ((records j hj).static b).neck.scale
            ((records j hj).static b).neck.scale_pos
            (gflow (H.time j.succ + τ / ((records j hj).static b).neck.scale))) Ξ hΞ) ∧
        (∀ (v : standardCapWindow D) (i l : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
            (fun z : ℝ × standardCapWindow D => chartGramMatrix (S.base.metric z.1) v z.2 i l)
            (Icc 0 (((records j hj).static b).neck.scale * (t - H.time j.succ)) ×ˢ
              (trivializationAt ThreeSpace (TangentSpace ThreeModel) v).baseSet)) ∧
        (∀ τ ∈ Icc 0 (((records j hj).static b).neck.scale * (t - H.time j.succ)),
          ∀ v : standardCapWindow D,
            normSq0S (S.base.metric τ) v 4 (S.base.rm04 τ v) ≤ P ^ 2 ∧
              |S.scalar τ v| ≤ Creset) ∧
        ∃ Q : StandardSolution,
          ENNReal.ofReal (((records j hj).static b).neck.scale * (t - H.time j.succ)) <
            Q.val.lifetime ∧
          ∀ τ ∈ Icc 0 (((records j hj).static b).neck.scale * (t - H.time j.succ)),
            (∀ i ≤ N, ∀ v : standardCapWindow D,
              metricDerivNorm i (S.base.metric τ)
                ((Q.val.metric τ).restrictOpen (standardCapWindow D))
                (StandardCap.metric.restrictOpen (standardCapWindow D)) v < ε) ∧
            ∀ i ≤ 2, ∀ v : standardCapWindow D,
              metricDerivNorm i (S.base.metric τ)
                ((Q.val.metric τ).restrictOpen (standardCapWindow D))
                (StandardCap.metric.restrictOpen (standardCapWindow D)) v < η := by
  obtain ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, hwindow⟩ :=
    ObservedHistory.exists_uniform_prepared_incoming_cap_window_flow_of_backward_trace.{u, 0, 0, u}
      Θ C hΘ hΘ1
  refine ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, ?_⟩
  intro D ε η hD hε hη N
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hwindow⟩ :=
    hwindow (I := ThreeModel) D ε η hD hε hη N
  refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro H p T₀ records hcanonical hRp hmp hζp pF recordsF δbound hdelta hδb qcan a₀ θcap hqcan hθ
    hHI hlow k s Gk hGk hderiv t hkt hts hcur j hj hl y A b x hanchor hage hxD hbirth haq
  obtain ⟨x₀, δ, kd, d, w, -, hwmetric, -⟩ := hcanonical j hj b
  set Sc := (records j hj).static b with hSc
  set q := Sc.neck.scale with hqdef
  have hq : 0 < q := Sc.neck.scale_pos
  have hR : R ≤ p.modelRadius := hRp
  have hDD : D ≤ p.modelRadius := by linarith
  let F := Gk.closedPrefix t hkt hts
  let G := F.restrictIncoming le_rfl F.lt le_rfl
  let L := F.endpointTerminalLimitMetric (H.stage k)
  have hreg : G.terminalRegularRegion = univ := F.terminalRegularRegion_eq_univ (H.stage k)
  have hmetric : ∀ x' (v z : TangentSpace ThreeModel x'), w.windowMetric.inner x' v z =
      q * (H.initialMetric j.succ).inner (Sc.window x')
        (mfderiv ThreeModel ThreeModel Sc.window x' v)
        (mfderiv ThreeModel ThreeModel Sc.window x' z) := by
    intro x' v z
    have ho : (H.toHistory.event j).outputMetric = H.initialMetric j.succ := H.event_output j
    rw [hwmetric x' v z, ho]
  have hdeltas : ∀ i : Fin H.eventCount, j.succ ≤ i.castSucc → i.succ ≤ k →
      ∀ c, (recordsF i).delta c ≤ δ₀ :=
    fun i hi _ c => ((recordsF i).delta_le c).trans ((hdelta i (hj.trans
      (H.time_strictMono.monotone (hi.trans (Fin.castSucc_lt_succ (i := i)).le)))).trans hδb)
  have hslabs : ∀ i : Fin H.eventCount, j.succ ≤ i.castSucc → i.succ ≤ k →
      ∀ x' : (H.stage i.castSucc).Carrier, ∀ τ ∈ Ioo (H.time i.castSucc) (H.time i.succ),
        qcan < (H.toHistory.event i).incoming.flow.scalar τ x' →
        |derivWithin (fun v => (H.toHistory.event i).incoming.flow.scalar v x') (Iic τ) τ| ≤
          C * (H.toHistory.event i).incoming.flow.scalar τ x' ^ 2 :=
    fun i _ hi x' τ hτ hR => hderiv i (Fin.castSucc_lt_succ.trans_le hi) x' τ hτ hR
  have hfinal : ∀ x' : (H.stage k).Carrier, ∀ τ ∈ Ioo (H.time k) t,
      qcan < G.flow.scalar τ x' →
      |derivWithin (fun v => G.flow.scalar v x') (Iic τ) τ| ≤ C * G.flow.scalar τ x' ^ 2 :=
    fun x' τ hτ hR => hcur x' τ hτ hR
  have htime : q * (t - H.time j.succ) ≤ Θ := by
    have h1 : q * (t - H.time j.succ) ≤ q * (θcap * q⁻¹) :=
      mul_le_mul_of_nonneg_left hage hq.le
    have h2 : q * (θcap * q⁻¹) = θcap := by field_simp
    linarith
  have hxz : (⟨x.val, hxD⟩ : standardCapWindow D).val = x.val := rfl
  have hanchor' : A.point j.succ le_rfl hl =
      Sc.window (TopologicalSpace.Opens.inclusion
        (show standardCapWindow D ≤ standardCapWindow p.modelRadius from fun w hv =>
          (show ‖w‖ < D + 1 from hv).trans_le (add_le_add hDD (le_refl 1)))
        ⟨x.val, hxD⟩) := hanchor
  obtain ⟨hy, Ξ, hΞs, hΞbirth, hΞmark, hΞ, gflow, S, hS1, hS2, hS3, hS4, hS5, hS6, hS7, Q, hQ,
      hclose⟩ :=
    hwindow w hR hmp hζp H.toHistory j.succ k hl t G L hGk
      Sc.window Sc.window_smooth q qcan a₀ hq hqcan hbirth haq hmetric pF recordsF hHI hlow
      hdeltas hslabs hfinal htime ⟨x.val, hxD⟩ y A hanchor'
  exact ⟨G, L, fun _ => rfl, hreg, rfl, x₀, δ, kd, d, w, hmetric, hDD, ⟨x.val, hxD⟩, hxz, hy,
    Ξ, hΞs, hΞbirth, hΞmark, hΞ, gflow, S, hS1, hS2, hS3, hS4, hS5, hS6, hS7, Q, hQ, hclose⟩

/-- **`_P6LL`（G2p，late records + hybrid）**：`CapWindowSliceComparison:17` 的副本，底座换成
`exists_standard_comparison_of_cap_window_trace_late_P6LL`；`CapWindowPoint` 用 late 展开形。 -/
theorem exists_capWindow_embedding_standard_close_late_P6LL (C : ℝ≥0) :
    ∃ Cbirth : ℝ, 0 < Cbirth ∧
    ∀ (Dw D₂ ε : ℝ), 0 < Dw → Dw < D₂ → 0 < ε →
    ∃ R : ℝ, D₂ + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧ ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ 0 < δ₀ ∧
    ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters} {T₀ : ℝ}
      (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        GeometricCutoffRecord H.toHistory i p),
      (∀ i hi b, ((records i hi).static b).hasCanonicalWindow) →
      R ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
    ∀ {pF : CutoffParameters}, (∀ i, GeometricCutoffRecord H.toHistory i pF) →
    ∀ δbound : ℝ, (∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        pF.delta (H.time i.succ) ≤ δbound) →
      δbound ≤ δ₀ →
    ∀ (qcan a₀ : ℝ), 0 < qcan →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ i hi b, qcan ≤ Cbirth * ((records i hi).static b).neck.scale ∧
        1 ≤ a₀ * ((records i hi).static b).neck.scale) →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative C qcan k →
    ∀ t : ℝ, H.time k < t → t < s → Gk.DerivativeBoundBefore C qcan t →
    ∀ w : (H.stage k).Carrier,
      (∃ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ k)
        (A : BackwardPointTrace H.toHistory j.succ k hl w)
        (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        A.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dw + 1 ∧
          t - H.time j.succ ≤ 1 / 2 * (((records j hj).static b).neck.scale)⁻¹) →
    ∃ (Ξ : standardCapWindow D₂ → (H.stage k).Carrier)
      (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
      Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dw + 1 ∧
      ∃ (i : Fin H.eventCount) (hi : T₀ ≤ H.time i.succ)
        (b : (H.toHistory.event i).RetainedBoundaryIndex)
        (Q : StandardSolution) (τw : ℝ), τw ∈ Icc (0 : ℝ) (1 / 2) ∧
        ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
          metricDerivNorm m
            (localPullMetric (scaleMetric ((records i hi).static b).neck.scale
              ((records i hi).static b).neck.scale_pos (Gk.flow.base.metric t)) Ξ hΞ)
            ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
            (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < ε := by
  obtain ⟨Pb, Creset, Cbirth, -, -, hCbirth, hbridge⟩ :=
    exists_standard_comparison_of_cap_window_trace_late_P6LL.{u} (1 / 2) C (by norm_num)
      (by norm_num)
  refine ⟨Cbirth, hCbirth, ?_⟩
  intro Dw D₂ ε hDw hD₂ hε
  obtain ⟨R, hR, m₀, hm₀, ζ₀, δ₀, hζ₀, -, hδ₀, hwin⟩ :=
    hbridge D₂ ε ε (hDw.trans hD₂) hε hε 2
  refine ⟨R, hR, m₀, hm₀, ζ₀, δ₀, hζ₀, hδ₀, ?_⟩
  intro H p T₀ records hcan hRp hmp hζp pF recordsF δbound hdelta hδb qcan a₀ hqcan hHI hlow
    hbirth k s Gk hGk hderiv t hkt hts hcur w hcap
  obtain ⟨j, hj, hl, A, b, x, hanchor, hxD, hage⟩ := hcap
  obtain ⟨hb1, hb2⟩ := hbirth j hj b
  have hxD' : ‖x.val‖ < D₂ + 1 := by linarith
  obtain ⟨G, L, hG, -, hL, -, -, -, -, -, -, -, z, hzx, hy, Ξ, hΞs, -, hΞmark, hΞ, gflow, S,
      -, hS2, -, -, hS5, -, -, Q, -, hclose⟩ :=
    hwin H records hcan hRp hmp hζp recordsF δbound hdelta hδb qcan a₀ (1 / 2) hqcan le_rfl hHI
      hlow k s Gk hGk hderiv t hkt hts hcur j hj hl w A b x hanchor hage hxD' hb1 hb2
  set q := ((records j hj).static b).neck.scale with hqdef
  have hq : 0 < q := ((records j hj).static b).neck.scale_pos
  have hba : H.time j.succ ≤ H.time k := H.time_strictMono.monotone hl
  set T := q * (t - H.time j.succ) with hTdef
  have hT0 : 0 ≤ T := mul_nonneg hq.le (by linarith)
  have hTθ : T ≤ 1 / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hage hq.le
    rwa [mul_comm (1 / 2 : ℝ), ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] at h1
  have hTmem : T ∈ Icc 0 T := ⟨hT0, le_rfl⟩
  have htT : H.time j.succ + T / q = t := by
    rw [hTdef, mul_div_cancel_left₀ _ hq.ne']
    ring
  have hST := H.capWindow_flow_metric_eq Gk hl hΞ hq hG hL hS2 hS5 T hTmem
    (by rw [htT]; linarith)
  rw [htT] at hST
  refine ⟨fun v => (Ξ v).val.val,
    H.toHistory.isLocalDiffeomorph_backwardSurvivorIncomingDomain_val_val j.succ k hl G hΞ, z,
    H.toHistory.injective_backwardSurvivorIncomingDomain_val_val j.succ k hl G
      hΞs.isEmbedding.injective, congrArg Subtype.val hΞmark, by rw [hzx]; exact hxD,
    j, hj, b, Q, T, ⟨hT0, hTθ⟩, ?_⟩
  intro u m hm
  have h := (hclose T hTmem).2 m hm u
  rwa [hST] at h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
