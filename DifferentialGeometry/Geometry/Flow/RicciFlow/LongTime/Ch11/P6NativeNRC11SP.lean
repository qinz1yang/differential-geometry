import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeWindowPersistenceLocalC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowStandardComparison

/-!
# NR 侧：record 层 cap window standard comparison 的局部 Dt 孪生（O-CH11-NATIVE-NR G3，后缀 `_C11SP`）

`exists_standard_comparison_of_cap_window_trace_tube_C11SP` = `CapWindowStandardComparison` 的
`exists_standard_comparison_of_cap_window_trace` 的孪生：原来的两个全局 Dt 前提
`H.EventSlabsDerivative C qcan k`（所有 slab、所有点）与 `Gk.DerivativeBoundBefore C qcan t` 换成
**开 tube 形局部 Dt（合同 X）**：tube `W`（开）覆盖从 `j.succ` 出发、起点在新生 cap 窗
`range ((records j).static b).window` 内的 backward traces，Dt 只在 `W` 上要。证明 = 原证明把
`WindowPersistence:1029` 换成 G2 孪生；量词序随 G2 加强为 `∃ P Creset Cbirth, ∀ C`。

这是 NR（NATIVE-CC `P6LargeCapNonResurgeryC11SP` 的 `hNR`）要用的 record 层窗口控制：在
`e₁` 新生的大 cap（`q = neck.scale`）上，`t − T(e₁⁺) ≤ θcap / q`、`θcap ≤ Θ < 1` 的自身尺度时间窗里，
窗口 survivor 嵌入 + 贴近标准解。
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

open ObservedHistory in
theorem exists_standard_comparison_of_cap_window_trace_tube_C11SP
    (Θ : ℝ) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ P Creset Cbirth : ℝ, 0 < P ∧ 0 < Creset ∧ 0 < Cbirth ∧ ∀ C : ℝ≥0,
    ∀ (D ε η : ℝ) (hD : 0 < D), 0 < ε → 0 < η → ∀ N : ℕ,
    ∃ R : ℝ, D + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
    ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
      (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      (∀ i b, ((records i).static b).hasCanonicalWindow) →
      R ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
    ∀ (qcan a₀ θcap : ℝ), 0 < qcan → θcap ≤ Θ →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
    ∀ (t : ℝ) (hkt : H.time k < t), t < s →
    ∀ (j : Fin H.eventCount) (hl : j.succ ≤ k) (y : (H.stage k).Carrier)
      (A : BackwardPointTrace H.toHistory j.succ k hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j).static b).window x →
      t - H.time j.succ ≤ θcap * (((records j).static b).neck.scale)⁻¹ →
      ‖x.val‖ < D + 1 →
      qcan ≤ Cbirth * ((records j).static b).neck.scale →
      1 ≤ a₀ * ((records j).static b).neck.scale →
    (∀ i : Fin H.eventCount, j.succ ≤ i.castSucc → i.succ ≤ k → p.delta (H.time i.succ) ≤ δ₀) →
    ∀ (W : ∀ i : Fin (H.eventCount + 1), Set (H.stage i).Carrier), (∀ i, IsOpen (W i)) →
      (∀ (i : Fin (H.eventCount + 1)) (hf : j.succ ≤ i), i ≤ k →
        ∀ (x' : (H.stage i).Carrier) (A' : BackwardPointTrace H.toHistory j.succ i hf x'),
          A'.point j.succ le_rfl hf ∈ ((records j).static b).window '' {z | ‖z.val‖ < R + 1} →
            x' ∈ W i) →
      (∀ i : Fin H.eventCount, j.succ ≤ i.castSucc → i.succ ≤ k →
        ∀ x' : (H.stage i.castSucc).Carrier, x' ∈ W i.castSucc →
        ∀ τ ∈ Ioo (H.time i.castSucc) (H.time i.succ),
          qcan < (H.toHistory.event i).incoming.flow.scalar τ x' →
          |derivWithin (fun v => (H.toHistory.event i).incoming.flow.scalar v x') (Iic τ) τ| ≤
            C * (H.toHistory.event i).incoming.flow.scalar τ x' ^ 2) →
      (∀ x' : (H.stage k).Carrier, x' ∈ W k → ∀ τ ∈ Ioo (H.time k) t,
        qcan < Gk.flow.scalar τ x' →
        |derivWithin (fun v => Gk.flow.scalar v x') (Iic τ) τ| ≤ C * Gk.flow.scalar τ x' ^ 2) →
    ∃ (G : (H.stage k).IncomingSlab (H.time k) t) (L : G.TerminalLimitMetric),
      (∀ v, G.flow.base.metric v = Gk.flow.base.metric v) ∧
      G.terminalRegularRegion = univ ∧
      L.metric = (Gk.flow.base.metric t).restrictOpen G.terminalRegularOpen ∧
    ∃ (x₀ : (H.toHistory.event j).incoming.terminalRegularOpen) (δ : ℝ) (kd : ℕ)
      (d : normalizedDatum (H.toHistory.event j).terminal.metric x₀ δ kd)
      (w : StandardCap.CanonicalStaticInsertionWitness d p.fixed.collarLength p.fixed.collar_pos
        p.modelRadius p.modelOrder p.modelAccuracy),
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        ((records j).static b).neck.scale * (H.initialMetric j.succ).inner
          (((records j).static b).window x)
          (mfderiv ThreeModel ThreeModel ((records j).static b).window x v)
          (mfderiv ThreeModel ThreeModel ((records j).static b).window x z)) ∧
    ∃ hDD : D ≤ p.modelRadius,
    ∃ z : standardCapWindow D, z.val = x.val ∧
    ∃ hy : y ∈ G.terminalRegularRegion,
    ∃ Ξ : standardCapWindow D →
        H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G,
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
      (∀ v, H.toHistory.backwardSurvivorMap j.succ k hl j.succ le_rfl hl (Ξ v).val =
        ((records j).static b).window
          (TopologicalSpace.Opens.inclusion
            (show standardCapWindow D ≤ standardCapWindow p.modelRadius from fun w hv =>
              (show ‖w‖ < D + 1 from hv).trans_le (add_le_add hDD (le_refl 1))) v)) ∧
      H.toHistory.backwardSurvivorIncomingMap j.succ k hl G (Ξ z) = ⟨y, hy⟩ ∧
      ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
        (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          (H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G))
        (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
          (RealTimeInterval.closed 0
            (((records j).static b).neck.scale * (t - H.time j.succ))
            (mul_nonneg ((records j).static b).neck.scale_pos.le
              (sub_nonneg.mpr ((H.time_strictMono.monotone hl).trans hkt.le))))),
        (∀ (i : Fin H.eventCount) (hf : j.succ ≤ i.castSucc) (hi : i.succ ≤ k),
          ∀ τ ∈ Icc (H.time i.castSucc) (H.time i.succ),
            gflow τ = (H.toHistory.backwardSurvivorSlabMetric j.succ k hl i hf hi τ).restrictOpen
              (H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G)) ∧
        (∀ τ ∈ Icc (H.time k) t,
          gflow τ = H.toHistory.backwardSurvivorIncomingMetric j.succ k hl G L τ) ∧
        IsSolutionOn S ∧ S.base.metric 0 = (w.restrictWindow hD hDD).windowMetric ∧
        (∀ τ, S.base.metric τ =
          localPullMetric (scaleMetric ((records j).static b).neck.scale
            ((records j).static b).neck.scale_pos
            (gflow (H.time j.succ + τ / ((records j).static b).neck.scale))) Ξ hΞ) ∧
        (∀ (v : standardCapWindow D) (i l : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
            (fun z : ℝ × standardCapWindow D => chartGramMatrix (S.base.metric z.1) v z.2 i l)
            (Icc 0 (((records j).static b).neck.scale * (t - H.time j.succ)) ×ˢ
              (trivializationAt ThreeSpace (TangentSpace ThreeModel) v).baseSet)) ∧
        (∀ τ ∈ Icc 0 (((records j).static b).neck.scale * (t - H.time j.succ)),
          ∀ v : standardCapWindow D,
            normSq0S (S.base.metric τ) v 4 (S.base.rm04 τ v) ≤ P ^ 2 ∧
              |S.scalar τ v| ≤ Creset) ∧
        ∃ Q : StandardSolution,
          ENNReal.ofReal (((records j).static b).neck.scale * (t - H.time j.succ)) <
            Q.val.lifetime ∧
          ∀ τ ∈ Icc 0 (((records j).static b).neck.scale * (t - H.time j.succ)),
            (∀ i ≤ N, ∀ v : standardCapWindow D,
              metricDerivNorm i (S.base.metric τ)
                ((Q.val.metric τ).restrictOpen (standardCapWindow D))
                (StandardCap.metric.restrictOpen (standardCapWindow D)) v < ε) ∧
            ∀ i ≤ 2, ∀ v : standardCapWindow D,
              metricDerivNorm i (S.base.metric τ)
                ((Q.val.metric τ).restrictOpen (standardCapWindow D))
                (StandardCap.metric.restrictOpen (standardCapWindow D)) v < η := by
  obtain ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, hwindowC⟩ :=
    exists_uniform_prepared_incoming_cap_window_flow_of_backward_trace_tube_C11SP.{u, 0, 0, u}
      Θ hΘ hΘ1
  refine ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, ?_⟩
  intro C D ε η hD hε hη N
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hwindow⟩ :=
    hwindowC C (I := ThreeModel) D ε η hD hε hη N
  refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro H p records hcanonical hRp hmp hζp qcan a₀ θcap hqcan hθ hHI hlow
    k s Gk hGk t hkt hts j hl y A b x hanchor hage hxD hbirth haq hδloc W hW htube hderivW hfinalW
  obtain ⟨x₀, δ, kd, d, w, -, hwmetric, -⟩ := hcanonical j b
  set Sc := (records j).static b with hSc
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
      ∀ c, (records i).delta c ≤ δ₀ :=
    fun i h1 h2 c => ((records i).delta_le c).trans (hδloc i h1 h2)
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
      Sc.window Sc.window_smooth q qcan a₀ hq hqcan hbirth haq hmetric p records hHI hlow
      hdeltas W hW htube hderivW hfinalW htime ⟨x.val, hxD⟩ y A hanchor'
  exact ⟨G, L, fun _ => rfl, hreg, rfl, x₀, δ, kd, d, w, hmetric, hDD, ⟨x.val, hxD⟩, hxz, hy,
    Ξ, hΞs, hΞbirth, hΞmark, hΞ, gflow, S, hS1, hS2, hS3, hS4, hS5, hS6, hS7, Q, hQ, hclose⟩

/-- consumer（G3a）：tube 孪生 ⇒ 原 `exists_standard_comparison_of_cap_window_trace`（取 `W i := univ`；
全局 `EventSlabsDerivative` / `DerivativeBoundBefore` 落成局部形）。陈述与原定理逐字相同。 -/
theorem exists_standard_comparison_of_cap_window_trace_global_C11SP
    (Θ : ℝ) (C : ℝ≥0) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ P Creset Cbirth : ℝ, 0 < P ∧ 0 < Creset ∧ 0 < Cbirth ∧
    ∀ (D ε η : ℝ) (hD : 0 < D), 0 < ε → 0 < η → ∀ N : ℕ,
    ∃ R : ℝ, D + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
    ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ (H : RetainedCoreHistory.{u}) (p₀ : CutoffParameters)
      (δbound ρbound : ℝ) {p : CutoffParameters}
      (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      δbound ≤ δ₀ → R ≤ p₀.modelRadius → m₀ ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀ →
    ∀ (qcan a₀ θcap : ℝ), 0 < qcan → θcap ≤ Θ →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative C qcan k →
    ∀ (t : ℝ) (hkt : H.time k < t), t < s → Gk.DerivativeBoundBefore C qcan t →
    ∀ (j : Fin H.eventCount) (hl : j.succ ≤ k) (y : (H.stage k).Carrier)
      (A : BackwardPointTrace H.toHistory j.succ k hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j).static b).window x →
      t - H.time j.succ ≤ θcap * (((records j).static b).neck.scale)⁻¹ →
      ‖x.val‖ < D + 1 →
      qcan ≤ Cbirth * ((records j).static b).neck.scale →
      1 ≤ a₀ * ((records j).static b).neck.scale →
    ∃ (G : (H.stage k).IncomingSlab (H.time k) t) (L : G.TerminalLimitMetric),
      (∀ v, G.flow.base.metric v = Gk.flow.base.metric v) ∧
      G.terminalRegularRegion = univ ∧
      L.metric = (Gk.flow.base.metric t).restrictOpen G.terminalRegularOpen ∧
    ∃ (x₀ : (H.toHistory.event j).incoming.terminalRegularOpen) (δ : ℝ) (kd : ℕ)
      (d : normalizedDatum (H.toHistory.event j).terminal.metric x₀ δ kd)
      (w : StandardCap.CanonicalStaticInsertionWitness d p.fixed.collarLength p.fixed.collar_pos
        p.modelRadius p.modelOrder p.modelAccuracy),
      (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
        ((records j).static b).neck.scale * (H.initialMetric j.succ).inner
          (((records j).static b).window x)
          (mfderiv ThreeModel ThreeModel ((records j).static b).window x v)
          (mfderiv ThreeModel ThreeModel ((records j).static b).window x z)) ∧
    ∃ hDD : D ≤ p.modelRadius,
    ∃ z : standardCapWindow D, z.val = x.val ∧
    ∃ hy : y ∈ G.terminalRegularRegion,
    ∃ Ξ : standardCapWindow D →
        H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G,
      IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
      (∀ v, H.toHistory.backwardSurvivorMap j.succ k hl j.succ le_rfl hl (Ξ v).val =
        ((records j).static b).window
          (TopologicalSpace.Opens.inclusion
            (show standardCapWindow D ≤ standardCapWindow p.modelRadius from fun w hv =>
              (show ‖w‖ < D + 1 from hv).trans_le (add_le_add hDD (le_refl 1))) v)) ∧
      H.toHistory.backwardSurvivorIncomingMap j.succ k hl G (Ξ z) = ⟨y, hy⟩ ∧
      ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
        (gflow : ℝ → SmoothRiemannianMetric ThreeModel
          (H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G))
        (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
          (RealTimeInterval.closed 0
            (((records j).static b).neck.scale * (t - H.time j.succ))
            (mul_nonneg ((records j).static b).neck.scale_pos.le
              (sub_nonneg.mpr ((H.time_strictMono.monotone hl).trans hkt.le))))),
        (∀ (i : Fin H.eventCount) (hf : j.succ ≤ i.castSucc) (hi : i.succ ≤ k),
          ∀ τ ∈ Icc (H.time i.castSucc) (H.time i.succ),
            gflow τ = (H.toHistory.backwardSurvivorSlabMetric j.succ k hl i hf hi τ).restrictOpen
              (H.toHistory.backwardSurvivorIncomingDomain j.succ k hl G)) ∧
        (∀ τ ∈ Icc (H.time k) t,
          gflow τ = H.toHistory.backwardSurvivorIncomingMetric j.succ k hl G L τ) ∧
        IsSolutionOn S ∧ S.base.metric 0 = (w.restrictWindow hD hDD).windowMetric ∧
        (∀ τ, S.base.metric τ =
          localPullMetric (scaleMetric ((records j).static b).neck.scale
            ((records j).static b).neck.scale_pos
            (gflow (H.time j.succ + τ / ((records j).static b).neck.scale))) Ξ hΞ) ∧
        (∀ (v : standardCapWindow D) (i l : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
            (fun z : ℝ × standardCapWindow D => chartGramMatrix (S.base.metric z.1) v z.2 i l)
            (Icc 0 (((records j).static b).neck.scale * (t - H.time j.succ)) ×ˢ
              (trivializationAt ThreeSpace (TangentSpace ThreeModel) v).baseSet)) ∧
        (∀ τ ∈ Icc 0 (((records j).static b).neck.scale * (t - H.time j.succ)),
          ∀ v : standardCapWindow D,
            normSq0S (S.base.metric τ) v 4 (S.base.rm04 τ v) ≤ P ^ 2 ∧
              |S.scalar τ v| ≤ Creset) ∧
        ∃ Q : StandardSolution,
          ENNReal.ofReal (((records j).static b).neck.scale * (t - H.time j.succ)) <
            Q.val.lifetime ∧
          ∀ τ ∈ Icc 0 (((records j).static b).neck.scale * (t - H.time j.succ)),
            (∀ i ≤ N, ∀ v : standardCapWindow D,
              metricDerivNorm i (S.base.metric τ)
                ((Q.val.metric τ).restrictOpen (standardCapWindow D))
                (StandardCap.metric.restrictOpen (standardCapWindow D)) v < ε) ∧
            ∀ i ≤ 2, ∀ v : standardCapWindow D,
              metricDerivNorm i (S.base.metric τ)
                ((Q.val.metric τ).restrictOpen (standardCapWindow D))
                (StandardCap.metric.restrictOpen (standardCapWindow D)) v < η := by
  obtain ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, h⟩ :=
    exists_standard_comparison_of_cap_window_trace_tube_C11SP.{u} Θ hΘ hΘ1
  refine ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, ?_⟩
  intro D ε η hD hε hη N
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, h⟩ := h C D ε η hD hε hη N
  refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro H p₀ δbound ρbound p records hfam hδb hRp hmp hζp qcan a₀ θcap hqcan hθ hHI hlow
    k s Gk hGk hderiv t hkt hts hcur j hl y A b x hanchor hage hxD hbirth haq
  obtain ⟨-, hradius, horder, haccuracy, -, hcanonical, hdelta, -⟩ := hfam
  exact h H records hcanonical (hradius ▸ hRp) (horder ▸ hmp) (haccuracy ▸ hζp) qcan a₀ θcap hqcan
    hθ hHI hlow k s Gk hGk t hkt hts j hl y A b x hanchor hage hxD hbirth haq
    (fun i _ _ => (hdelta i).trans hδb) (fun _ => univ)
    (fun _ => isOpen_univ) (fun _ _ _ _ _ _ => mem_univ _)
    (fun i _ hi x' _ τ hτ hR => hderiv i (Fin.castSucc_lt_succ.trans_le hi) x' τ hτ hR)
    (fun x' _ τ hτ hR => hcur x' τ hτ hR)


/-- **G3b（PROVISIONAL[X, SEP]）NR 的两两核**：在 `e₁` 新生大 cap（`q₁ = neck.scale ≤ 4BQ`）上，trace
`A : e₁⁺ → e₂⁻` 在自身尺度窗 `t − T(e₁⁺) ≤ θ/Q`（`4Bθ ≤ Θ`）内；合同 X（开 tube `W` + 局部 Dt）经 G3a
（⇐ G2 孪生）给出 `e₂⁻` 处窗口 survivor 嵌入 + 贴近标准解；separation 合同 `hSEP`（窗口控制 ⇒ 穿过 `e₂`
的点不落在 `e₂` 任何大 cap 的 buffer `transitionEnd < ‖z₂‖ ≤ transitionEnd + 10`）给 NR 的两两结论。
`hSEP` 的前件逐字 = G3a 结论在 `k := e₂.castSucc`、`Gk := (event e₂).incoming`、`j := e₁` 处的实例。 -/
theorem nonResurgery_pair_of_tube_C11SP
    (Θ : ℝ) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ P Creset Cbirth : ℝ, 0 < P ∧ 0 < Creset ∧ 0 < Cbirth ∧ ∀ C : ℝ≥0,
    ∀ (D ε η : ℝ) (hD : 0 < D), 0 < ε → 0 < η → ∀ N : ℕ,
    ∃ R : ℝ, D + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
    ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
      (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      (∀ i b, ((records i).static b).hasCanonicalWindow) →
      R ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
    ∀ (qcan a₀ B Q θ : ℝ), 0 < qcan → 0 < Q → 0 ≤ θ → 4 * (B * θ) ≤ Θ →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
    ∀ (e₁ e₂ : Fin H.eventCount) (hl : e₁.succ ≤ e₂.castSucc)
      (t : ℝ) (ht : t ∈ Ioo (H.time e₂.castSucc) (H.time e₂.succ))
      (y : (H.stage e₂.castSucc).Carrier) (A : BackwardPointTrace H.toHistory e₁.succ e₂.castSucc
          hl y)
      (b : (H.toHistory.event e₁).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point e₁.succ le_rfl hl = ((records e₁).static b).window x →
      t - H.time e₁.succ ≤ θ / Q →
      ((records e₁).static b).neck.scale ≤ 4 * (B * Q) →
      ‖x.val‖ < D + 1 →
      qcan ≤ Cbirth * ((records e₁).static b).neck.scale →
      1 ≤ a₀ * ((records e₁).static b).neck.scale →
    (∀ i : Fin H.eventCount, e₁.succ ≤ i.castSucc → i.succ ≤ e₂.castSucc →
      p.delta (H.time i.succ) ≤ δ₀) →
    ∀ (W : ∀ i : Fin (H.eventCount + 1), Set (H.stage i).Carrier), (∀ i, IsOpen (W i)) →
      (∀ (i : Fin (H.eventCount + 1)) (hf : e₁.succ ≤ i), i ≤ e₂.castSucc →
        ∀ (x' : (H.stage i).Carrier) (A' : BackwardPointTrace H.toHistory e₁.succ i hf x'),
          A'.point e₁.succ le_rfl hf ∈ ((records e₁).static b).window '' {z | ‖z.val‖ < R + 1} →
            x' ∈ W i) →
      (∀ i : Fin H.eventCount, e₁.succ ≤ i.castSucc → i.succ ≤ e₂.castSucc →
        ∀ x' : (H.stage i.castSucc).Carrier, x' ∈ W i.castSucc →
        ∀ τ ∈ Ioo (H.time i.castSucc) (H.time i.succ),
          qcan < (H.toHistory.event i).incoming.flow.scalar τ x' →
          |derivWithin (fun v => (H.toHistory.event i).incoming.flow.scalar v x') (Iic τ) τ| ≤
            C * (H.toHistory.event i).incoming.flow.scalar τ x' ^ 2) →
      (∀ x' : (H.stage e₂.castSucc).Carrier, x' ∈ W e₂.castSucc → ∀ τ ∈ Ioo (H.time e₂.castSucc) t,
        qcan < (H.toHistory.event e₂).incoming.flow.scalar τ x' →
        |derivWithin (fun v => (H.toHistory.event e₂).incoming.flow.scalar v x') (Iic τ) τ| ≤
          C * (H.toHistory.event e₂).incoming.flow.scalar τ x' ^ 2) →
      ((
        ∃ (G : (H.stage e₂.castSucc).IncomingSlab (H.time e₂.castSucc) t) (L :
            G.TerminalLimitMetric),
          (∀ v, G.flow.base.metric v = (H.toHistory.event e₂).incoming.flow.base.metric v) ∧
          G.terminalRegularRegion = univ ∧
          L.metric = ((H.toHistory.event e₂).incoming.flow.base.metric t).restrictOpen
              G.terminalRegularOpen ∧
        ∃ (x₀ : (H.toHistory.event e₁).incoming.terminalRegularOpen) (δ : ℝ) (kd : ℕ)
          (d : normalizedDatum (H.toHistory.event e₁).terminal.metric x₀ δ kd)
          (w : StandardCap.CanonicalStaticInsertionWitness d p.fixed.collarLength p.fixed.collar_pos
            p.modelRadius p.modelOrder p.modelAccuracy),
          (∀ x (v z : TangentSpace ThreeModel x), w.windowMetric.inner x v z =
            ((records e₁).static b).neck.scale * (H.initialMetric e₁.succ).inner
              (((records e₁).static b).window x)
              (mfderiv ThreeModel ThreeModel ((records e₁).static b).window x v)
              (mfderiv ThreeModel ThreeModel ((records e₁).static b).window x z)) ∧
        ∃ hDD : D ≤ p.modelRadius,
        ∃ z : standardCapWindow D, z.val = x.val ∧
        ∃ hy : y ∈ G.terminalRegularRegion,
        ∃ Ξ : standardCapWindow D →
            H.toHistory.backwardSurvivorIncomingDomain e₁.succ e₂.castSucc hl G,
          IsSmoothEmbedding ThreeModel ThreeModel ∞ Ξ ∧
          (∀ v, H.toHistory.backwardSurvivorMap e₁.succ e₂.castSucc hl e₁.succ le_rfl hl (Ξ v).val =
            ((records e₁).static b).window
              (TopologicalSpace.Opens.inclusion
                (show standardCapWindow D ≤ standardCapWindow p.modelRadius from fun w hv =>
                  (show ‖w‖ < D + 1 from hv).trans_le (add_le_add hDD (le_refl 1))) v)) ∧
          H.toHistory.backwardSurvivorIncomingMap e₁.succ e₂.castSucc hl G (Ξ z) = ⟨y, hy⟩ ∧
          ∃ (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
            (gflow : ℝ → SmoothRiemannianMetric ThreeModel
              (H.toHistory.backwardSurvivorIncomingDomain e₁.succ e₂.castSucc hl G))
            (S : SolutionOn (I := ThreeModel) (M := standardCapWindow D)
              (RealTimeInterval.closed 0
                (((records e₁).static b).neck.scale * (t - H.time e₁.succ))
                (mul_nonneg ((records e₁).static b).neck.scale_pos.le
                  (sub_nonneg.mpr ((H.time_strictMono.monotone hl).trans ht.1.le))))),
            (∀ (i : Fin H.eventCount) (hf : e₁.succ ≤ i.castSucc) (hi : i.succ ≤ e₂.castSucc),
              ∀ τ ∈ Icc (H.time i.castSucc) (H.time i.succ),
                gflow τ = (H.toHistory.backwardSurvivorSlabMetric e₁.succ e₂.castSucc hl i hf hi
                    τ).restrictOpen
                  (H.toHistory.backwardSurvivorIncomingDomain e₁.succ e₂.castSucc hl G)) ∧
            (∀ τ ∈ Icc (H.time e₂.castSucc) t,
              gflow τ = H.toHistory.backwardSurvivorIncomingMetric e₁.succ e₂.castSucc hl G L τ) ∧
            IsSolutionOn S ∧ S.base.metric 0 = (w.restrictWindow hD hDD).windowMetric ∧
            (∀ τ, S.base.metric τ =
              localPullMetric (scaleMetric ((records e₁).static b).neck.scale
                ((records e₁).static b).neck.scale_pos
                (gflow (H.time e₁.succ + τ / ((records e₁).static b).neck.scale))) Ξ hΞ) ∧
            (∀ (v : standardCapWindow D) (i l : Fin (Module.finrank ℝ ThreeSpace)),
              ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
                (fun z : ℝ × standardCapWindow D => chartGramMatrix (S.base.metric z.1) v z.2 i l)
                (Icc 0 (((records e₁).static b).neck.scale * (t - H.time e₁.succ)) ×ˢ
                  (trivializationAt ThreeSpace (TangentSpace ThreeModel) v).baseSet)) ∧
            (∀ τ ∈ Icc 0 (((records e₁).static b).neck.scale * (t - H.time e₁.succ)),
              ∀ v : standardCapWindow D,
                normSq0S (S.base.metric τ) v 4 (S.base.rm04 τ v) ≤ P ^ 2 ∧
                  |S.scalar τ v| ≤ Creset) ∧
            ∃ Q : StandardSolution,
              ENNReal.ofReal (((records e₁).static b).neck.scale * (t - H.time e₁.succ)) <
                Q.val.lifetime ∧
              ∀ τ ∈ Icc 0 (((records e₁).static b).neck.scale * (t - H.time e₁.succ)),
                (∀ i ≤ N, ∀ v : standardCapWindow D,
                  metricDerivNorm i (S.base.metric τ)
                    ((Q.val.metric τ).restrictOpen (standardCapWindow D))
                    (StandardCap.metric.restrictOpen (standardCapWindow D)) v < ε) ∧
                ∀ i ≤ 2, ∀ v : standardCapWindow D,
                  metricDerivNorm i (S.base.metric τ)
                    ((Q.val.metric τ).restrictOpen (standardCapWindow D))
                    (StandardCap.metric.restrictOpen (standardCapWindow D)) v < η) →
      (∀ (y₂ : (H.stage e₂.succ).Carrier), (H.toHistory.event e₂).RegularCrossing y y₂ →
        ∀ (b₂ : (H.toHistory.event e₂).RetainedBoundaryIndex) (z₂ : standardCapWindow
            p.modelRadius),
          StandardCap.transitionEnd < ‖z₂.val‖ → ‖z₂.val‖ ≤ StandardCap.transitionEnd + 10 →
          ((records e₂).static b₂).neck.scale ≤ 4 * (B * Q) →
          ((records e₂).static b₂).window z₂ ≠ y₂)) →
      (∀ (y₂ : (H.stage e₂.succ).Carrier), (H.toHistory.event e₂).RegularCrossing y y₂ →
        ∀ (b₂ : (H.toHistory.event e₂).RetainedBoundaryIndex) (z₂ : standardCapWindow
            p.modelRadius),
          StandardCap.transitionEnd < ‖z₂.val‖ → ‖z₂.val‖ ≤ StandardCap.transitionEnd + 10 →
          ((records e₂).static b₂).neck.scale ≤ 4 * (B * Q) →
          ((records e₂).static b₂).window z₂ ≠ y₂) := by
  obtain ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, hcmp⟩ :=
    exists_standard_comparison_of_cap_window_trace_tube_C11SP.{u} Θ hΘ hΘ1
  refine ⟨P, Creset, Cbirth, hP, hCreset, hCbirth, ?_⟩
  intro C D ε η hD hε hη N
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hcmp⟩ := hcmp C D ε η hD hε hη N
  refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro H p records hcanonical hRp hmp hζp qcan a₀ B Q θ hqcan hQ hθ hBθ hHI hlow
    e₁ e₂ hl t ht y A b x hanchor hage hscale hxD hbirth haq hδloc W hW htube hderivW hfinalW hSEP
  apply hSEP
  have hq : 0 < ((records e₁).static b).neck.scale := ((records e₁).static b).neck.scale_pos
  have hage' : t - H.time e₁.succ ≤ 4 * (B * θ) * (((records e₁).static b).neck.scale)⁻¹ := by
    rw [← div_eq_mul_inv]
    refine hage.trans ?_
    rw [div_le_div_iff₀ hQ hq]
    nlinarith [mul_le_mul_of_nonneg_left hscale hθ]
  exact hcmp H records hcanonical hRp hmp hζp qcan a₀ (4 * (B * θ)) hqcan hBθ
    hHI hlow e₂.castSucc (H.time e₂.succ) (H.toHistory.event e₂).incoming
    (H.toHistory.event_initial e₂) t ht.1 ht.2 e₁ hl y A b x hanchor hage' hxD hbirth haq
    hδloc W hW htube hderivW hfinalW


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
