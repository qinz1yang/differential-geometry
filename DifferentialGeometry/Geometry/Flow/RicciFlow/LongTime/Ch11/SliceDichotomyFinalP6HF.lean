import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceLateCgP6S3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceHistoryBridgeFinalP6M

/-!
# late 单切片二分的 final slab 孪生（O-CH11-HCLOSEF G2a，后缀 `_P6HF`）

`Local/SliceDichotomyLateCg_P6LS3` / `Local/SliceDichotomyLate_P6L3` 三层单切片引理的 **event + final 合取版**
（`_both_P6HF`）：常数只从底层 kernel 取一次（SLT 窗口 kernel
`exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_window_P6WB` 对 `(H, G)` 泛型；
CWP kernel `exists_capWindow_embedding_standard_close_late_P6LL` 对 `(k, s, Gk)` 泛型），第一合取项与原
event 版逐字，第二合取项是 final slab 孪生：`H := K.prefixAt (Fin.last _)`、
`G := (K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl`（以 `GF` + 形状等式给出）、
`hGi := K.final_initial hfin`、κ 桥 `tested_noncollapse_final_P6M`、final slab 窗口 pinching 单列。
共用常数是序列层"event 切片 / final 切片"统一二分（G2b）的前提。
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

/-- final stage 度量 = 限制后 final slab 的度量（`stageMetric_last_of_lt` + 定义等）。 -/
theorem RetainedCoreHistory.stageMetric_last_restrict_P6HF (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon) (v : ℝ) :
    K.toHistory.stageMetric (Fin.last K.eventCount) v =
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.base.metric v := by
  rw [ObservedHistory.stageMetric_last_of_lt (H := K.toHistory) (h := hfin) v]
  rfl

/-- **非 CWP 分支（单切片）：event slab 与 final slab 两版共用常数（`_both_P6HF`）**：
`slice_scalar_bound_of_not_capWindowPoint_window_pinch_P6LS3` 逐字（第一合取项）+ final slab 孪生
（`H := prefixAt last`、`G := (finalSlab hfin).restrictIncoming …`、`final_initial`、
`tested_noncollapse_final_P6M`；final slab 窗口 pinching 单列）。 -/
theorem RetainedCoreHistory.slice_scalar_bound_of_not_capWindowPoint_window_pinch_both_P6HF
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq : ℝ) :
    ∃ Q Λ Dcap Rrad ζ₀ Rad Bw : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧
    Dcap ≤ Rrad ∧ 0 < ζ₀ ∧ 0 < Bw ∧
    (∀ (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount) {p : CutoffParameters} (T₀ : ℝ)
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
      ∀ qd : ℝ, qd ≤ q → K.EventSlabsDerivative Ctime qd j.castSucc →
      (K.toHistory.event j).incoming.DerivativeBoundBefore Ctime qd v →
      (∀ x ∈ U, ∀ v' ∈ Ioo (K.time j.castSucc) v,
        v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ v' →
        q < (K.toHistory.event j).incoming.flow.scalar v' x →
        ∀ ξ : TangentSpace ThreeModel x,
          |scalarDifferential (K.toHistory.event j).incoming.flow v' x ξ| ≤
            Cgrad * (K.toHistory.event j).incoming.flow.scalar v' x *
              Real.sqrt ((K.toHistory.event j).incoming.flow.scalar v' x) *
              Real.sqrt (((K.toHistory.event j).incoming.flow.base.metric v').inner x ξ ξ)) →
      (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
        v - Bw / (K.toHistory.event j).incoming.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
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
          Q * (K.toHistory.event j).incoming.flow.scalar v w) ∧
    (∀ (K : RetainedCoreHistory.{u}) (hfin : K.time (Fin.last K.eventCount) < K.horizon)
      (GF : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount))
        K.horizon), GF = (K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl →
    ∀ {p : CutoffParameters} (T₀ : ℝ)
      (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        GeometricCutoffRecord K.toHistory i p),
      (∀ i hT b, ((records i hT).static b).hasCanonicalWindow) →
      Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
      (∀ i : Fin K.eventCount, Perelman.PhiAlmostNonnegative
        (K.toHistory.event i).incoming.flow
        (Ico (K.time i.castSucc) (K.time i.succ) ∩ Ici T₀) phi) →
      Perelman.PhiAlmostNonnegative GF.flow
        (Ico (K.time (Fin.last K.eventCount)) K.horizon ∩ Ici T₀) phi →
    ∀ (v : ℝ), K.time (Fin.last K.eventCount) < v → v < K.horizon →
    ∀ (w : (K.stage (Fin.last K.eventCount)).Carrier) (q ρ : ℝ),
      T₀ ≤ v - Bw / GF.flow.scalar v w →
      0 < q → q ≤ Cq * GF.flow.scalar v w →
      Λ ≤ GF.flow.scalar v w →
      Λ ≤ GF.flow.scalar v w * v →
      Λ ≤ ρ * Real.sqrt (GF.flow.scalar v w) →
    ∀ U : Set (K.stage (Fin.last K.eventCount)).Carrier,
      (∀ x ∈ riemannianBallOf (GF.flow.base.metric v) w
        (Rad / Real.sqrt (GF.flow.scalar v w)), x ∈ U) →
      (∀ x ∈ U, q < GF.flow.scalar v x →
        ∃ W : SpatialCanonicalWitness (GF.flow.base.metric v)
          ε C1 C2 x, W.capTubeHasNeckChart ε) →
      ∀ qd : ℝ, qd ≤ q → K.EventSlabsDerivative Ctime qd (Fin.last K.eventCount) →
      GF.DerivativeBoundBefore Ctime qd v →
      (∀ x ∈ U, ∀ v' ∈ Ioo (K.time (Fin.last K.eventCount)) v,
        v - Bw / GF.flow.scalar v w ≤ v' →
        q < GF.flow.scalar v' x →
        ∀ ξ : TangentSpace ThreeModel x,
          |scalarDifferential GF.flow v' x ξ| ≤
            Cgrad * GF.flow.scalar v' x *
              Real.sqrt (GF.flow.scalar v' x) *
              Real.sqrt ((GF.flow.base.metric v').inner x ξ ξ)) →
      (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
        v - Bw / GF.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
        K.time (Fin.last K.eventCount) < τ → (τ : ℝ) < K.horizon →
        ∀ z ∈ U, ∀ zz : (K.toHistory.stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρ → K.toHistory.isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel (K.toHistory.stageAt τ).Carrier
              (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ)
              (riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage τ) τ) zz b)) →
      (¬ ∃ (i : Fin K.eventCount) (hT : T₀ ≤ K.time i.succ) (hl : i.succ ≤ (Fin.last K.eventCount))
        (B : BackwardPointTrace K.toHistory i.succ (Fin.last K.eventCount) hl w)
        (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        B.point i.succ le_rfl hl = ((records i hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
          v - K.time i.succ ≤ 1 / 2 * (((records i hT).static b).neck.scale)⁻¹) →
      ∀ z ∈ riemannianBallOf (GF.flow.base.metric v) w
          (A / Real.sqrt (GF.flow.scalar v w)),
        GF.flow.scalar v z ≤
          Q * GF.flow.scalar v w) := by
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hD, hDR, hζ₀, hBw, hmain⟩ :=
    RetainedCoreHistory.exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_window_P6WB
      hεle κ C1 C2 hκ Ctime Cgrad hphi A hA Cq (1 / 2) (by norm_num)
  refine ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hD, hDR, hζ₀, hBw, ?_, ?_⟩
  · intro K j p T₀ records hcan hR hord hacc hpinch v hv1 hv2 w q ρ hT₀ hq hqC hΛR hΛt hΛρ U hU hW
      qd hqd hslabK hderG hgrad hnc hnot
    have hslabP := K.eventSlabsDerivative_prefixAt j.castSucc (fun i hi => hslabK i hi)
    have hncB := K.tested_noncollapse_eventPrefix_P6M j (κ := κ) (ρ := ρ)
      (a := v - Bw / (K.toHistory.event j).incoming.flow.scalar v w) (t := v) U hnc
      (K.prefixAt_time_last _)
    exact hmain (K.prefixAt j.castSucc) (K.prefixAt_time_last _) (K.toHistory.event j).incoming
      (K.event_initial j) hv1 hv2 w q ρ hq hqC hΛR hΛt
      T₀ hT₀ (fun i hT => K.geometricCutoffRecordOfPrefix j.castSucc
        (records (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) hT))
      (fun i hT b => hcan (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) hT b) hR hord hacc U hU
      hW
      (fun i first hf z _ Btr v' hv' _ hRv' =>
        hslabP i (Fin.castSucc_lt_last i) _ v' hv' (lt_of_le_of_lt hqd hRv'))
      (fun x _ v' hv' _ hRv' => hderG x v' hv' (lt_of_le_of_lt hqd hRv')) hgrad
      (fun i v' hv' ξ => hpinch (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i) v'
        ⟨hv'.1, hT₀.trans hv'.2⟩ ξ)
      (fun v' hv' ξ => hpinch j v' ⟨hv'.1, hT₀.trans hv'.2⟩ ξ) hncB hΛρ
      (by
        rintro ⟨i, hT, hl, Btr, b, x, h1, h2, h3⟩
        exact hnot ⟨Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i, hT,
          Fin.le_def.mpr (Fin.le_def.mp hl), K.backwardPointTraceOfPrefix j.castSucc Btr, b, x, h1,
          h2, h3⟩)
  · intro K hfin GF hGF p T₀ records hcan hR hord hacc hpinch hpinchF v hv1 hv2 w q ρ hT₀ hq hqC hΛR
      hΛt hΛρ U hU hW
      qd hqd hslabK hderG hgrad hnc hnot
    subst hGF
    have hslabP := K.eventSlabsDerivative_prefixAt (Fin.last K.eventCount) (fun i hi => hslabK i hi)
    have hncB := K.tested_noncollapse_final_P6M hfin (κ := κ) (ρ := ρ)
      (a := v - Bw / ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v w) (t :=
        v) U hnc
      (K.prefixAt_time_last _)
    exact hmain (K.prefixAt (Fin.last K.eventCount)) (K.prefixAt_time_last _) ((K.finalSlab
      hfin).restrictIncoming le_rfl hfin le_rfl)
      (K.final_initial hfin) hv1 hv2 w q ρ hq hqC hΛR hΛt
      T₀ hT₀ (fun i hT => K.geometricCutoffRecordOfPrefix (Fin.last K.eventCount)
        (records (Fin.castLE (Nat.le_of_lt_succ (Fin.last K.eventCount).isLt) i) hT))
      (fun i hT b => hcan (Fin.castLE (Nat.le_of_lt_succ (Fin.last K.eventCount).isLt) i) hT b) hR
        hord hacc U hU
      hW
      (fun i first hf z _ Btr v' hv' _ hRv' =>
        hslabP i (Fin.castSucc_lt_last i) _ v' hv' (lt_of_le_of_lt hqd hRv'))
      (fun x _ v' hv' _ hRv' => hderG x v' hv' (lt_of_le_of_lt hqd hRv')) hgrad
      (fun i v' hv' ξ => hpinch (Fin.castLE (Nat.le_of_lt_succ (Fin.last K.eventCount).isLt) i) v'
        ⟨hv'.1, hT₀.trans hv'.2⟩ ξ)
      (fun v' hv' ξ => hpinchF v' ⟨hv'.1, hT₀.trans hv'.2⟩ ξ) hncB hΛρ
      (by
        rintro ⟨i, hT, hl, Btr, b, x, h1, h2, h3⟩
        exact hnot ⟨Fin.castLE (Nat.le_of_lt_succ (Fin.last K.eventCount).isLt) i, hT,
          Fin.le_def.mpr (Fin.le_def.mp hl), K.backwardPointTraceOfPrefix (Fin.last K.eventCount)
            Btr, b, x, h1,
          h2, h3⟩)

/-- **CWP 分支（late，切片形）：event / final 两版共用常数（`_both_P6HF`）**：
`capWindow_branch_late_P6L3` 逐字 + final slab 孪生（P6LL kernel 取 `k := last`、`s := horizon`）。 -/
theorem RetainedCoreHistory.capWindow_branch_late_both_P6HF (C : ℝ≥0) :
    ∃ Cbirth : ℝ, 0 < Cbirth ∧
    ∀ (Dw D₂ η : ℝ), 0 < Dw → Dw < D₂ → 0 < η →
    ∃ Rr : ℝ, D₂ + 1 < Rr ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧ ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ 0 < δ₀ ∧
    (∀ (K : RetainedCoreHistory.{u}) {p : CutoffParameters} {T₀ : ℝ}
      (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        GeometricCutoffRecord K.toHistory i p),
      (∀ i hi b, ((records i hi).static b).hasCanonicalWindow) →
      Rr ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
    ∀ {pF : CutoffParameters}, (∀ i, GeometricCutoffRecord K.toHistory i pF) →
    ∀ δbound : ℝ, (∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        pF.delta (K.time i.succ) ≤ δbound) →
      δbound ≤ δ₀ →
    ∀ (qcan a₀ : ℝ), 0 < qcan →
      (∀ x, InFixedHamiltonIveyRegion (K.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (K.initialMetric 0) x) →
      (∀ i hi b, qcan ≤ Cbirth * ((records i hi).static b).neck.scale ∧
        1 ≤ a₀ * ((records i hi).static b).neck.scale) →
    ∀ (e : Fin K.eventCount), K.EventSlabsDerivative C qcan e.castSucc →
    ∀ v : ℝ, K.time e.castSucc < v → v < K.time e.succ →
      (K.toHistory.event e).incoming.DerivativeBoundBefore C qcan v →
    ∀ w : (K.stage e.castSucc).Carrier,
      (∃ (i : Fin K.eventCount) (hT : T₀ ≤ K.time i.succ) (hl : i.succ ≤ e.castSucc)
        (B : BackwardPointTrace K.toHistory i.succ e.castSucc hl w)
        (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        B.point i.succ le_rfl hl = ((records i hT).static b).window x ∧ ‖x.val‖ < Dw + 1 ∧
          v - K.time i.succ ≤ 1 / 2 * (((records i hT).static b).neck.scale)⁻¹) →
    ∃ (Ξ : standardCapWindow D₂ → (K.stage e.castSucc).Carrier)
      (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
      Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dw + 1 ∧
      ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
        τw ∈ Icc (0 : ℝ) (1 / 2) ∧
        ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
          metricDerivNorm m (localPullMetric (scaleMetric lam hlam
              (K.toHistory.stageMetric e.castSucc v)) Ξ hΞ)
            ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
            (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η) ∧
    (∀ (K : RetainedCoreHistory.{u}) {p : CutoffParameters} {T₀ : ℝ}
      (records : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        GeometricCutoffRecord K.toHistory i p),
      (∀ i hi b, ((records i hi).static b).hasCanonicalWindow) →
      Rr ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
    ∀ {pF : CutoffParameters}, (∀ i, GeometricCutoffRecord K.toHistory i pF) →
    ∀ δbound : ℝ, (∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
        pF.delta (K.time i.succ) ≤ δbound) →
      δbound ≤ δ₀ →
    ∀ (qcan a₀ : ℝ), 0 < qcan →
      (∀ x, InFixedHamiltonIveyRegion (K.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (K.initialMetric 0) x) →
      (∀ i hi b, qcan ≤ Cbirth * ((records i hi).static b).neck.scale ∧
        1 ≤ a₀ * ((records i hi).static b).neck.scale) →
    ∀ (hfin : K.time (Fin.last K.eventCount) < K.horizon)
      (GF : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount))
        K.horizon), GF = (K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl →
      K.EventSlabsDerivative C qcan (Fin.last K.eventCount) →
    ∀ v : ℝ, K.time (Fin.last K.eventCount) < v → v < K.horizon →
      GF.DerivativeBoundBefore C qcan v →
    ∀ w : (K.stage (Fin.last K.eventCount)).Carrier,
      (∃ (i : Fin K.eventCount) (hT : T₀ ≤ K.time i.succ) (hl : i.succ ≤ (Fin.last K.eventCount))
        (B : BackwardPointTrace K.toHistory i.succ (Fin.last K.eventCount) hl w)
        (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        B.point i.succ le_rfl hl = ((records i hT).static b).window x ∧ ‖x.val‖ < Dw + 1 ∧
          v - K.time i.succ ≤ 1 / 2 * (((records i hT).static b).neck.scale)⁻¹) →
    ∃ (Ξ : standardCapWindow D₂ → (K.stage (Fin.last K.eventCount)).Carrier)
      (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ) (z₀ : standardCapWindow D₂),
      Injective Ξ ∧ Ξ z₀ = w ∧ ‖z₀.val‖ < Dw + 1 ∧
      ∃ (lam : ℝ) (hlam : 0 < lam) (Q : StandardSolution) (τw : ℝ),
        τw ∈ Icc (0 : ℝ) (1 / 2) ∧
        ∀ (u : standardCapWindow D₂) (m : ℕ), m ≤ 2 →
          metricDerivNorm m (localPullMetric (scaleMetric lam hlam
              (K.toHistory.stageMetric (Fin.last K.eventCount) v)) Ξ hΞ)
            ((Q.val.metric τw).restrictOpen (standardCapWindow D₂))
            (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η) := by
  obtain ⟨Cbirth, hCbirth, hP⟩ :=
    RetainedCoreHistory.exists_capWindow_embedding_standard_close_late_P6LL.{u} C
  refine ⟨Cbirth, hCbirth, fun Dw D₂ η hDw hD₂ hη => ?_⟩
  obtain ⟨Rr, hRr, m₀, hm₀, ζ₀, δ₀, hζ₀, hδ₀, hP'⟩ := hP Dw D₂ η hDw hD₂ hη
  refine ⟨Rr, hRr, m₀, hm₀, ζ₀, δ₀, hζ₀, hδ₀, ?_, ?_⟩
  · intro K p T₀ records hcan hR hm hζ pF recordsF δb hdelta hδ qcan a₀ hq hHI hlow hbirth e hslab v
      hv1 hv2 hder w hcw
    have h := hP' K records hcan hR hm hζ recordsF δb hdelta hδ qcan a₀ hq hHI hlow hbirth
      e.castSucc
      (K.time e.succ) (K.toHistory.event e).incoming (K.event_initial e) hslab v hv1 hv2 hder w hcw
    obtain ⟨Ξ, hΞ, z₀, hinj, hz₀, hn, i, hi, b, Q, τw, hτw, hcl⟩ := h
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact ⟨Ξ, hΞ, z₀, hinj, hz₀, hn, _, _, Q, τw, hτw, hcl⟩
  · intro K p T₀ records hcan hR hm hζ pF recordsF δb hdelta hδ qcan a₀ hq hHI hlow hbirth hfin GF
      hGF hslab v hv1 hv2 hder w hcw
    subst hGF
    have h := hP' K records hcan hR hm hζ recordsF δb hdelta hδ qcan a₀ hq hHI hlow hbirth
      (Fin.last K.eventCount) K.horizon ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
        (K.final_initial hfin) hslab
      v hv1 hv2 hder w hcw
    obtain ⟨Ξ, hΞ, z₀, hinj, hz₀, hn, i, hi, b, Q, τw, hτw, hcl⟩ := h
    rw [K.stageMetric_last_restrict_P6HF hfin]
    exact ⟨Ξ, hΞ, z₀, hinj, hz₀, hn, _, _, Q, τw, hτw, hcl⟩

/-- **单切片二分：event / final 两版共用常数（`_both_P6HF`）**：`slice_dichotomy_late_Cg_window_P6LS3`
逐字 + final slab 孪生（stage 变量 `k = last`；U 侧前提在 `G := (finalSlab hfin).restrictIncoming …` 上）。 -/
theorem RetainedCoreHistory.slice_dichotomy_late_Cg_window_both_P6HF
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0) (Cg : ℝ)
    (hCg : 0 < Cg) {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {η₃ Lc : ℝ}
    (hη₃ : 0 < η₃) (hLc : 0 < Lc) :
    ∃ Cbirth : ℝ, 0 < Cbirth ∧ ∀ A Dd : ℝ, 1 ≤ A → 0 < Dd → ∃ QB Dcap D₂ : ℝ, 0 ≤ QB ∧
    Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) ≤ D₂ ∧
    ∃ (Λ Rad Bw Rmin ζmin δ₀ : ℝ) (m₀ : ℕ), 1 ≤ Λ ∧ 0 < Bw ∧ 0 < ζmin ∧ 0 < δ₀ ∧
    (∀ (K : RetainedCoreHistory.{u}) {p : CutoffParameters} (T₀ : ℝ)
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
    ∀ (Rn ρ : ℝ), 0 < Rn → qcan ≤ Cg * Rn → Λ ≤ Rn → Λ ≤ Rn * v → Λ ≤ ρ * Real.sqrt Rn →
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
                (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃)) ∧
    (∀ (K : RetainedCoreHistory.{u}) {p : CutoffParameters} (T₀ : ℝ)
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
    ∀ (hfin : K.time (Fin.last K.eventCount) < K.horizon)
      (GF : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount))
        K.horizon), GF = (K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl →
      Perelman.PhiAlmostNonnegative GF.flow
        (Ico (K.time (Fin.last K.eventCount)) K.horizon ∩ Ici T₀) phi →
      K.EventSlabsDerivative Ctime qcan (Fin.last K.eventCount) →
    ∀ v : ℝ, K.time (Fin.last K.eventCount) < v → v < K.horizon →
      GF.DerivativeBoundBefore Ctime qcan v →
    ∀ (Rn ρ : ℝ), 0 < Rn → qcan ≤ Cg * Rn → Λ ≤ Rn → Λ ≤ Rn * v → Λ ≤ ρ * Real.sqrt Rn →
      T₀ ≤ v - Bw / Rn →
    ∀ (k : Fin (K.eventCount + 1)), k = (Fin.last K.eventCount) →
    ∀ (z sk : (K.toHistory.stage k).Carrier) (sj : (K.stage (Fin.last K.eventCount)).Carrier), HEq
      sk sj →
    ∀ d1 : ENNReal, riemannianEDistOf (K.toHistory.stageMetric k v) sk z ≤ d1 →
    ∀ zj : (K.stage (Fin.last K.eventCount)).Carrier, HEq z zj →
    (∀ w : (K.stage (Fin.last K.eventCount)).Carrier,
      riemannianEDistOf (GF.flow.base.metric v) sj w ≤
        d1 + ENNReal.ofReal (Dd / Real.sqrt Rn) →
      riemannianEDistOf (GF.flow.base.metric v) zj w <
        ENNReal.ofReal (Dd / Real.sqrt Rn) →
      Rn ≤ GF.flow.scalar v w →
        (∀ x ∈ riemannianBallOf (GF.flow.base.metric v) w
              (Rad / Real.sqrt (GF.flow.scalar v w)),
          Cg * Rn < GF.flow.scalar v x →
          ∃ W : SpatialCanonicalWitness (GF.flow.base.metric v)
            ε C1 C2 x, W.capTubeHasNeckChart ε) ∧
        (∀ x ∈ riemannianBallOf (GF.flow.base.metric v) w
              (Rad / Real.sqrt (GF.flow.scalar v w)),
          ∀ v' ∈ Ioo (K.time (Fin.last K.eventCount)) v,
          v - Bw / GF.flow.scalar v w ≤ v' →
          Cg * Rn < GF.flow.scalar v' x →
          ∀ ξ : TangentSpace ThreeModel x,
            |scalarDifferential GF.flow v' x ξ| ≤
              Cgrad * GF.flow.scalar v' x *
                Real.sqrt (GF.flow.scalar v' x) *
                Real.sqrt ((GF.flow.base.metric v').inner x ξ ξ)) ∧
        (∀ (τ : Icc (0 : ℝ) K.toHistory.horizon),
          v - Bw / GF.flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
          K.time (Fin.last K.eventCount) < τ → (τ : ℝ) < K.horizon →
          ∀ z ∈ riemannianBallOf (GF.flow.base.metric v) w
                (Rad / Real.sqrt (GF.flow.scalar v w)),
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
                (StandardCap.metric.restrictOpen (standardCapWindow D₂)) u < η₃)) := by
  obtain ⟨Cbirth, hCbirth, hCWP⟩ := RetainedCoreHistory.capWindow_branch_late_both_P6HF.{u} Ctime
  refine ⟨Cbirth, hCbirth, fun A Dd hA hDd => ?_⟩
  have hAB : 0 < 2 * Dd * Real.sqrt A + 1 := by positivity
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, Rad, Bw, hQ, hΛ, hD, -, hζ₀, hBw, hmain, hmainF⟩ :=
    RetainedCoreHistory.slice_scalar_bound_of_not_capWindowPoint_window_pinch_both_P6HF hεle κ C1 C2
      hκ
      Ctime Cgrad hphi (2 * Dd * Real.sqrt A + 1) hAB Cg
  have hDpos : 0 < Dcap := StandardCap.transitionEnd_pos.trans hD
  have hDD₂ : Dcap < Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1) := by
    have : 0 ≤ 2 * Dd * Lc * Real.sqrt (2 * A) := by positivity
    linarith
  obtain ⟨Rr, -, m₀, -, ζ₁, δ₀, hζ₁, hδ₀, hcap, hcapF⟩ :=
    hCWP Dcap (Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1)) η₃ hDpos hDD₂ hη₃
  refine ⟨Q, Dcap, Dcap + 1 + (2 * Dd * Lc * Real.sqrt (2 * A) + 1), by linarith, le_rfl, Λ, Rad,
    Bw, max Rr Rrad, min ζ₀ ζ₁, δ₀, max m₀ 2, hΛ, hBw, lt_min hζ₀ hζ₁, hδ₀, ?_, ?_⟩
  · intro K p T₀ records hcan hRad hord hacc hpinch pF recordsF δb hdelta hδ qcan a₀ hq0 hHI hlow
      hbirth j hslab v hv1 hv2 hder Rn ρ hRn hqR hΛRn hΛv hΛρ hT₀ k hk z sk sj hs d1 hzd zj hzj hU
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
      obtain ⟨h1, h4, h5⟩ := hU w hw hzw hRw
      have hRw2 : Rn ≤ (K.toHistory.event j).incoming.flow.scalar v w := hRw
      have hρ0 : 0 < ρ := by
        by_contra hneg
        have : ρ * Real.sqrt Rn ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) (Real.sqrt_nonneg _)
        linarith
      have hT₀w : T₀ ≤ v - Bw / (K.toHistory.event j).incoming.flow.scalar v w :=
        hT₀.trans (by linarith [div_le_div_of_nonneg_left hBw.le hRn hRw2])
      exact hmain K j T₀ records hcan ((le_max_right _ _).trans hRad) ((le_max_right _ _).trans
        hord)
        (hacc.trans (min_le_left _ _)) hpinch v hv1 hv2 w (Cg * Rn) ρ
        hT₀w (lt_of_lt_of_le hq0 hqR) (mul_le_mul_of_nonneg_left hRw2 hCg.le) (hΛRn.trans hRw)
        (hΛv.trans (mul_le_mul_of_nonneg_right hRw hv0))
        (hΛρ.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hRw) hρ0.le)) _ (fun _ h => h) h1
        qcan hqR hslab hder h4 h5 hncw x hx
    · intro w _ hcw
      exact hcap K records hcan ((le_max_left _ _).trans hRad) ((le_max_left _ _).trans hord)
        (hacc.trans (min_le_right _ _)) recordsF δb hdelta hδ qcan a₀ hq0 hHI hlow hbirth
        j hslab v hv1 hv2 hder w hcw
  · intro K p T₀ records hcan hRad hord hacc hpinch pF recordsF δb hdelta hδ qcan a₀ hq0 hHI hlow
      hbirth hfin GF hGF hpinchF hslab v hv1 hv2 hder Rn ρ hRn hqR hΛRn hΛv hΛρ hT₀ k hk z sk sj hs
        d1 hzd zj hzj hU
    subst hGF
    subst hk
    obtain rfl := eq_of_heq hs
    obtain rfl := eq_of_heq hzj
    have hv0 : 0 ≤ v := (K.toHistory.time_nonneg _).trans hv1.le
    refine ⟨fun w => ∃ (i : Fin K.eventCount) (hT : T₀ ≤ K.time i.succ) (hl : i.succ ≤ (Fin.last
      K.eventCount))
        (B : BackwardPointTrace K.toHistory i.succ (Fin.last K.eventCount) hl w)
        (b : (K.toHistory.event i).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        B.point i.succ le_rfl hl = ((records i hT).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
          v - K.time i.succ ≤ 1 / 2 * (((records i hT).static b).neck.scale)⁻¹, ?_, ?_⟩
    · intro w hzw hncw hRw x hx
      rw [K.stageMetric_last_restrict_P6HF hfin] at hzd hzw hRw hx ⊢
      have hw : riemannianEDistOf (((K.finalSlab hfin).restrictIncoming le_rfl hfin
        le_rfl).flow.base.metric v) sk w ≤
          d1 + ENNReal.ofReal (Dd / Real.sqrt Rn) :=
        (riemannianEDistOf_triangle _ _ _ _).trans (add_le_add hzd hzw.le)
      obtain ⟨h1, h4, h5⟩ := hU w hw hzw hRw
      have hRw2 : Rn ≤ ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v w :=
        hRw
      have hρ0 : 0 < ρ := by
        by_contra hneg
        have : ρ * Real.sqrt Rn ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) (Real.sqrt_nonneg _)
        linarith
      have hT₀w : T₀ ≤ v - Bw / ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar
        v w :=
        hT₀.trans (by linarith [div_le_div_of_nonneg_left hBw.le hRn hRw2])
      exact hmainF K hfin _ rfl T₀ records hcan ((le_max_right _ _).trans hRad) ((le_max_right _
        _).trans hord)
        (hacc.trans (min_le_left _ _)) hpinch hpinchF v hv1 hv2 w (Cg * Rn) ρ
        hT₀w (lt_of_lt_of_le hq0 hqR) (mul_le_mul_of_nonneg_left hRw2 hCg.le) (hΛRn.trans hRw)
        (hΛv.trans (mul_le_mul_of_nonneg_right hRw hv0))
        (hΛρ.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hRw) hρ0.le)) _ (fun _ h => h) h1
        qcan hqR hslab hder h4 h5 hncw x hx
    · intro w _ hcw
      exact hcapF K records hcan ((le_max_left _ _).trans hRad) ((le_max_left _ _).trans hord)
        (hacc.trans (min_le_right _ _)) recordsF δb hdelta hδ qcan a₀ hq0 hHI hlow hbirth
        hfin _ rfl hslab v hv1 hv2 hder w hcw

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
