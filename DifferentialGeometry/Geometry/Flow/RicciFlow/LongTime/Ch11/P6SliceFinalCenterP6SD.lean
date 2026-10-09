import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceLateCgFinalLocalP6SD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10FinalSlabCeilingCXJF

/-!
# final slab 中心的 D1 三分 producer：去 `hstaySlCF`（O-CH11-SLICEDICH G5，后缀 `_P6SD`）

G4 的 F6 / F7 在 final slab 中心吃 `hstaySlCF`。G3 的三分法在 final 用不上的两处（`hbound_of_eventSlabs_P6SB2`
的 `activeStage t < last`、SLTPROD / SLICE-BCBD2 stay 链的 `hσlast`）换成树内 final 通用件：
* `hbound_final_P6SD`（PROVED）：event 段用 `hslabK`，final 段用 `hderF`（同一阈值 `Q`）；
* `traceDt_finalCenter_P6SD`（PROVED）：(B) clipped reciprocal 反证；(C) CXJF final 通用 stay
  `hstop_final_CXJF` + 条件保护 `hprotC_gen_of_ceiling_CXJF` 以 `(v, w, L/2)` 锚定，再经 hgood 时间分量。
生成器 `build-logs/scratch/O-CH11-SLICEDICH/gen/gen5.py`。不声称 J10 已去。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

/-- **final slab 内的 `hbound`（`_P6SD`，PROVED）**：`hbound_of_eventSlabs_P6SB2` 的 final 版——history trace
`A : [a, t]`（`t` 可在 final slab），event slab 段用 `EventSlabsDerivative C q last`，final slab 段用限制后
final slab 的 `DerivativeBoundBefore C q horizon`。 -/
theorem RetainedCoreHistory.hbound_final_P6SD (K : RetainedCoreHistory.{u}) {C : ℝ≥0} {q : ℝ}
    (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    (hslab : K.EventSlabsDerivative C q (Fin.last K.eventCount))
    (hderF : ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).DerivativeBoundBefore C q
      K.horizon)
    {a t : Icc (0 : ℝ) K.toHistory.horizon} (hat : a ≤ t)
    {y : (K.toHistory.stageAt t).Carrier}
    (A : BackwardPointTrace K.toHistory (K.toHistory.activeStage a) (K.toHistory.activeStage t)
      (K.toHistory.activeStage_mono hat) y) :
    ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      K.toHistory.time (K.toHistory.activeStage v) < (v : ℝ) → (v : ℝ) < K.toHistory.horizon →
      q < metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
        (A.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
          (K.toHistory.activeStage_mono hvt)) →
      |derivWithin (fun s => metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) s)
        (A.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
          (K.toHistory.activeStage_mono hvt))) (Iic (v : ℝ)) v| ≤
        C * metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
          (A.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
            (K.toHistory.activeStage_mono hvt)) ^ 2 := by
  intro v hav hvt htv hvH hq
  by_cases hlast : K.toHistory.activeStage v = Fin.last K.eventCount
  · have hgenF : ∀ (m : Fin (K.eventCount + 1)) (hm : m = Fin.last K.eventCount)
        (h1 : K.toHistory.activeStage a ≤ m) (h2 : m ≤ K.toHistory.activeStage t),
        K.toHistory.time m < (v : ℝ) →
        q < metricScalarAt (K.toHistory.stageMetric m v) (A.point m h1 h2) →
        |derivWithin (fun s => metricScalarAt (K.toHistory.stageMetric m s) (A.point m h1 h2))
            (Iic (v : ℝ)) v| ≤
          C * metricScalarAt (K.toHistory.stageMetric m v) (A.point m h1 h2) ^ 2 := by
      intro m hm h1 h2 htm hqm
      subst hm
      simp only [K.stageMetric_last_restrict_P6HF hfin] at hqm ⊢
      exact hderF _ v ⟨htm, hvH⟩ hqm
    exact hgenF _ hlast _ _ htv hq
  · have hlt : K.toHistory.activeStage v < Fin.last K.eventCount :=
      lt_of_le_of_ne (Fin.le_last _) hlast
    obtain ⟨e, he⟩ := Fin.exists_castSucc_eq.mpr (ne_of_lt hlt)
    have hvlt : (K.toHistory.activeStage v).val < K.eventCount := by
      rw [← he]
      exact e.isLt
    have hnext := K.toHistory.activeStage_before_next v hvlt
    have hfin' : (⟨(K.toHistory.activeStage v).val + 1, by omega⟩ : Fin (K.eventCount + 1)) =
        e.succ := by
      apply Fin.ext
      change (K.toHistory.activeStage v).val + 1 = e.succ.val
      rw [Fin.val_succ, ← he, Fin.val_castSucc]
    have hv2 : (v : ℝ) < K.toHistory.time e.succ :=
      hnext.trans_eq (congrArg K.toHistory.time hfin')
    have hgen : ∀ (m : Fin (K.eventCount + 1)) (hm : e.castSucc = m)
        (h1 : K.toHistory.activeStage a ≤ m) (h2 : m ≤ K.toHistory.activeStage t),
        K.toHistory.time m < (v : ℝ) →
        q < metricScalarAt (K.toHistory.stageMetric m v) (A.point m h1 h2) →
        |derivWithin (fun s => metricScalarAt (K.toHistory.stageMetric m s) (A.point m h1 h2))
            (Iic (v : ℝ)) v| ≤
          C * metricScalarAt (K.toHistory.stageMetric m v) (A.point m h1 h2) ^ 2 := by
      intro m hm h1 h2 htm hqm
      subst hm
      simp only [ObservedHistory.stageMetric_castSucc_apply] at hqm ⊢
      exact hslab e (Fin.castSucc_lt_last e) _ v ⟨htm, hv2⟩ hqm
    exact hgen _ he _ _ htv hq

/-- **final slab 中心的 D1 单实例（`_P6SD`，PROVED）**：情形 (B) / (C)（调用方先处理 (A)
`R(v′, x) > Q`）。中心 `w` 在 final slab（`time last < v < horizon`），U 点 `z ∈ B(w, Rad/√R(v,w))` 的
history trace `Btr` 回到 event slab `i` 的时刻 `v′`（guard `(v − v′)·max(Cg·R, R(v, z)) ≤ c⋆`）。
(B) `R(v, z) > 2Q`：`hbound_final_P6SD` + clipped reciprocal 与 `R(v′, x) ≤ Q` 矛盾；
(C)：final 通用 stay `hstop_final_CXJF` 以 `(v, w, L/2)` 锚定，保护 ⇐ `hprotC_gen_of_ceiling_CXJF`
+ `hsepQ`，再经 hgood 时间分量。 -/
theorem RetainedCoreHistory.traceDt_finalCenter_P6SD {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (hCg : 1 ≤ Cg) (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    (GF : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount))
      K.horizon) (hGF : GF = (K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
    {Q : ℝ} (hQ0 : 0 < Q) (hslab : K.EventSlabsDerivative Ctime' Q (Fin.last K.eventCount))
    (hderF : GF.DerivativeBoundBefore Ctime' Q K.horizon)
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier} {rX : ℝ} (hrX : 0 < rX)
    (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT rX)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - rX ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {aP : ℝ} (haP : 0 ≤ aP)
    (hpin : ∀ (s : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt s).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage s) s) (aP + s) x)
    (y : (K.toHistory.stageAt σ).Carrier) {R L : ℝ} (hR1 : 1 ≤ R) (hL0 : 0 ≤ L)
    (hgood : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hdfin : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
        (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
          (K.toHistory.activeStage_mono hsT)) y ≠ ⊤)
    (hRa : 1 ≤ R * aSeed) {T₀X : ℝ} (hT₀X : T₀X ≤ aSeed)
    (hOldX : ∀ e : Fin K.eventCount, T₀X ≤ K.toHistory.time e.succ →
      (K.toHistory.event e).old = (K.toHistory.event e).transition.trace.retainedCore)
    {p : CutoffParameters} {T₀ : ℝ}
    (records : ∀ e : Fin K.eventCount, T₀ ≤ K.time e.succ → GeometricCutoffRecord K.toHistory e p)
    (hcan : ∀ (e : Fin K.eventCount) (he : T₀ ≤ K.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (hacc : p.modelAccuracy ≤ 1 / 2) (hDm : StandardCap.transitionEnd + 10 < p.modelRadius)
    (hnc : ∀ (e : Fin K.eventCount) (he : T₀ ≤ K.time e.succ)
      (w : (K.toHistory.stage e.succ).Carrier),
      (∀ b, metricScalarAt (K.toHistory.event e).outputMetric w <
        ((records e he).static b).neck.scale / 2) →
      ¬ ∃ (b : (K.toHistory.event e).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        w = ((records e he).static b).window x ∧ ‖x.val‖ < p.modelRadius)
    (hsepQ : ∀ (e : Fin K.eventCount) (he : T₀ ≤ K.time e.succ) b,
      2 * max (3 / rX ^ 2) (4 * Q) < ((records e he).static b).neck.scale)
    {κs Rad : ℝ} (hκdef : κs = min (min (rX / 50) (localPropagationRadius C2' / 2))
      (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4)))))
    (hLρ : 8 * localPropagationRadius C2' ≤ L)
    (hLc : 4 * (max Rad 0 + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κs) + 4 ≤ L)
    {v : ℝ} (hv1 : K.time (Fin.last K.eventCount) < v) (hv2 : v < K.horizon) (hvσ : v ≤ σ)
    (hva : (aSeed : ℝ) ≤ v)
    (hLJ : ∀ s : ℝ, v - (L / 2) ^ 2 / R ≤ s → (σ : ℝ) - L ^ 2 / R ≤ s)
    (w : (K.stage (Fin.last K.eventCount)).Carrier)
    (h1 : K.toHistory.activeStage aSeed ≤ Fin.last K.eventCount)
    (h2 : Fin.last K.eventCount ≤ K.toHistory.activeStage Tn)
    (hwseed : riemannianEDistOf (GF.flow.base.metric v)
        (seedTrace.point (Fin.last K.eventCount) h1 h2) w ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / 2 / Real.sqrt R))
    (hRw : R ≤ GF.flow.scalar v w)
    (i : Fin K.eventCount) (first : Fin (K.eventCount + 1)) (hf : first ≤ i.castSucc)
    (z : (K.stage (Fin.last K.eventCount)).Carrier)
    (hz : z ∈ riemannianBallOf (GF.flow.base.metric v) w (Rad / Real.sqrt (GF.flow.scalar v w)))
    (Btr : BackwardPointTrace K.toHistory first (Fin.last K.eventCount)
      (hf.trans (Fin.castSucc_lt_last i).le) z)
    {v' : ℝ} (hv' : v' ∈ Ioo (K.time i.castSucc) (K.time i.succ))
    (ha : (aSeed : ℝ) ≤ v') (hLτ : (σ : ℝ) - L ^ 2 / R ≤ v') (hT₀v' : T₀ ≤ v')
    (hg : (v - v') * max (Cg * R) (GF.flow.scalar v z) ≤ 1 / (2 * max (Ctime' : ℝ) 1))
    (hRx : Cg * R < (K.toHistory.event i).incoming.flow.scalar v'
      (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le))
    (hAQ : (K.toHistory.event i).incoming.flow.scalar v'
      (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) ≤ Q) :
    |derivWithin (fun s => (K.toHistory.event i).incoming.flow.scalar s
        (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le)) (Iic v') v'| ≤
      Ctime' * (K.toHistory.event i).incoming.flow.scalar v'
        (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) ^ 2 := by
  subst hGF
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  have hρ : 0 < localPropagationRadius C2' := localPropagationRadius_pos hC2
  have hm1 : (1 : ℝ) ≤ max (Ctime' : ℝ) 1 := le_max_right _ _
  have hc0 : (0 : ℝ) ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by positivity
  have hc1 : 1 / (2 * max (Ctime' : ℝ) 1) ≤ 1 := by
    rw [div_le_one (by linarith only [hm1])]
    linarith only [hm1]
  have hCc : (Ctime' : ℝ) * (1 / (2 * max (Ctime' : ℝ) 1)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith only [le_max_left (Ctime' : ℝ) 1]
  have hv'v : v' < v :=
    hv'.2.trans_le ((K.toHistory.time_strictMono.monotone (Fin.le_last i.succ)).trans hv1.le)
  have htv0 : 0 ≤ v - v' := sub_nonneg.mpr hv'v.le
  have h0 : (0 : ℝ) ≤ v' := (K.toHistory.time_nonneg _).trans hv'.1.le
  have h0v : (0 : ℝ) ≤ v := h0.trans hv'v.le
  let vJ : Icc (0 : ℝ) K.toHistory.horizon := ⟨v, h0v, hvσ.trans σ.2.2⟩
  let vI : Icc (0 : ℝ) K.toHistory.horizon := ⟨v', h0, (hv'v.le.trans hvσ).trans σ.2.2⟩
  have hvIJ : vI ≤ vJ := hv'v.le
  have hvJσ : vJ ≤ σ := hvσ
  have hvJT : vJ ≤ Tn := hvJσ.trans hsT
  have hvJa : aSeed ≤ vJ := hva
  have hvIa : aSeed ≤ vI := ha
  have hactJ : K.toHistory.activeStage vJ = Fin.last K.eventCount :=
    K.toHistory.activeStage_eq_last_of_time_last_le vJ hv1.le
  have hactI : K.toHistory.activeStage vI = i.castSucc :=
    K.toHistory.activeStage_eq_of_slab_P6L3 i vI hv'.1.le hv'.2
  let z' : (K.toHistory.stageAt vJ).Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hactJ.symm) z
  have hzz : HEq z' z := cast_heq _ _
  have hfI : first ≤ K.toHistory.activeStage vI := by
    rw [hactI]
    exact hf
  have hIl : K.toHistory.activeStage vI ≤ Fin.last K.eventCount := Fin.le_last _
  obtain ⟨A, hAeq⟩ := exists_trace_transport_P6SP (K.toHistory.activeStage_mono hvIJ) z'
    hactJ.symm hzz.symm (Btr.restrictFirst hfI hIl)
  have hpt : HEq (A.point (K.toHistory.activeStage vI) (K.toHistory.activeStage_mono le_rfl)
      (K.toHistory.activeStage_mono hvIJ))
      (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) := by
    rw [hAeq (K.toHistory.activeStage vI) (K.toHistory.activeStage_mono le_rfl) hIl
      (K.toHistory.activeStage_mono hvIJ)]
    exact point_heq_of_eq_P6M2 Btr hactI (hfI.trans (K.toHistory.activeStage_mono le_rfl)) hIl hf
      (Fin.castSucc_lt_last i).le
  have hsc := scalar_stage_eq_P6L2 (H := K.toHistory) i hactI (vI : ℝ) _ _ hpt
  have hscJ := K.scalar_stage_eq_last_P6HF hfin hactJ (vJ : ℝ) z' z hzz
  by_cases hB : 2 * Q < ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z
  · -- (B) 不可能：沿 trace 的 clipped reciprocal 下界
    exfalso
    have hRz : (v - v') * ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z ≤
        1 / (2 * max (Ctime' : ℝ) 1) :=
      (mul_le_mul_of_nonneg_left (le_max_right _ _) htv0).trans hg
    have htime : (Ctime' : ℝ) * metricScalarAt
        (K.toHistory.stageMetric (K.toHistory.activeStage vJ) vJ) z' * ((vJ : ℝ) - vI) ≤ 1 / 2 := by
      rw [hscJ]
      change (Ctime' : ℝ) *
        ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z * (v - v') ≤ 1 / 2
      have h1' := mul_le_mul_of_nonneg_left hRz Ctime'.coe_nonneg
      calc (Ctime' : ℝ) * ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z *
            (v - v')
          = (Ctime' : ℝ) * ((v - v') *
            ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z) := by ring
        _ ≤ 1 / 2 := h1'.trans hCc
    have hlow := BackwardPointTrace.scalar_gt_of_time_local_derivative_control_P6SB2 hvIJ A hQ0
      (K.hbound_final_P6SD hfin hslab hderF hvIJ A) (by rw [hscJ]; exact hB) htime vI le_rfl hvIJ
    rw [hsc] at hlow
    exact absurd hlow (not_lt.mpr hAQ)
  push Not at hB
  -- (C) CXJD final 通用 stay，以 (v, w, L/2) 锚定
  obtain ⟨Qb, hQbdef⟩ : ∃ Qb : ℝ, Qb = max (max
      (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z / R) Cg) 1 :=
    ⟨_, rfl⟩
  obtain ⟨Tt, hTdef⟩ : ∃ Tt : ℝ, Tt = 1 / (2 * max (Ctime' : ℝ) 1) / Qb := ⟨_, rfl⟩
  have hQb1 : (1 : ℝ) ≤ Qb := by rw [hQbdef]; exact le_max_right _ _
  have hQbpos : 0 < Qb := lt_of_lt_of_le one_pos hQb1
  have hQbM : Qb * R ≤
      max (Cg * R) (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z) := by
    have hCgR : R ≤ Cg * R := le_mul_of_one_le_left hR0.le hCg
    have hle : Qb ≤ max (Cg * R)
        (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z) / R := by
      rw [hQbdef]
      refine max_le (max_le ?_ ?_) ?_
      · exact div_le_div_of_nonneg_right (le_max_right _ _) hR0.le
      · rw [le_div_iff₀ hR0]
        exact le_max_left _ _
      · rw [le_div_iff₀ hR0, one_mul]
        exact hCgR.trans (le_max_left _ _)
    calc Qb * R ≤ max (Cg * R)
          (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z) / R * R :=
        mul_le_mul_of_nonneg_right hle hR0.le
      _ = _ := div_mul_cancel₀ _ hR0.ne'
  have hQbQ : Qb * R ≤ 2 * Q := hQbM.trans (max_le (by linarith only [hRx, hAQ, hQ0]) hB)
  have hstep : 2 * (Ctime' : ℝ) * Qb * Tt ≤ 1 := by
    have hT : 2 * (Ctime' : ℝ) * Qb * Tt = (Ctime' : ℝ) / max (Ctime' : ℝ) 1 := by
      rw [hTdef]
      field_simp
    rw [hT, div_le_one (by linarith only [hm1])]
    exact le_max_left _ _
  have hdepth : (vJ : ℝ) - vI ≤ Tt / R := by
    change v - v' ≤ Tt / R
    rw [hTdef, div_div, le_div_iff₀ (mul_pos hQbpos hR0)]
    exact (mul_le_mul_of_nonneg_left hQbM htv0).trans hg
  have hRle : (v - v') * R ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by
    have h3 := mul_le_mul_of_nonneg_left ((le_mul_of_one_le_left hR0.le hCg).trans
      (le_max_left (Cg * R)
        (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z))) htv0
    exact h3.trans hg
  have hTv : v - v' ≤ 1 / R := by
    rw [le_div_iff₀ hR0]
    exact hRle.trans hc1
  have haL : (vJ : ℝ) - (L / 2) ^ 2 / R ≤ vI := by
    have hκpos : 0 < κs := by
      rw [hκdef]
      exact lt_min (lt_min (div_pos hrX (by norm_num)) (div_pos hρ (by norm_num)))
        (lt_min one_pos (by positivity))
    have hnn : 0 ≤ max Rad 0 + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κs :=
      add_nonneg (le_max_right _ _) (div_nonneg (by positivity) hκpos.le)
    have hL2 : (2 : ℝ) ≤ L := by linarith only [hLc, hnn]
    have h1L : 1 / R ≤ (L / 2) ^ 2 / R :=
      div_le_div_of_nonneg_right (by nlinarith only [hL2]) hR0.le
    change v - (L / 2) ^ 2 / R ≤ v'
    linarith only [h1L, hTv]
  have hRa' : 1 ≤ R * vI := by
    have := mul_le_mul_of_nonneg_left ha hR0.le
    change 1 ≤ R * v'
    linarith only [this, hRa]
  let w' : (K.toHistory.stageAt vJ).Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hactJ.symm) w
  have hww : HEq w' w := cast_heq _ _
  have hwJ : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage vJ) vJ)
        (seedTrace.point (K.toHistory.activeStage vJ)
          (K.toHistory.activeStage_mono hvJa) (K.toHistory.activeStage_mono hvJT)) w' ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / 2 / Real.sqrt R) := by
    have hs := point_heq_of_eq_P6M2 seedTrace hactJ (K.toHistory.activeStage_mono hvJa)
      (K.toHistory.activeStage_mono hvJT) h1 h2
    exact (K.edist_stage_eq_last_P6HF hfin hactJ v _ w' _ w hs hww).trans_le hwseed
  have hc' : 0 ≤ L / 2 / Real.sqrt R :=
    div_nonneg (div_nonneg hL0 (by norm_num)) (Real.sqrt_nonneg _)
  have hbud : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage vJ) vJ)
        (seedTrace.point (K.toHistory.activeStage vJ)
          (K.toHistory.activeStage_mono hvJa) (K.toHistory.activeStage_mono hvJT)) w' +
        ENNReal.ofReal (L / 2 / Real.sqrt R) ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R) := by
    refine (add_le_add hwJ le_rfl).trans_eq ?_
    rw [add_assoc, ← ENNReal.ofReal_add hc' hc']
    congr 2
    ring
  have hdw := ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hdfin, ENNReal.ofReal_ne_top⟩) hwJ
  have hrr : Rad / Real.sqrt (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar
      v w) ≤ max Rad 0 / Real.sqrt R :=
    (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans
      (div_le_div_of_nonneg_left (le_max_right _ _) (Real.sqrt_pos.2 hR0)
        (Real.sqrt_le_sqrt hRw))
  have hzy : z' ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage vJ) vJ) w'
      (max Rad 0 / Real.sqrt R) := by
    have hz2 := riemannianBallOf_mono _ _ hrr hz
    change riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage vJ) vJ) w' z' <
      ENNReal.ofReal (max Rad 0 / Real.sqrt R)
    rw [K.edist_stage_eq_last_P6HF hfin hactJ (vJ : ℝ) w' z' w z hww hzz]
    exact hz2
  have hzc : metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage vJ) vJ) z' ≤
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z / R * R :=
    le_of_eq (by rw [hscJ, div_mul_cancel₀ _ hR0.ne'])
  have hQb : max (max (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z / R)
      Cg) 1 ≤ Qb := le_of_eq hQbdef.symm
  obtain ⟨hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hnum⟩ := cstar_numerics_P6SP (Qb := Qb) (R := R)
    (Rad := max Rad 0) (L := L / 2) hrX hρ hc0 hQb1 hR1 hκdef (by linarith only [hLρ])
    (by linarith only [hLc])
  have hTeq : Tt / R = 1 / (2 * max (Ctime' : ℝ) 1) / Qb / R := by rw [hTdef]
  rw [← hTeq] at hnum
  let rec' : ∀ e : Fin K.eventCount, (vI : ℝ) ≤ K.toHistory.time e.succ →
      GeometricCutoffRecord K.toHistory e p := fun e he => records e (hT₀v'.trans he)
  have hgood' : ∀ (v'' : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v'') (hvs : v'' ≤ vJ),
      (vJ : ℝ) - (L / 2) ^ 2 / R ≤ (v'' : ℝ) →
      ∀ z'' : (K.toHistory.stageAt v'').Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v'') v'')
            (seedTrace.point (K.toHistory.activeStage v'') (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hvJT))) z'' ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage vJ) vJ)
              (seedTrace.point (K.toHistory.activeStage vJ) (K.toHistory.activeStage_mono hvJa)
                (K.toHistory.activeStage_mono hvJT)) w' +
            ENNReal.ofReal (L / 2 / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v'') v'') z'' →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v'' z'' :=
    fun v'' hav'' hvs'' hw'' z'' hd'' hR'' =>
      hgood v'' hav'' (hvs''.trans hvJσ) (hLJ _ hw'') z'' (hd''.trans hbud) hR''
  have hprot := ObservedHistory.hprotC_gen_of_ceiling_CXJF K haT hsmall hclock seedTrace hvJT hvJa
    w' (L / 2) hR0 (by linarith only [hL0]) hgood' hQb hstep hvIa hvIJ haL hdepth hzc A rec' hDm
    (fun e he w'' hw'' => hnc e (hT₀v'.trans he) w'' hw'')
    (fun e he b _ => by
      have hS := hsepQ e (hT₀v'.trans he) b
      have hmx : max (3 / rX ^ 2) (2 * (Qb * R)) ≤ max (3 / rX ^ 2) (4 * Q) :=
        max_le_max le_rfl (by linarith only [hQbQ])
      linarith only [hS, hmx])
  have hstop := ObservedHistory.hstop_final_CXJF hC2 K haT hsmall hclock seedTrace haP hpin hvJT
    hvJa w' (L / 2) hR0 hgood' hQb hstep hvIa hvIJ hv2 haL hdepth hRa' hzc A hℓ hKℓ hℓr hKr hKC
    hℓρ hρL le_rfl rec' (fun e he => hOldX e (hT₀X.trans (ha.trans he)))
    (fun e he b => hcan e (hT₀v'.trans he) b) hacc hDm hprot hzy hdw hnum
  have hd := (hstop vI le_rfl hvIJ).trans hbud
  have hRm : Cg * R ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage vI) vI)
      (A.point (K.toHistory.activeStage vI) (K.toHistory.activeStage_mono le_rfl)
        (K.toHistory.activeStage_mono hvIJ)) := by
    rw [hsc]
    exact hRx.le
  have htv : K.toHistory.time (K.toHistory.activeStage vI) < (vI : ℝ) := by
    rw [hactI]
    exact hv'.1
  have hvh : (vI : ℝ) < K.toHistory.horizon := hv'v.trans hv2
  have hg2 := (hgood vI hvIa (hvIJ.trans hvJσ) hLτ _ hd hRm).2 htv hvh
  exact K.toHistory.deriv_of_stage_P6SD i hactI v' _ _ hpt hg2

/-- **F6″ final slab U 侧块扩展 ⇐ `hgood` + `hclosCF` + 先验供给（`hslabK` / `hderF`）+ `hscaleK` + CXJD 族
（`_P6SD`，PROVED ⇐ 这些前提；**无 `hstaySlCF`**）**：G4b F6 的孪生，final slab 中心的 D1 改由三分生产：
(A) `hslabK` 逐点；(B) / (C) `traceDt_finalCenter_P6SD`。 -/
theorem ObservedHistory.hUVCF_of_selection_Cg_sepRho_P6SD {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2')
    {κ Aκ : ℝ} {K : ℕ → RetainedCoreHistory.{u}}
    (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl)
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier) (R L r ρV : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v) ((K n).toHistory.activeStage_mono
              hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v) z
          →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono
            (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hκRF : ∀ᶠ n in atTop, ∀ (c : ((K n).toHistory.stage (Fin.last (K
      n).toHistory.eventCount)).Carrier)
      (U : Set ((K n).toHistory.stage (Fin.last (K n).toHistory.eventCount)).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (K n).toHistory.time (Fin.last (K n).toHistory.eventCount) < τ → (τ : ℝ) < (K
          n).toHistory.horizon →
        ∀ z ∈ U, ∀ zz cc : ((K n).toHistory.stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (K n).toHistory.time (Fin.last (K n).toHistory.eventCount) < τ → (τ : ℝ) < (K
          n).toHistory.horizon →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((K n).toHistory.stageAt τ).Carrier, HEq cc c
          →
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
              ((seedTrace n).point ((K n).toHistory.activeStage τ) ((K n).toHistory.activeStage_mono
                hav)
                ((K n).toHistory.activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (K n).toHistory.time (Fin.last (K n).toHistory.eventCount) < τ → (τ : ℝ) < (K
          n).toHistory.horizon →
        ∀ z ∈ U, ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
              ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
              (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ) zz
                b))
    (hclosCF : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (v : ℝ), (K n).toHistory.time (Fin.last (K n).toHistory.eventCount) < v →
        v < (K n).toHistory.horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : (Fin.last (K n).toHistory.eventCount) ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory (Fin.last (K n).toHistory.eventCount) ((K
          n).toHistory.activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ (Fin.last (K n).toHistory.eventCount))
        (h2 : (Fin.last (K n).toHistory.eventCount) ≤ (K n).toHistory.activeStage (Tn n)) (w : ((K
          n).toHistory.stage (Fin.last (K n).toHistory.eventCount)).Carrier),
        riemannianEDistOf ((K n).toHistory.stageMetric (Fin.last (K n).toHistory.eventCount) v)
            ((seedTrace n).point (Fin.last (K n).toHistory.eventCount) h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((K n).toHistory.stageMetric (Fin.last (K n).toHistory.eventCount) v)
            (tr.point (Fin.last (K n).toHistory.eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd /
              Real.sqrt (R n)) →
        R n ≤ metricScalarAt ((K n).toHistory.stageMetric (Fin.last (K n).toHistory.eventCount) v) w
          →
        ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric (Fin.last (K n).toHistory.eventCount) v)
          w
            (Rad / Real.sqrt (metricScalarAt ((K n).toHistory.stageMetric (Fin.last (K
              n).toHistory.eventCount) v) w)),
        ∀ τ : ℝ, v - B / metricScalarAt ((K n).toHistory.stageMetric (Fin.last (K
          n).toHistory.eventCount) v) w ≤ τ → τ ≤ v →
          (K n).toHistory.time (Fin.last (K n).toHistory.eventCount) < τ →
          riemannianEDistOf ((K n).toHistory.stageMetric (Fin.last (K n).toHistory.eventCount) τ)
              ((seedTrace n).point (Fin.last (K n).toHistory.eventCount) h1 h2) x ≤
            riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
              n))
                ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                  n).toHistory.activeStage_mono (has n))
                  ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hCg : 1 ≤ Cg) (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    {Q T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime' (Q n) (Fin.last (K n).eventCount))
    (hderF : ∀ n, (G n).DerivativeBoundBefore Ctime' (Q n) (K n).horizon)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    {rX : ℝ} (hrX : 0 < rX)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) rX)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - rX ^ 2)
    (aP : ℕ → ℝ) (haP : ∀ n, 0 ≤ aP n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage s) s)
        (aP n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (K n).eventCount), T₀X n ≤ (K n).toHistory.time e.succ →
      ((K n).toHistory.event e).old = ((K n).toHistory.event e).transition.trace.retainedCore)
    (hdfin : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) ≠ ⊤) :
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (v : ℝ), (K n).time (Fin.last (K n).eventCount) < v →
        v < (K n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
        n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : (Fin.last (K n).eventCount) ≤ (K n).toHistory.activeStage (σ n))
        (tr : BackwardPointTrace (K n).toHistory (Fin.last (K n).eventCount) ((K
          n).toHistory.activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ (Fin.last (K n).eventCount))
        (h2 : (Fin.last (K n).eventCount) ≤ (K n).toHistory.activeStage (Tn n)) (w : ((K
          n).toHistory.stage (Fin.last (K n).eventCount)).Carrier),
        riemannianEDistOf ((G n).flow.base.metric v)
            ((seedTrace n).point (Fin.last (K n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((G n).flow.base.metric v)
            (tr.point (Fin.last (K n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R
              n)) →
        R n ≤ (G n).flow.scalar v w →
          (∀ x ∈ riemannianBallOf ((G n).flow.base.metric v) w
                (Rad / Real.sqrt ((G n).flow.scalar v w)),
            Cg * R n < (G n).flow.scalar v x →
            ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric v)
              eps C1' C2' x, W.capTubeHasNeckChart eps) ∧
          (∀ x ∈ riemannianBallOf ((G n).flow.base.metric v) w
                (Rad / Real.sqrt ((G n).flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) v,
            v - B / (G n).flow.scalar v w ≤ v' →
            Cg * R n < (G n).flow.scalar v' x →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential (G n).flow v' x ξ| ≤
                (C2'.toNNReal : ℝ) * (G n).flow.scalar v' x *
                  Real.sqrt ((G n).flow.scalar v' x) *
                  Real.sqrt (((G n).flow.base.metric v').inner x ξ ξ)) ∧
          (∀ (τ : Icc (0 : ℝ) (K n).toHistory.horizon),
            v - B / (G n).flow.scalar v w ≤ (τ : ℝ) → (τ : ℝ) ≤ v →
            (K n).time (Fin.last (K n).eventCount) < τ → (τ : ℝ) < (K n).horizon →
            ∀ z ∈ riemannianBallOf ((G n).flow.base.metric v) w
                  (Rad / Real.sqrt ((G n).flow.scalar v w)),
            ∀ zz : ((K n).toHistory.stageAt τ).Carrier, HEq zz z →
            ∀ b : ℝ, 0 < b → b ≤ ρV n → (K n).toHistory.isParabolicallyRmControlledBall τ zz b →
              ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
                riemannianVolumeMeasure ThreeModel ((K n).toHistory.stageAt τ).Carrier
                  ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                  (riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ) τ)
                    zz b)) ∧
          (∀ x ∈ riemannianBallOf ((G n).flow.base.metric v) w
                (Rad / Real.sqrt ((G n).flow.scalar v w)),
            ∀ v' ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) v,
            v - B / (G n).flow.scalar v w ≤ v' →
            Cg * R n < (G n).flow.scalar v' x →
            |derivWithin (fun s => (G n).flow.scalar s x) (Iic v') v'| ≤
              Ctime' * (G n).flow.scalar v' x ^ 2) ∧
          (∀ (i : Fin (K n).eventCount) (first : Fin ((K n).eventCount + 1))
              (hf : first ≤ i.castSucc),
            ∀ z ∈ riemannianBallOf ((G n).flow.base.metric v) w
                (Rad / Real.sqrt ((G n).flow.scalar v w)),
            ∀ Btr : BackwardPointTrace (K n).toHistory first (Fin.last (K n).eventCount)
              (hf.trans (Fin.castSucc_lt_last i).le) z,
            ∀ v' ∈ Ioo ((K n).time i.castSucc) ((K n).time i.succ),
            v - B / (G n).flow.scalar v w ≤ v' →
            (v - v') * max (Cg * R n) ((G n).flow.scalar v z) ≤
              1 / (2 * max (Ctime' : ℝ) 1) →
            Cg * R n < ((K n).toHistory.event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) →
            |derivWithin (fun s => ((K n).toHistory.event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le)) (Iic v') v'| ≤
              Ctime' * ((K n).toHistory.event i).incoming.flow.scalar v'
                (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) ^ 2) := by
  obtain ⟨ε₀, hε₀, hnc0⟩ := exists_hnc_of_records_P6SB2.{u}
  obtain ⟨κs, hκdef⟩ : ∃ κs : ℝ, κs = min (min (rX / 50) (localPropagationRadius C2' / 2))
      (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4)))) := ⟨_, rfl⟩
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  intro Rad B σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hX1 : (1 : ℝ) ≤ max B 0 - σ₁ + 1 := by
    have := le_max_right B 0
    linarith
  filter_upwards [hclosCF Rad B σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr,
    Filter.Eventually.filter_mono hφt
      (hL.eventually_ge_atTop (max (2 * max Rad 0) (max B 0 - σ₁ + 1))),
    Filter.Eventually.filter_mono hφt (hwin (max B 0 - σ₁ + 1) (by linarith)),
    Filter.Eventually.filter_mono hφt hκRF, Filter.Eventually.filter_mono hφt hdistσ,
    Filter.Eventually.filter_mono hφt (hL.eventually_ge_atTop (max (max
      (8 * localPropagationRadius C2')
      (4 * (max Rad 0 + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κs) + 4)) 2)),
    Filter.Eventually.filter_mono hφt (hT₀ (max B 0 - σ₁ + 1)),
    Filter.Eventually.filter_mono hφt (hnat.eventually_gt_atTop (StandardCap.transitionEnd + 10)),
    Filter.Eventually.filter_mono hφt (hnat.eventually_ge_atTop 9),
    Filter.Eventually.filter_mono hφt (hnat.eventually_ge_atTop (6 / rX ^ 2 + 1)),
    Filter.Eventually.filter_mono hφt (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (ge_mem_nhds (lt_min hε₀ (by norm_num : (0 : ℝ) < 1 / 2))))]
    with n hcl hLn hwn hκn hdσ hLX2 hT₀n hTEn h9 hr6 hacn
  intro v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw
  rw [hG n] at hwseed hwnear hRw ⊢
  have hcl' := hcl v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w
    (by rw [(K n).stageMetric_last_restrict_P6HF (hfin n)]; exact hwseed)
    (by rw [(K n).stageMetric_last_restrict_P6HF (hfin n)]; exact hwnear)
    (by rw [(K n).stageMetric_last_restrict_P6HF (hfin n)]; exact hRw)
  simp only [(K n).stageMetric_last_restrict_P6HF (hfin n)] at hcl'
  have hRn := hR n
  have hLX : max B 0 - σ₁ + 1 ≤ L n := (le_max_right _ _).trans hLn
  have hL0 : 0 ≤ L n := by linarith
  have hRad : 2 * max Rad 0 ≤ L n := (le_max_left _ _).trans hLn
  have hvσ : v ≤ (σ n : ℝ) := by
    have : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ hRn
    linarith
  have hwinB : ∀ τ : ℝ, v - B / (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
    le_rfl).flow.scalar v w ≤ τ →
      (aSeed n : ℝ) ≤ τ ∧ (σ n : ℝ) - L n ^ 2 / R n ≤ τ := fun τ hτ => by
    obtain ⟨e1, e2⟩ := window_P6L3 hRn hRw hvσ1 hτ le_rfl hX1 hLX
    exact ⟨hwn.trans e1, e2⟩
  have hwin0 : (aSeed n : ℝ) ≤ v ∧ (σ n : ℝ) - L n ^ 2 / R n ≤ v := by
    have hX0 : max 0 0 - σ₁ + 1 ≤ max B 0 - σ₁ + 1 := by
      rw [max_self]
      linarith [le_max_right B 0]
    obtain ⟨e1, e2⟩ := window_P6L3 (B := 0) (τ := v) hRn hRw hvσ1 (by simp) hX0 hX1 hLX
    exact ⟨hwn.trans e1, e2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx hRx
    exact (K n).witness_of_hgood_final_P6HF (hfin n) (haT n) (hsT n) (has n) (seedTrace n) (y n)
      (R n) (L n) (hgood n) v hv1 hwin0.1 hvσ hwin0.2 h1 h2 x
      (seed_triangle_metric_P6HF _ _ w x _ hRn hRw hL0 hRad hwseed hx) hRx.le
  · intro x hx v' hv' hBv' hRx ξ
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    exact (K n).gradient_of_hgood_final_P6HF hC2 (hfin n) (haT n) (hsT n) (has n) (seedTrace n)
      (y n) (R n) (L n) (hgood n) v' hv'.1 ha (hv'.2.le.trans hvσ) hLτ h1 h2 x
      (hcl' x hx v' hBv' hv'.2.le hv'.1) hRx.le ξ
  · have ha : (Tn n : ℝ) - r n ^ 2 / 2 ≤ v - B / (((K n).finalSlab (hfin n)).restrictIncoming le_rfl
      (hfin n) le_rfl).flow.scalar v w :=
      (hroom n).trans (hwinB _ le_rfl).2
    exact (K n).regionalKappa_of_closure_final_P6HF (hfin n) (haT n) (hsT n) (has n) (seedTrace n)
      (y n) hRn hL0 hκn hdσ _ _ v ha (hvσ.trans (hsT n)) h1 h2
      (fun τ haτ hτv hτ1 _ x hx => hcl' x hx τ haτ hτv hτ1)
  · intro x hx v' hv' hBv' hRx
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    exact (K n).deriv_of_hgood_final_P6SD (hfin n) (haT n) (hsT n) (has n) (seedTrace n) (y n)
      (R n) (L n) (hgood n) v' hv'.1 (hv'.2.trans hv2) ha (hv'.2.le.trans hvσ) hLτ h1 h2 x
      (hcl' x hx v' hBv' hv'.2.le hv'.1) hRx.le
  · intro i first hf z hz Btr v' hv' hBv' hg hRx
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    obtain ⟨e1, -⟩ := window_P6L3 hRn hRw hvσ1 hBv' le_rfl hX1 hLX
    have hT₀v' : T₀ n ≤ v' := hT₀n.trans e1
    have hR1 : (1 : ℝ) ≤ R n := by
      have e2 := hRn1 n
      have e3 : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith only [e2, e3]
    have hLρ : 8 * localPropagationRadius C2' ≤ L n :=
      ((le_max_left _ _).trans (le_max_left _ _)).trans hLX2
    have hLc : 4 * (max Rad 0 + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κs) + 4 ≤ L n :=
      ((le_max_right _ _).trans (le_max_left _ _)).trans hLX2
    have hwinJ : ∀ s : ℝ, v - (L n / 2) ^ 2 / R n ≤ s → (σ n : ℝ) - L n ^ 2 / R n ≤ s := by
      intro s hs
      have hLa : -σ₁ + 1 ≤ L n := by linarith only [hLX, le_max_right B 0]
      have hσ0 : σ₁ < 0 := lt_of_le_of_lt h12 hσ₂
      have hsq := mul_le_mul hLa hLa (by linarith only [hσ0]) hL0
      have hA' : 0 ≤ σ₁ + 3 / 4 * L n ^ 2 := by
        nlinarith only [hsq, sq_nonneg (σ₁ - 1 / 3)]
      have hdiv : 0 ≤ (σ₁ + 3 / 4 * L n ^ 2) / R n := div_nonneg hA' hRn.le
      have heq : (σ₁ + 3 / 4 * L n ^ 2) / R n =
          σ₁ / R n + L n ^ 2 / R n - (L n / 2) ^ 2 / R n := by
        rw [add_div, mul_div_assoc, div_pow]
        ring
      linarith only [hvσ1, hdiv, heq, hs]
    have hQ1 : (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) (Q n) := le_max_left _ _
    have hQ0 : 0 < max ((n : ℝ) + 1) (Q n) := lt_of_lt_of_le (Nat.cast_add_one_pos n) hQ1
    have hslabQ : (K n).EventSlabsDerivative Ctime' (max ((n : ℝ) + 1) (Q n))
        (Fin.last (K n).eventCount) :=
      fun e he y' t' ht hR' => hslabK n e he y' t' ht ((le_max_right _ _).trans_lt hR')
    have hderF' : (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
        le_rfl).DerivativeBoundBefore Ctime' (max ((n : ℝ) + 1) (Q n)) (K n).horizon := by
      have h := hderF n
      rw [hG n] at h
      exact fun y' t' ht hR' => h y' t' ht ((le_max_right _ _).trans_lt hR')
    by_cases hA : max ((n : ℝ) + 1) (Q n) <
        ((K n).toHistory.event i).incoming.flow.scalar v'
          (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le)
    · -- (A) 天花板以上：先验供给逐点
      exact hslabQ i (Fin.castSucc_lt_last i) _ v' hv' hA
    push Not at hA
    have hacc1 : (p n).modelAccuracy ≤ min ε₀ (1 / 2) := (hacc n).trans hacn
    have hDm' : StandardCap.transitionEnd + 10 < (p n).modelRadius := by
      linarith only [hrad n, hTEn]
    have hncK := hnc0 (H := (K n).toHistory) (q := p n) (T₀ := T₀ n) (recordsK n)
      (hacc1.trans (min_le_left _ _)) (le_trans (by omega) (hord n)) (hcanK n)
    have hsepQ : ∀ (e : Fin (K n).eventCount) (he : T₀ n ≤ (K n).time e.succ) b,
        2 * max (3 / rX ^ 2) (4 * max ((n : ℝ) + 1) (Q n)) <
          ((recordsK n e he).static b).neck.scale := by
      intro e he b'
      have hS := hscaleK n e he b'
      have h8 : 8 * max ((n : ℝ) + 1) (Q n) < ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) := by
        nlinarith only [h9, hQ0]
      have hn1 : (1 : ℝ) ≤ max ((n : ℝ) + 1) (Q n) :=
        le_trans (by linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hQ1
      have hnQ : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) :=
        le_mul_of_one_le_right (Nat.cast_add_one_pos n).le hn1
      have h6 : 6 / rX ^ 2 < ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) := by
        linarith only [hnQ, hr6]
      have h63 : 2 * (3 / rX ^ 2) = 6 / rX ^ 2 := by ring
      rcases le_total (3 / rX ^ 2) (4 * max ((n : ℝ) + 1) (Q n)) with hm | hm
      · rw [max_eq_right hm]
        linarith only [h8, hS]
      · rw [max_eq_left hm]
        linarith only [h6, hS, h63]
    exact (K n).traceDt_finalCenter_P6SD hC2 hCg (hfin n) _ rfl hQ0 hslabQ hderF' (haT n) (hsT n)
      (has n) hrX (hsmall n) (hclock n) (seedTrace n) (haP n) (hpin n) (y n) hR1 hL0 (hgood n)
      (hdfin n) (hRa n) (hT₀X n) (hOldX n) (recordsK n) (hcanK n)
      (hacc1.trans (min_le_right _ _)) hDm' hncK hsepQ hκdef hLρ hLc hv1 hv2 hvσ hwin0.1 hwinJ w
      h1 h2 hwseed hRw i first hf z hz Btr hv' ha hLτ hT₀v' hg hRx hA

/-- **F7″ final 支 `hbcadC` producer，无 stay binder（`_P6SD`，PROVISIONAL[`hclosC`, `hclosCF`,
`hdistQC`, `hslabK` / `hderF` / `hscaleK`@同一阈值 `Q n`, CXJD 结构输入族]）**：G4b F7 去掉
`hstaySlCF`，final slab 中心的 U 侧经 F6″（三分）。**无 `hqR`、无 `hstaySlC` / `hstaySlCF`**。 -/
theorem ObservedHistory.hbcadC_final_of_hclosC_sepRhoF_P6SD
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime' : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Cg : ℝ} (hCg : 1 ≤ Cg)
    {K : ℕ → RetainedCoreHistory.{u}}
    (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl)
    {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime' (Q n) (Fin.last (K n).eventCount))
    (hpinchF : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi)
    (hderF : ∀ n, (G n).DerivativeBoundBefore Ctime' (Q n) (K n).horizon)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
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
    (hC2 : 0 ≤ C2) {Aκ : ℝ} (r : ℕ → ℝ)
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
        (Kh n).HasSpatialCanonicalTimeControl ε C1 C2 Ctime' v z)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
      (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))
    (hclosC : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
        ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
        ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
          (Kh n).time j'.castSucc < τ →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
              ((seedTrace n).point j'.castSucc h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hκRF : ∀ᶠ n in atTop, ∀ (c : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier)
      (U : Set ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))
    (hclosCF : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (v : ℝ), (Kh n).time (Fin.last (Kh n).eventCount) < v →
      v < (Kh n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) (Fin.last (Kh n).eventCount) ((Kh n).activeStage (σ n))
          hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ (Fin.last (Kh n).eventCount))
        (h2 : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage
          (Fin.last (Kh n).eventCount)).Carrier),
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt
              (R n)) →
        R n ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w →
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w
            (Rad / Real.sqrt (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
              w)),
        ∀ τ : ℝ, v - B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w ≤ τ
          → τ ≤ v →
          (Kh n).time (Fin.last (Kh n).eventCount) < τ →
          riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) τ)
              ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    {rX : ℝ} (hrX : 0 < rX)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) rX)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - rX ^ 2)
    (aP : ℕ → ℝ) (haP : ∀ n, 0 ≤ aP n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s) (aP n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hdfin : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤) :
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (K * R n)) →
      ∀ᶠ n in map φ atTop,
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
      ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₁)
        (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x₂),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤
          C * R n := by
  subst hKh
  have hUVC := ObservedHistory.hUVC_of_selection_Cg_sepRho_P6SD (Ctime' := Ctime') (Cg := Cg) hC2
    (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT seedTrace y R L r ρV hRpos hL hgood hwin
    hroom hdistσ hκR hclosC rfl hCg hRn1 hcanK hacc hrad hord hscaleK hslabK hT₀ hrX hsmall hclock
    aP haP hpin hRa T₀X hT₀X hOldX hdfin
  have hUVCF := ObservedHistory.hUVCF_of_selection_Cg_sepRho_P6SD (Ctime' := Ctime') (Cg := Cg) hC2
    hfin hG Tn aSeed σ haT hsT has pT seedTrace y R L r ρV hRpos hL hgood hwin hroom hdistσ hκRF
    hclosCF hCg hRn1 hcanK hacc hrad hord hscaleK hslabK hderF hT₀ hrX hsmall hclock aP haP hpin
    hRa T₀X hT₀X hOldX hdfin
  exact ObservedHistory.hbcadC_lateHI_of_slice_data_final_cond_local_P6SD hεle hκ hphi hCg hfin hG
    recordsF hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK hpinchF hderF σ y R hRpos
    hRn1 hT₀ Tn aSeed haT hsT has pT seedTrace L hL hwin ρV hρV hdistQC hUVC hUVCF

/-- **consumer（期 4 调用形，final，`_P6SD`）**：F7″ 的输出逐字付 κ 条件形 driver
`exists_subseq_forall_depthExtendable_kappaC_P6KA` 的 `hbcadC` 槽（DEPTH4C 主定理 final 支 hbcadC 槽同形）。 -/
example
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime' : ℝ≥0}
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {Cg : ℝ} (hCg : 1 ≤ Cg)
    {K : ℕ → RetainedCoreHistory.{u}}
    (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (K n).horizon)
    {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon}
    (hG : ∀ n, G n = ((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n) le_rfl)
    {Q T₀ : ℕ → ℝ} {p pF : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ}
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hδF : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      (pF n).delta ((K n).time i.succ) ≤ 1 / ((n : ℝ) + 1))
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hbirthA : ∀ᶠ n in atTop, ∀ i hi b,
      1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale)
    (hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩ Ici (T₀ n)) phi)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime' (Q n) (Fin.last (K n).eventCount))
    (hpinchF : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi)
    (hderF : ∀ n, (G n).DerivativeBoundBefore Ctime' (Q n) (K n).horizon)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (ρV : ℕ → ℝ) (hρV : Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop)
    (hdistQC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
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
    (hC2 : 0 ≤ C2) {Aκ : ℝ} (r : ℕ → ℝ)
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
        (Kh n).HasSpatialCanonicalTimeControl ε C1 C2 Ctime' v z)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hdistσ : ∀ᶠ n in atTop,
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) (y n) +
        ENNReal.ofReal ((L n + 1) / Real.sqrt (R n)) ≤ ENNReal.ofReal (Aκ * r n))
    (hκR : ∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
      (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))
    (hclosC : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
        v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
        (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            ((seedTrace n).point j'.castSucc h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
        ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
            (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
        ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ → τ ≤ v →
          (Kh n).time j'.castSucc < τ →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric τ)
              ((seedTrace n).point j'.castSucc h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    (hκRF : ∀ᶠ n in atTop, ∀ (c : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier)
      (U : Set ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier) (a t ρU : ℝ),
      (Tn n : ℝ) - r n ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
            ENNReal.ofReal ρU) →
      (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
            ENNReal.ofReal (Aκ * r n)) →
      ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
        (Kh n).time (Fin.last (Kh n).eventCount) < τ → (τ : ℝ) < (Kh n).horizon →
        ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
        ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
              ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
              (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))
    (hclosCF : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ Dw Dd T Kc : ℝ, 0 < Dw → 0 < Dd → -σ₁ < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ (v : ℝ), (Kh n).time (Fin.last (Kh n).eventCount) < v →
      v < (Kh n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) (Fin.last (Kh n).eventCount) ((Kh n).activeStage (σ n))
          hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ (Fin.last (Kh n).eventCount))
        (h2 : (Fin.last (Kh n).eventCount) ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage
          (Fin.last (Kh n).eventCount)).Carrier),
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt
              (R n)) →
        R n ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w →
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w
            (Rad / Real.sqrt (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
              w)),
        ∀ τ : ℝ, v - B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w ≤ τ
          → τ ≤ v →
          (Kh n).time (Fin.last (Kh n).eventCount) < τ →
          riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) τ)
              ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)))
    {rX : ℝ} (hrX : 0 < rX)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) rX)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - rX ^ 2)
    (aP : ℕ → ℝ) (haP : ∀ n, 0 ≤ aP n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s) (aP n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (Kh n).eventCount), T₀X n ≤ (Kh n).time e.succ →
      ((Kh n).event e).old = ((Kh n).event e).transition.trace.retainedCore)
    (hdfin : ∀ n, riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) ≠ ⊤)
    (hRlim : Tendsto R atTop atTop) {Cst : ℝ≥0}
    (hsurvive : ∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (∀ z ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (A / Real.sqrt (R n)),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) z ≤ Q * R n) →
        (Kh n).isTracedRegion (σ n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) z ≤ Q * R n)
    (hextend : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → ObservedHistory.DepthExtendable Kh σ y R ψ T) →
      (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((Kh (ψ i)).stageMetric
          ((Kh (ψ i)).activeStage (σ (ψ i))) (σ (ψ i))) (y (ψ i))
          (A / Real.sqrt (R (ψ i))),
      ∀ (w : Icc (0 : ℝ) (Kh (ψ i)).horizon),
        (w : ℝ) = σ (ψ i) - T' / R (ψ i) →
      ∀ (hwt : w ≤ σ (ψ i))
        (Bt : BackwardPointTrace (Kh (ψ i)) ((Kh (ψ i)).activeStage w)
          ((Kh (ψ i)).activeStage (σ (ψ i)))
          ((Kh (ψ i)).activeStage_mono hwt) x),
        metricScalarAt ((Kh (ψ i)).stageMetric ((Kh (ψ i)).activeStage w) w)
          (Bt.point ((Kh (ψ i)).activeStage w) le_rfl
            ((Kh (ψ i)).activeStage_mono hwt)) ≤
          M * R (ψ i)) →
      ObservedHistory.DepthExtendable Kh σ y R ψ (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1))))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n))))
    {κd : ℝ} (hκd : 0 < κd) (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappaC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κd * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'')
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))))
    {εd : ℝ} (hεd : 0 < εd) (hεXd : εd ≤ crossingWindowNeckAccuracy.{u})
    (hεNd : εd ≤ crossingNeckAccuracy.{u}) {C1s C2s Cs : ℝ}
    {qs : ℕ → ℝ} (hqs : ∀ n, qs n ≤ Cs * R n)
    (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) εd C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart εd)
    {Ctimed : ℝ≥0} {Cq : ℝ} {qcan : ℕ → ℝ} (hqcan : ∀ n, qcan n ≤ Cq * R n)
    (hderivC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qcan n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctimed * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R ψ T := by
  have hb := ObservedHistory.hbcadC_final_of_hclosC_sepRhoF_P6SD hεle hκ hphi hCg hfin hG recordsF
    hHI hcanK hδF hacc hrad hord hscaleK hbirthA hpinchK0 hslabK hpinchF hderF Kh hKh σ y R hRpos
    hRn1 hT₀ Tn aSeed haT hsT has pT seedTrace L hL hwin ρV hρV hdistQC hC2 r hgood hroom hdistσ hκR
    hclosC hκRF hclosCF hrX hsmall hclock aP haP hpin hRa T₀X hT₀X hOldX hdfin
  exact ObservedHistory.exists_subseq_forall_depthExtendable_kappaC_P6KA Kh σ y R hRpos hRlim
    hsurvive hanchor0 hextend hr₀ hw hseed hκd ρnc hradii hkappaC hPhi hpinch hεd hεXd hεNd hqs
    hwitC hqcan hderivC hb

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
