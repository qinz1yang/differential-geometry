import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceTruncBaseP6SD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceDichotomySepRhoP6SD

/-!
# SLICEDICH 链截断孪生 G6b：U 侧块（O-CH11-SLICEDICH G6b，后缀 `_P6SD`）

`hslabK` / `hderF` 换截断形（终点 `min (time e.succ) (tK n)` / `min horizon (tK n)`，连接行
`hTnK : ∀ n, (Tn n : ℝ) ≤ tK n`）。三件都是 G3 / G5 原件逐字孪生，改动只有：签名两行 + 连接行、
`hslabQ` / `hderF'` 的构造、(A) 逐点调用点的终点 `lt_min`（`v' < v ≤ σ ≤ Tn ≤ tK`）、
(B) 反证改调 G6a 的 `_lt_` / `_T_` 件。
* `traceDt_finalCenter_T_P6SD`（G5 `traceDt_finalCenter_P6SD`）；
* `hUVCF_of_selection_Cg_sepRho_T_P6SD`（G5 F6″）；
* `hUVC_of_selection_Cg_sepRho_T_P6SD`（G3 L6″）。
生成器 `build-logs/scratch/O-CH11-SLICEDICH/gen/gen6b.py`。无新 binder / Prop。
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

/-- **final slab 中心的 D1 单实例，截断形（`_P6SD`，PROVED）**：情形 (B) / (C)（调用方先处理 (A)
`R(v′, x) > Q`）。中心 `w` 在 final slab（`time last < v < horizon`），U 点 `z ∈ B(w, Rad/√R(v,w))` 的
history trace `Btr` 回到 event slab `i` 的时刻 `v′`（guard `(v − v′)·max(Cg·R, R(v, z)) ≤ c⋆`）。
(B) `R(v, z) > 2Q`：`hbound_final_P6SD` + clipped reciprocal 与 `R(v′, x) ≤ Q` 矛盾；
(C)：final 通用 stay `hstop_final_CXJF` 以 `(v, w, L/2)` 锚定，保护 ⇐ `hprotC_gen_of_ceiling_CXJF`
+ `hsepQ`，再经 hgood 时间分量。 -/
theorem RetainedCoreHistory.traceDt_finalCenter_T_P6SD {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (hCg : 1 ≤ Cg) (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    (GF : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount))
      K.horizon) (hGF : GF = (K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
    {Q tK : ℝ} (hQ0 : 0 < Q) (hslab : ∀ e : Fin K.eventCount,
      (K.toHistory.event e).incoming.DerivativeBoundBefore Ctime' Q (min (K.time e.succ) tK))
    (hderF : GF.DerivativeBoundBefore Ctime' Q (min K.horizon tK))
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (hTK : (Tn : ℝ) ≤ tK)
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
    have hlow := BackwardPointTrace.scalar_gt_of_time_local_derivative_control_lt_P6SD hvIJ A hQ0
      (K.hbound_final_T_P6SD hfin hslab hderF hvIJ ((show (vJ : ℝ) ≤ Tn from hvJT).trans hTK) A)
      (by rw [hscJ]; exact hB) htime vI le_rfl hvIJ
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


/-- **F6″ final slab U 侧块扩展，截断形 ⇐ `hgood` + `hclosCF` + 先验供给（`hslabK` / `hderF`）+ `hscaleK` + CXJD 族
（`_P6SD`，PROVED ⇐ 这些前提；**无 `hstaySlCF`**）**：G4b F6 的孪生，final slab 中心的 D1 改由三分生产：
(A) `hslabK` 逐点；(B) / (C) `traceDt_finalCenter_P6SD`。 -/
theorem ObservedHistory.hUVCF_of_selection_Cg_sepRho_T_P6SD {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg : ℝ}
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
    {Q T₀ tK : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hslabK : ∀ n (e : Fin (K n).eventCount),
      ((K n).toHistory.event e).incoming.DerivativeBoundBefore Ctime' (Q n)
        (min ((K n).time e.succ) (tK n)))
    (hderF : ∀ n, (G n).DerivativeBoundBefore Ctime' (Q n) (min (K n).horizon (tK n)))
    (hTnK : ∀ n, (Tn n : ℝ) ≤ tK n)
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
    have hslabQ : ∀ e : Fin (K n).eventCount,
        ((K n).toHistory.event e).incoming.DerivativeBoundBefore Ctime' (max ((n : ℝ) + 1) (Q n))
          (min ((K n).time e.succ) (tK n)) :=
      fun e y' t' ht hR' => hslabK n e y' t' ht ((le_max_right _ _).trans_lt hR')
    have hvK : v ≤ tK n := hvσ.trans ((show (σ n : ℝ) ≤ Tn n from hsT n).trans (hTnK n))
    have hderF' : (((K n).finalSlab (hfin n)).restrictIncoming le_rfl (hfin n)
        le_rfl).DerivativeBoundBefore Ctime' (max ((n : ℝ) + 1) (Q n))
          (min (K n).horizon (tK n)) := by
      have h := hderF n
      rw [hG n] at h
      exact fun y' t' ht hR' => h y' t' ht ((le_max_right _ _).trans_lt hR')
    by_cases hA : max ((n : ℝ) + 1) (Q n) <
        ((K n).toHistory.event i).incoming.flow.scalar v'
          (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le)
    · -- (A) 天花板以上：先验供给逐点
      have hv'v : v' < v := hv'.2.trans_le
        (((K n).toHistory.time_strictMono.monotone (Fin.le_last i.succ)).trans hv1.le)
      exact hslabQ i _ v' ⟨hv'.1, lt_min hv'.2 (hv'v.trans_le hvK)⟩ hA
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
    exact (K n).traceDt_finalCenter_T_P6SD hC2 hCg (hfin n) _ rfl hQ0 hslabQ hderF' (haT n) (hsT n)
      (hTnK n)
      (has n) hrX (hsmall n) (hclock n) (seedTrace n) (haP n) (hpin n) (y n) hR1 hL0 (hgood n)
      (hdfin n) (hRa n) (hT₀X n) (hOldX n) (recordsK n) (hcanK n)
      (hacc1.trans (min_le_right _ _)) hDm' hncK hsepQ hκdef hLρ hLc hv1 hv2 hvσ hwin0.1 hwinJ w
      h1 h2 hwseed hRw i first hf z hz Btr hv' ha hLτ hT₀v' hg hRx hA

/-- **L6″ 条件形 `hUVC` 扩展，截断形 ⇐ `hgood` + `hclosC` + 先验供给 + `hscaleK` + CXJD 族（`_P6SD`，PROVED ⇐
这些前提；**无 `hstaySlC`**）**：G2 L6 的孪生，D1 合取改由 SLICE-BCBD2 G8 三分法以 **w 为中心**生产：
`Qm := max(n+1, Q n)`；(A) `R(v′, x) > Qm`：`hslabK` 逐点；(B) `R(v′, x) ≤ Qm < R(v, z)/2`：
`scalar_gt_of_slabs_prefix_P6SB2` 反证；(C) 其余：`stay_cstar_prefix_sepRho_P6SB2` 以
`(σ, y, L) := (v, w, L/2)` 重新锚定（hgood′ ⇐ hgood：w 的 Good 条件给 seed 预算 `L/2`，窗口
eventually），跨越 record 的分离
⇐ `hscaleK`（`Cg·R n < R(v′, x) ≤ Qm` ⇒ `Qb·R n ≤ 2Qm`），再经 hgood 时间分量得 Dt。D1 的 full-history
trace 经 `prefixTraceOfHistory_P6SD` 转 prefixAt 形。 -/
theorem ObservedHistory.hUVC_of_selection_Cg_sepRho_T_P6SD {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2')
    {κ Aκ : ℝ} (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L r ρV : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
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
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
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
    {K : ℕ → RetainedCoreHistory.{u}} (hKh : Kh = fun n => (K n).toHistory) (hCg : 1 ≤ Cg)
    (hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    {Q T₀ tK : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hslabK : ∀ n (e : Fin (K n).eventCount),
      ((K n).toHistory.event e).incoming.DerivativeBoundBefore Ctime' (Q n)
        (min ((K n).time e.succ) (tK n)))
    (hTnK : ∀ n, (Tn n : ℝ) ≤ tK n)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
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
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ φ : ℕ → ℕ, StrictMono φ →
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
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v x →
            ∃ W : SpatialCanonicalWitness (((Kh n).event j').incoming.flow.base.metric v)
              eps C1' C2' x, W.capTubeHasNeckChart eps) ∧
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((Kh n).time j'.castSucc) v,
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v' x →
            ∀ ξ : TangentSpace ThreeModel x,
              |scalarDifferential ((Kh n).event j').incoming.flow v' x ξ| ≤
                (C2'.toNNReal : ℝ) * ((Kh n).event j').incoming.flow.scalar v' x *
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
                  (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b)) ∧
          (∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ v' ∈ Ioo ((Kh n).time j'.castSucc) v,
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            Cg * R n < ((Kh n).event j').incoming.flow.scalar v' x →
            |derivWithin (fun s => ((Kh n).event j').incoming.flow.scalar s x) (Iic v') v'| ≤
              Ctime' * ((Kh n).event j').incoming.flow.scalar v' x ^ 2) ∧
          (∀ (i : Fin (Kh n).eventCount) (first : Fin ((Kh n).eventCount + 1))
              (hf : first ≤ i.castSucc) (hij : i.castSucc < j'.castSucc),
            ∀ z ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
                (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
            ∀ Btr : BackwardPointTrace (Kh n) first j'.castSucc (hf.trans hij.le) z,
            ∀ v' ∈ Ioo ((Kh n).time i.castSucc) ((Kh n).time i.succ),
            v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ v' →
            (v - v') * max (Cg * R n) (((Kh n).event j').incoming.flow.scalar v z) ≤
              1 / (2 * max (Ctime' : ℝ) 1) →
            Cg * R n < ((Kh n).event i).incoming.flow.scalar v'
              (Btr.point i.castSucc hf hij.le) →
            |derivWithin (fun s => ((Kh n).event i).incoming.flow.scalar s
                (Btr.point i.castSucc hf hij.le)) (Iic v') v'| ≤
              Ctime' * ((Kh n).event i).incoming.flow.scalar v'
                (Btr.point i.castSucc hf hij.le) ^ 2) := by
  obtain ⟨ε₀, hε₀, hnc0⟩ := exists_hnc_of_records_P6SB2.{u}
  obtain ⟨κs, hκdef⟩ : ∃ κs : ℝ, κs = min (min (rX / 50) (localPropagationRadius C2' / 2))
      (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4)))) := ⟨_, rfl⟩
  have hρ : 0 < localPropagationRadius C2' := localPropagationRadius_pos hC2
  have hm1 : (1 : ℝ) ≤ max (Ctime' : ℝ) 1 := le_max_right _ _
  have hc0 : (0 : ℝ) ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by positivity
  have hc1 : 1 / (2 * max (Ctime' : ℝ) 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hCc : (Ctime' : ℝ) * (1 / (2 * max (Ctime' : ℝ) 1)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [le_max_left (Ctime' : ℝ) 1]
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  intro Rad B σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hX1 : (1 : ℝ) ≤ max B 0 - σ₁ + 1 := by
    have := le_max_right B 0
    linarith
  filter_upwards [hclosC Rad B σ₁ σ₂ h12 hσ₂ φ hφ Dw Dd T Kc hDw hDd hT hKc htr,
    Filter.Eventually.filter_mono hφt
      (hL.eventually_ge_atTop (max (2 * max Rad 0) (max B 0 - σ₁ + 1))),
    Filter.Eventually.filter_mono hφt (hwin (max B 0 - σ₁ + 1) (by linarith)),
    Filter.Eventually.filter_mono hφt hκR, Filter.Eventually.filter_mono hφt hdistσ,
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
  intro j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw
  have hcl' := hcl j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw
  have hRn := hR n
  have hLX : max B 0 - σ₁ + 1 ≤ L n := (le_max_right _ _).trans hLn
  have hL0 : 0 ≤ L n := by linarith
  have hRad : 2 * max Rad 0 ≤ L n := (le_max_left _ _).trans hLn
  have hvσ : v ≤ (σ n : ℝ) := by
    have : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ hRn
    linarith
  have hwinB : ∀ τ : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ τ →
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
    exact (Kh n).witness_of_hgood_slab_Cg_P6LS3 (haT n) (hsT n) (has n) (seedTrace n) (y n) (R n)
      (L n) (hgood n) j' v hv1 hv2 hwin0.1 hvσ hwin0.2 h1 h2 x
      (seed_triangle_P6L3 (Kh n) j' v _ w x _ hRn hRw hL0 hRad hwseed hx) hRx.le
  · intro x hx v' hv' hBv' hRx ξ
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    exact (Kh n).gradient_of_hgood_slab_Cg_P6LS3 hC2 (haT n) (hsT n) (has n) (seedTrace n) (y n)
      (R n) (L n) (hgood n) j' v' hv'.1 (hv'.2.trans hv2) ha (hv'.2.le.trans hvσ) hLτ h1 h2 x
      (hcl' x hx v' hBv' hv'.2.le hv'.1) hRx.le ξ
  · have ha : (Tn n : ℝ) - r n ^ 2 / 2 ≤ v - B / ((Kh n).event j').incoming.flow.scalar v w :=
      (hroom n).trans (hwinB _ le_rfl).2
    exact regionalKappa_of_closure_P6L3 (Kh n) (haT n) (hsT n) (has n) (seedTrace n) (y n) hRn hL0
      hκn hdσ j' _ _ v ha (hvσ.trans (hsT n)) h1 h2
      (fun τ haτ hτv hτ1 _ x hx => hcl' x hx τ haτ hτv hτ1)
  · intro x hx v' hv' hBv' hRx
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    exact (Kh n).deriv_of_hgood_slab_Cg_P6SD (haT n) (hsT n) (has n) (seedTrace n) (y n)
      (R n) (L n) (hgood n) j' v' hv'.1 (hv'.2.trans hv2) ha (hv'.2.le.trans hvσ) hLτ h1 h2 x
      (hcl' x hx v' hBv' hv'.2.le hv'.1) hRx.le
  · intro i first hf hij z hz Btr v' hv' hBv' hg hRx
    obtain ⟨ha, hLτ⟩ := hwinB v' hBv'
    obtain ⟨e1, -⟩ := window_P6L3 hRn hRw hvσ1 hBv' le_rfl hX1 hLX
    have hT₀v' : T₀ n ≤ v' := hT₀n.trans e1
    have hsj : i.succ ≤ j'.castSucc := Fin.le_def.mpr (by
      have := Fin.lt_def.mp hij
      simp only [Fin.val_succ, Fin.val_castSucc] at this ⊢
      omega)
    have hv'v : v' < v :=
      hv'.2.trans_le (((Kh n).time_strictMono.monotone hsj).trans hv1.le)
    have htv0 : 0 ≤ v - v' := sub_nonneg.mpr hv'v.le
    have h0 : (0 : ℝ) ≤ v' := ((Kh n).time_nonneg _).trans hv'.1.le
    have h0v : (0 : ℝ) ≤ v := h0.trans hv'v.le
    have hR1 : (1 : ℝ) ≤ R n := by
      have e1 := hRn1 n
      have e2 : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith only [e1, e2]
    have hL2 : (2 : ℝ) ≤ L n := (le_max_right _ _).trans hLX2
    have hLρ : 8 * localPropagationRadius C2' ≤ L n :=
      ((le_max_left _ _).trans (le_max_left _ _)).trans hLX2
    have hLc : 4 * (max Rad 0 + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κs) + 4 ≤ L n :=
      ((le_max_right _ _).trans (le_max_left _ _)).trans hLX2
    have hRle : (v - v') * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by
      have h3 := mul_le_mul_of_nonneg_left ((le_mul_of_one_le_left hRn.le hCg).trans
        (le_max_left (Cg * R n) (((Kh n).event j').incoming.flow.scalar v z))) htv0
      exact h3.trans hg
    have hTv : v - v' ≤ 1 / R n := by
      rw [le_div_iff₀ hRn]
      exact hRle.trans hc1
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
    have hrr : Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w) ≤
        max Rad 0 / Real.sqrt (R n) :=
      (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans
        (div_le_div_of_nonneg_left (le_max_right _ _) (Real.sqrt_pos.2 hRn)
          (Real.sqrt_le_sqrt hRw))
    have hz' := riemannianBallOf_mono _ _ hrr hz
    have hQ1 : (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) (Q n) := le_max_left _ _
    have hQ0 : 0 < max ((n : ℝ) + 1) (Q n) := lt_of_lt_of_le (Nat.cast_add_one_pos n) hQ1
    subst hKh
    have hslabQ : ∀ e : Fin (K n).eventCount,
        ((K n).toHistory.event e).incoming.DerivativeBoundBefore Ctime' (max ((n : ℝ) + 1) (Q n))
          (min ((K n).time e.succ) (tK n)) :=
      fun e y' t' ht hR' => hslabK n e y' t' ht ((le_max_right _ _).trans_lt hR')
    have hvK : v ≤ tK n := hvσ.trans ((show (σ n : ℝ) ≤ Tn n from hsT n).trans (hTnK n))
    by_cases hA : max ((n : ℝ) + 1) (Q n) <
        ((K n).toHistory.event i).incoming.flow.scalar v' (Btr.point i.castSucc hf hij.le)
    · -- (A) 天花板以上：先验供给逐点
      exact hslabQ i _ v' ⟨hv'.1, lt_min hv'.2 (hv'v.trans_le hvK)⟩ hA
    push Not at hA
    let vJ : Icc (0 : ℝ) (K n).toHistory.horizon := ⟨v, h0v, hvσ.trans (σ n).2.2⟩
    let vI : Icc (0 : ℝ) (K n).toHistory.horizon :=
      ⟨v', h0, (hv'v.le.trans hvσ).trans (σ n).2.2⟩
    have hvJσ : vJ ≤ σ n := hvσ
    have hvJT : vJ ≤ Tn n := hvJσ.trans (hsT n)
    have hvJa : aSeed n ≤ vJ := hwin0.1
    have hvIJ : vI ≤ vJ := hv'v.le
    have hvIa : aSeed n ≤ vI := ha
    have hactJ : (K n).toHistory.activeStage vJ = j'.castSucc :=
      (K n).toHistory.activeStage_eq_of_slab_P6L3 j' vJ hv1.le hv2
    have hik : i.val < ((K n).prefixAt j'.castSucc).eventCount := by
      have := Fin.lt_def.mp hij
      simp only [Fin.val_castSucc] at this
      exact this
    let ip : Fin ((K n).prefixAt j'.castSucc).eventCount := ⟨i.val, hik⟩
    have hfi : first.val < ((K n).prefixAt j'.castSucc).eventCount + 1 := by
      have := Fin.le_def.mp hf
      simp only [Fin.val_castSucc] at this
      omega
    let fp : Fin (((K n).prefixAt j'.castSucc).eventCount + 1) := ⟨first.val, hfi⟩
    have hfp : fp ≤ ip.castSucc := Fin.le_def.mpr (Fin.le_def.mp hf)
    let Btrp := (K n).prefixTraceOfHistory_P6SD j'.castSucc (first := fp) Btr
    by_cases hB : 2 * max ((n : ℝ) + 1) (Q n) <
        ((K n).toHistory.event j').incoming.flow.scalar v z
    · -- (B) 不可能：trace 下界（clipped reciprocal）
      exfalso
      have hRz : (v - v') * ((K n).toHistory.event j').incoming.flow.scalar v z ≤
          1 / (2 * max (Ctime' : ℝ) 1) :=
        (mul_le_mul_of_nonneg_left (le_max_right _ _) htv0).trans hg
      have htime : (Ctime' : ℝ) * ((K n).toHistory.event j').incoming.flow.scalar vJ z *
          ((vJ : ℝ) - vI) ≤ 1 / 2 := by
        change (Ctime' : ℝ) * ((K n).toHistory.event j').incoming.flow.scalar v z * (v - v') ≤
          1 / 2
        have h1' := mul_le_mul_of_nonneg_left hRz Ctime'.coe_nonneg
        calc (Ctime' : ℝ) * ((K n).toHistory.event j').incoming.flow.scalar v z * (v - v')
            = (Ctime' : ℝ) * ((v - v') *
              ((K n).toHistory.event j').incoming.flow.scalar v z) := by ring
          _ ≤ 1 / 2 := h1'.trans hCc
      have hgt := (K n).scalar_gt_of_slabs_prefix_T_P6SD hQ0 hslabQ j' vJ hactJ hvK ip fp hfp z Btrp
        vI
        hv'.1 hv'.2 hvIJ hB htime
      exact absurd hgt (not_lt.mpr hA)
    push Not at hB
    -- (C) 天花板以下：CXJD stay 以 (v, w, L/2) 重新锚定 + hgood
    obtain ⟨Qb, hQbdef⟩ : ∃ Qb : ℝ, Qb = max (max
        (((K n).toHistory.event j').incoming.flow.scalar v z / R n) Cg) 1 := ⟨_, rfl⟩
    obtain ⟨Tt, hTdef⟩ : ∃ Tt : ℝ, Tt = 1 / (2 * max (Ctime' : ℝ) 1) / Qb := ⟨_, rfl⟩
    have hQb1 : (1 : ℝ) ≤ Qb := by rw [hQbdef]; exact le_max_right _ _
    have hQbM : Qb * R n ≤
        max (Cg * R n) (((K n).toHistory.event j').incoming.flow.scalar v z) := by
      have hCgR : R n ≤ Cg * R n := le_mul_of_one_le_left hRn.le hCg
      have hle : Qb ≤ max (Cg * R n)
          (((K n).toHistory.event j').incoming.flow.scalar v z) / R n := by
        rw [hQbdef]
        refine max_le (max_le ?_ ?_) ?_
        · exact div_le_div_of_nonneg_right (le_max_right _ _) hRn.le
        · rw [le_div_iff₀ hRn]
          exact le_max_left _ _
        · rw [le_div_iff₀ hRn, one_mul]
          exact hCgR.trans (le_max_left _ _)
      calc Qb * R n ≤ max (Cg * R n)
            (((K n).toHistory.event j').incoming.flow.scalar v z) / R n * R n :=
          mul_le_mul_of_nonneg_right hle hRn.le
        _ = _ := div_mul_cancel₀ _ hRn.ne'
    have hQbQ : Qb * R n ≤ 2 * max ((n : ℝ) + 1) (Q n) :=
      hQbM.trans (max_le (by linarith only [hRx, hA, hQ0]) hB)
    have hacc1 : (p n).modelAccuracy ≤ min ε₀ (1 / 2) := (hacc n).trans hacn
    have hDm' : StandardCap.transitionEnd + 10 < (p n).modelRadius := by
      linarith only [hrad n, hTEn]
    have hncK := hnc0 (H := (K n).toHistory) (q := p n) (T₀ := T₀ n) (recordsK n)
      (hacc1.trans (min_le_left _ _)) (le_trans (by omega) (hord n)) (hcanK n)
    have hscale' : ∀ (e : Fin (K n).eventCount) (he : T₀ n ≤ (K n).time e.succ) b,
        (vI : ℝ) < (K n).toHistory.time e.succ → e.succ ≤ (K n).toHistory.activeStage vJ →
        2 * max (3 / rX ^ 2) (2 * (Qb * R n)) < ((recordsK n e he).static b).neck.scale := by
      intro e he b' _ _
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
      have hmx : max (3 / rX ^ 2) (2 * (Qb * R n)) <
          ((recordsK n e he).static b').neck.scale / 2 :=
        max_lt (by linarith only [h6, hS, h63]) (by linarith only [hQbQ, h8, hS])
      linarith only [hmx]
    have hRa' : 1 ≤ R n * vI := by
      have := mul_le_mul_of_nonneg_left ha hRn.le
      change 1 ≤ R n * v'
      linarith only [this, hRa n]
    have haL : (vJ : ℝ) - (L n / 2) ^ 2 / R n ≤ vI := by
      have h1L : 1 / R n ≤ (L n / 2) ^ 2 / R n :=
        div_le_div_of_nonneg_right (by nlinarith only [hL2]) hRn.le
      change v - (L n / 2) ^ 2 / R n ≤ v'
      linarith only [h1L, hTv]
    let w' : ((K n).toHistory.stageAt vJ).Carrier :=
      cast (congrArg (fun m => ((K n).stage m).Carrier) hactJ.symm) w
    have hww : HEq w' w := cast_heq _ _
    have hwJ : riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage vJ) vJ)
          ((seedTrace n).point ((K n).toHistory.activeStage vJ)
            ((K n).toHistory.activeStage_mono hvJa) ((K n).toHistory.activeStage_mono hvJT)) w' ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) := by
      have hs := point_heq_of_eq_P6M2 (seedTrace n) hactJ ((K n).toHistory.activeStage_mono hvJa)
        ((K n).toHistory.activeStage_mono hvJT) h1 h2
      exact (edist_stage_eq_P6L2 j' hactJ v _ w' _ w hs hww).trans_le hwseed
    have hc' : 0 ≤ L n / 2 / Real.sqrt (R n) :=
      div_nonneg (div_nonneg hL0 (by norm_num)) (Real.sqrt_nonneg _)
    have hbud : riemannianEDistOf
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage vJ) vJ)
          ((seedTrace n).point ((K n).toHistory.activeStage vJ)
            ((K n).toHistory.activeStage_mono hvJa) ((K n).toHistory.activeStage_mono hvJT)) w' +
          ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) ≤
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) := by
      refine (add_le_add hwJ le_rfl).trans_eq ?_
      rw [add_assoc, ← ENNReal.ofReal_add hc' hc']
      congr 2
      ring
    have hdw := ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hdfin n, ENNReal.ofReal_ne_top⟩) hwJ
    obtain ⟨hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hnum⟩ := cstar_numerics_P6SP (Qb := Qb) (R := R n)
      (Rad := max Rad 0) (L := L n / 2) hrX hρ hc0 hQb1 hR1 hκdef (by linarith only [hLρ])
      (by linarith only [hLc])
    have hTeq : Tt / R n = 1 / (2 * max (Ctime' : ℝ) 1) / Qb / R n := by rw [hTdef]
    rw [← hTeq] at hnum
    have hstay := stay_cstar_prefix_sepRho_P6SB2 hC2 hCg (K n) j' hv1 hv2 (σ := vJ) rfl (haT n)
      (hsmall n) (hclock n) (seedTrace n) (haP n) (hpin n) hvJT hvJa w' w hww (L n / 2) hRn
      (fun v'' hav'' hvs'' hw'' z'' hd'' hR'' => hgood n v'' hav'' (hvs''.trans hvJσ)
        (hwinJ _ hw'') z'' (hd''.trans hbud) hR'')
      ip fp hfp z hz' Btrp vI hv'.1 hv'.2 hvIa hvIJ haL hRa' hQbdef hTdef hg hℓ hKℓ hℓr hKr hKC
      hℓρ hρL ((hT₀X n).trans ha) (hOldX n) (recordsK n) hT₀v' (hcanK n)
      (hacc1.trans (min_le_right _ _)) hDm' hncK hscale' (by linarith only [hL0]) hdw hnum
    exact ObservedHistory.slabDeriv_prefix_of_hgood_stay_P6SP (K n) j'.castSucc (haT n) (hsT n)
      (has n) (seedTrace n) (y n) (R n) (L n) (hgood n) ip
      (Btrp.point ip.castSucc hfp (Fin.le_last _)) vI hvIa (hvIJ.trans hvJσ) hv'.1 hv'.2 hLτ
      (fun x hx => (hstay x hx).trans hbud) hRx

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
