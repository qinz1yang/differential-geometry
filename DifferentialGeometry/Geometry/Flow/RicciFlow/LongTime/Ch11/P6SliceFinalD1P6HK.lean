import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HbcadCFinalGuardedP6HK
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10FinalSlabCeilingCXJF

/-!
# final slab 中心 D1 的 w 中心三分（A1 续 HARNACK N4-h，后缀 `_P6HK`）

去 `hstaySlCF` 的唯一缺件：SLICEDICH G3 L6″ 的 D1 三分（`stay_cstar_prefix_sepRho_P6SB2` /
`scalar_gt_of_slabs_prefix_P6SB2` / `hslabs` 先验供给）对 final slab 中心的孪生。
* `hbound_of_slabs_final_P6HK`（PROVED）：`hbound_of_eventSlabs_P6SB2` 的 final 孪生，final 段用 `hderF`。
* `slabDeriv_final_D1_P6HK`（PROVED，无 binder）：(A) `R > max(N, Q)` ⇐ `hslabK`；(B) `R(v,z) >
  2·max(N,Q)` ⇒
  `scalar_gt_of_time_local_derivative_control_P6SB2` + 上式矛盾；(C) 其余 ⇐ CX-J10FIN `hstop_final_CXJF` +
  `hprotC_gen_of_ceiling_CXJF`（`σ < horizon` 版，ch12 先前交付，lead 指定）以 `(v, w, L/2)` 重新锚定，
  再经 hgood 时间分量得 Dt。trace 是全 history trace（final 中心），不经 prefix。
生成器 `build-logs/scratch/O-CH11-HARNACK/gen2/g4a.py`（证明体 `d1_body.lean`）。
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

namespace RetainedCoreHistory

/-- **final 段导数界（`_P6HK`，PROVED）**：`hbound_of_eventSlabs_P6SB2` 的 final 孪生：trace 的 event slab 段用
`EventSlabsDerivative`，final slab 段用 `hderF`（限制 final slab 的 `DerivativeBoundBefore … horizon`）。 -/
theorem hbound_of_slabs_final_P6HK (K : RetainedCoreHistory.{u}) {C : ℝ≥0} {q : ℝ}
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
  by_cases hlt : K.toHistory.activeStage v < Fin.last K.eventCount
  · obtain ⟨e, he⟩ := Fin.exists_castSucc_eq.mpr (ne_of_lt hlt)
    have hvlt : (K.toHistory.activeStage v).val < K.eventCount := by
      rw [← he]
      exact e.isLt
    have hnext := K.toHistory.activeStage_before_next v hvlt
    have hfe : (⟨(K.toHistory.activeStage v).val + 1, by omega⟩ : Fin (K.eventCount + 1)) =
        e.succ := by
      apply Fin.ext
      change (K.toHistory.activeStage v).val + 1 = e.succ.val
      rw [Fin.val_succ, ← he, Fin.val_castSucc]
    have hv2 : (v : ℝ) < K.toHistory.time e.succ :=
      hnext.trans_eq (congrArg K.toHistory.time hfe)
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
  · have hm : K.toHistory.activeStage v = Fin.last K.eventCount :=
      le_antisymm (Fin.le_last _) (not_lt.mp hlt)
    have hgen : ∀ (m : Fin (K.eventCount + 1)) (hm : m = Fin.last K.eventCount)
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
    exact hgen _ hm _ _ htv hq

/-- **final 中心 D1 的 w 中心三分（`_P6HK`，PROVED）**：SLICEDICH G3 L6″ D1 合取证明（(A) 天花板以上先验供给 /
(B) clipped reciprocal 反证 / (C) CXJD stay 以 `(v, w, L/2)` 重新锚定）的 final slab 中心孪生。
(B) 用 `hbound_of_slabs_final_P6HK`（final 段 `hderF`）；(C) 用 CX-J10FIN `hstop_final_CXJF` +
`hprotC_gen_of_ceiling_CXJF`（σ < horizon 版，不要 `activeStage σ < last`）。trace 直接是全 history trace，不经
  prefix。 -/
theorem slabDeriv_final_D1_P6HK {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (hCg : 1 ≤ Cg) (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn)
    (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    (y : (K.toHistory.stageAt σ).Carrier) {R L : ℝ} (hR1 : 1 ≤ R)
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
    {Q Nn T₀ : ℝ} {p : CutoffParameters}
    (recordsK : ∀ i : Fin K.eventCount, T₀ ≤ K.time i.succ →
      GeometricCutoffRecord K.toHistory i p)
    (hcanK : ∀ i hi b, ((recordsK i hi).static b).hasCanonicalWindow)
    (hncK : ∀ (e : Fin K.eventCount) (he : T₀ ≤ K.time e.succ)
      (w : (K.toHistory.stage e.succ).Carrier),
      (∀ b, metricScalarAt (K.toHistory.event e).outputMetric w <
        ((recordsK e he).static b).neck.scale / 2) →
      ¬ ∃ (b : (K.toHistory.event e).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        w = ((recordsK e he).static b).window x ∧ ‖x.val‖ < p.modelRadius)
    (hacc : p.modelAccuracy ≤ 1 / 2) (hDm : StandardCap.transitionEnd + 10 < p.modelRadius)
    (hN9 : 9 ≤ Nn)
    (hscaleK : ∀ i hi b, Nn * max Nn Q ≤ ((recordsK i hi).static b).neck.scale)
    (hslabK : K.EventSlabsDerivative Ctime' Q (Fin.last K.eventCount))
    (hderF : ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).DerivativeBoundBefore Ctime' Q
      K.horizon)
    {rX : ℝ} (hrX : 0 < rX) (hr6 : 6 / rX ^ 2 + 1 ≤ Nn)
    (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT rX)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - rX ^ 2)
    {aP : ℝ} (haP : 0 ≤ aP)
    (hpin : ∀ (s : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt s).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage s) s) (aP + s) x)
    {T₀X : ℝ}
    (hOldX : ∀ e : Fin K.eventCount, T₀X ≤ K.toHistory.time e.succ →
      (K.toHistory.event e).old = (K.toHistory.event e).transition.trace.retainedCore)
    (hdfin : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
        (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
          (K.toHistory.activeStage_mono hsT)) y ≠ ⊤)
    {D : ℝ}
    (hLρ : 8 * localPropagationRadius C2' ≤ L)
    (hLc : 4 * (D + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) /
        min (min (rX / 50) (localPropagationRadius C2' / 2))
          (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4))))) + 4 ≤ L)
    (hL2 : 2 ≤ L)
    {v : ℝ} (hv1 : K.time (Fin.last K.eventCount) < v) (hv2 : v < K.horizon) (hvσ : v ≤ σ)
    (hwinJ : ∀ s : ℝ, v - (L / 2) ^ 2 / R ≤ s → (σ : ℝ) - L ^ 2 / R ≤ s)
    (h1 : K.toHistory.activeStage aSeed ≤ Fin.last K.eventCount)
    (h2 : Fin.last K.eventCount ≤ K.toHistory.activeStage Tn)
    (w z : (K.stage (Fin.last K.eventCount)).Carrier)
    (hwseed : riemannianEDistOf
        (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.base.metric v)
        (seedTrace.point (Fin.last K.eventCount) h1 h2) w ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / 2 / Real.sqrt R))
    (hz : z ∈ riemannianBallOf
      (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.base.metric v) w
      (D / Real.sqrt R))
    (i : Fin K.eventCount) (first : Fin (K.eventCount + 1)) (hf : first ≤ i.castSucc)
    (Btr : BackwardPointTrace K.toHistory first (Fin.last K.eventCount)
      (hf.trans (Fin.castSucc_lt_last i).le) z)
    (v' : ℝ) (hv' : v' ∈ Ioo (K.time i.castSucc) (K.time i.succ))
    (hav' : (aSeed : ℝ) ≤ v') (hLτ : (σ : ℝ) - L ^ 2 / R ≤ v') (hT₀v : T₀ ≤ v')
    (hT₀Xv : T₀X ≤ v') (hRa : 1 ≤ R * v')
    (hg : (v - v') * max (Cg * R)
        (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z) ≤
      1 / (2 * max (Ctime' : ℝ) 1))
    (hRx : Cg * R < (K.toHistory.event i).incoming.flow.scalar v'
      (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le)) :
    |derivWithin (fun s => (K.toHistory.event i).incoming.flow.scalar s
        (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le)) (Iic v') v'| ≤
      Ctime' * (K.toHistory.event i).incoming.flow.scalar v'
        (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) ^ 2 := by
  obtain ⟨κs, hκdef⟩ : ∃ κs : ℝ, κs = min (min (rX / 50) (localPropagationRadius C2' / 2))
      (min 1 (1 / (2 * Real.sqrt 3 * (9 + 2 * Real.exp 4)))) := ⟨_, rfl⟩
  rw [← hκdef] at hLc
  have hρ : 0 < localPropagationRadius C2' := localPropagationRadius_pos hC2
  have hR : 0 < R := lt_of_lt_of_le one_pos hR1
  have hm1 : (1 : ℝ) ≤ max (Ctime' : ℝ) 1 := le_max_right _ _
  have hc0 : (0 : ℝ) ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by positivity
  have hc1 : 1 / (2 * max (Ctime' : ℝ) 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hCc : (Ctime' : ℝ) * (1 / (2 * max (Ctime' : ℝ) 1)) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [le_max_left (Ctime' : ℝ) 1]
  have hL0 : 0 ≤ L := by linarith
  have hv'v : v' < v := hv'.2.trans_le
    ((K.toHistory.time_strictMono.monotone (Fin.le_last i.succ)).trans hv1.le)
  have htv0 : 0 ≤ v - v' := sub_nonneg.mpr hv'v.le
  have h0 : (0 : ℝ) ≤ v' := (K.toHistory.time_nonneg _).trans hv'.1.le
  have h0v : (0 : ℝ) ≤ v := h0.trans hv'v.le
  have hRle : (v - v') * R ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by
    have h3 := mul_le_mul_of_nonneg_left ((le_mul_of_one_le_left hR.le hCg).trans
      (le_max_left (Cg * R)
        (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z))) htv0
    exact h3.trans hg
  have hTv : v - v' ≤ 1 / R := by
    rw [le_div_iff₀ hR]
    exact hRle.trans hc1
  have hNQ1 : Nn ≤ max Nn Q := le_max_left _ _
  have hQ0 : 0 < max Nn Q := lt_of_lt_of_le (by linarith) hNQ1
  have hslabQ : K.EventSlabsDerivative Ctime' (max Nn Q) (Fin.last K.eventCount) :=
    fun e he y' t' ht hR' => hslabK e he y' t' ht ((le_max_right _ _).trans_lt hR')
  have hderQ : ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).DerivativeBoundBefore
      Ctime' (max Nn Q) K.horizon :=
    fun y' t' ht hR' => hderF y' t' ht ((le_max_right _ _).trans_lt hR')
  by_cases hA : max Nn Q < (K.toHistory.event i).incoming.flow.scalar v'
      (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le)
  · -- (A) 天花板以上：先验供给逐点
    exact hslabQ i (Fin.castSucc_lt_last i) _ v' hv' hA
  push Not at hA
  let vJ : Icc (0 : ℝ) K.toHistory.horizon := ⟨v, h0v, hvσ.trans σ.2.2⟩
  let vI : Icc (0 : ℝ) K.toHistory.horizon := ⟨v', h0, (hv'v.le.trans hvσ).trans σ.2.2⟩
  have hvJσ : vJ ≤ σ := hvσ
  have hvJT : vJ ≤ Tn := hvJσ.trans hsT
  have hvIJ : vI ≤ vJ := hv'v.le
  have hvIa : aSeed ≤ vI := hav'
  have hvJa : aSeed ≤ vJ := hvIa.trans hvIJ
  have hactJ : K.toHistory.activeStage vJ = Fin.last K.eventCount :=
    K.toHistory.activeStage_eq_last_of_time_last_le vJ hv1.le
  have hactI : K.toHistory.activeStage vI = i.castSucc :=
    K.toHistory.activeStage_eq_of_slab_P6L3 i vI hv'.1.le hv'.2
  -- full-history trace `A` of `z` from `vI` to `vJ`
  let z' : (K.toHistory.stageAt vJ).Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hactJ.symm) z
  have hz' : HEq z' z := cast_heq _ _
  have hfn : first ≤ K.toHistory.activeStage vI := by rw [hactI]; exact hf
  have hnl : K.toHistory.activeStage vI ≤ Fin.last K.eventCount := Fin.le_last _
  let B2 := Btr.restrictFirst hfn hnl
  obtain ⟨A, hA'⟩ := exists_trace_transport_P6SP (K.toHistory.activeStage_mono hvIJ) z'
    hactJ.symm hz'.symm B2
  have hAx : HEq (A.point (K.toHistory.activeStage vI) le_rfl (K.toHistory.activeStage_mono hvIJ))
      (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) := by
    have e1 := hA' (K.toHistory.activeStage vI) le_rfl hnl (K.toHistory.activeStage_mono hvIJ)
    rw [e1]
    exact point_heq_of_eq_P6M2 Btr hactI _ _ _ _
  have hscJ : metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage vJ) vJ) z' =
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z :=
    K.scalar_stage_eq_last_P6HF hfin hactJ (vJ : ℝ) z' z hz'
  by_cases hB : 2 * max Nn Q <
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z
  · -- (B) 不可能：trace 下界（clipped reciprocal，final 段用 hderF）
    exfalso
    have hRz : (v - v') * ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z
        ≤ 1 / (2 * max (Ctime' : ℝ) 1) :=
      (mul_le_mul_of_nonneg_left (le_max_right _ _) htv0).trans hg
    have htime : (Ctime' : ℝ) *
        metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage vJ) vJ) z' *
          ((vJ : ℝ) - vI) ≤ 1 / 2 := by
      rw [hscJ]
      change (Ctime' : ℝ) * _ * (v - v') ≤ 1 / 2
      have h1' := mul_le_mul_of_nonneg_left hRz Ctime'.coe_nonneg
      nlinarith [h1', hCc]
    have hlow := BackwardPointTrace.scalar_gt_of_time_local_derivative_control_P6SB2 hvIJ A hQ0
      (K.hbound_of_slabs_final_P6HK hfin hslabQ hderQ hvIJ A) (by rw [hscJ]; exact hB) htime vI
      le_rfl hvIJ
    have hsc2 := K.scalar_of_incoming_P6JG3H i hactI.symm (vI : ℝ)
      (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) _ hAx
    rw [hsc2] at hlow
    exact absurd hlow (not_lt.mpr hA)
  push Not at hB
  -- (C) 天花板以下：CXJF stay 以 (v, w, L/2) 重新锚定 + hgood
  obtain ⟨Qb, hQbdef⟩ : ∃ Qb : ℝ, Qb = max (max
      (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z / R) Cg) 1 :=
    ⟨_, rfl⟩
  obtain ⟨Tt, hTdef⟩ : ∃ Tt : ℝ, Tt = 1 / (2 * max (Ctime' : ℝ) 1) / Qb := ⟨_, rfl⟩
  have hQb1 : (1 : ℝ) ≤ Qb := by rw [hQbdef]; exact le_max_right _ _
  have hQbpos : 0 < Qb := by linarith
  have hQbM : Qb * R ≤
      max (Cg * R) (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z) := by
    have hCgR : R ≤ Cg * R := le_mul_of_one_le_left hR.le hCg
    have hle : Qb ≤ max (Cg * R)
        (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z) / R := by
      rw [hQbdef]
      refine max_le (max_le ?_ ?_) ?_
      · exact div_le_div_of_nonneg_right (le_max_right _ _) hR.le
      · rw [le_div_iff₀ hR]
        exact le_max_left _ _
      · rw [le_div_iff₀ hR, one_mul]
        exact hCgR.trans (le_max_left _ _)
    calc Qb * R ≤ max (Cg * R)
          (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z) / R * R :=
        mul_le_mul_of_nonneg_right hle hR.le
      _ = _ := div_mul_cancel₀ _ hR.ne'
  have hQbQ : Qb * R ≤ 2 * max Nn Q :=
    hQbM.trans (max_le (by linarith only [hRx, hA, hQ0]) hB)
  have hdepth : (vJ : ℝ) - vI ≤ Tt / R := by
    change v - v' ≤ Tt / R
    rw [hTdef, div_div, le_div_iff₀ (mul_pos hQbpos hR)]
    calc (v - v') * (Qb * R) ≤ (v - v') * max (Cg * R)
          (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z) :=
        mul_le_mul_of_nonneg_left hQbM htv0
      _ ≤ _ := hg
  have hstep : 2 * (Ctime' : ℝ) * Qb * Tt ≤ 1 := by
    have hT : 2 * (Ctime' : ℝ) * Qb * Tt = (Ctime' : ℝ) / max (Ctime' : ℝ) 1 := by
      rw [hTdef]
      field_simp
    rw [hT, div_le_one (by linarith)]
    exact le_max_left _ _
  have hQb : max (max (((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z /
      R) Cg) 1 ≤ Qb := le_of_eq hQbdef.symm
  have hzc : metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage vJ) vJ) z' ≤
      ((K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar v z / R * R := by
    rw [hscJ, div_mul_cancel₀ _ hR.ne']
  have hscale' : ∀ (e : Fin K.eventCount) (he : T₀ ≤ K.time e.succ) b,
      (vI : ℝ) < K.toHistory.time e.succ →
      2 * max (3 / rX ^ 2) (2 * (Qb * R)) < ((recordsK e he).static b).neck.scale := by
    intro e he b' _
    have hS := hscaleK e he b'
    have h8 : 8 * max Nn Q < Nn * max Nn Q := by nlinarith only [hN9, hQ0]
    have hn1 : (1 : ℝ) ≤ max Nn Q := le_trans (by linarith only [hN9]) hNQ1
    have hnQ : Nn ≤ Nn * max Nn Q := le_mul_of_one_le_right (by linarith only [hN9]) hn1
    have h6 : 6 / rX ^ 2 < Nn * max Nn Q := by linarith only [hnQ, hr6]
    have h63 : 2 * (3 / rX ^ 2) = 6 / rX ^ 2 := by ring
    have hmx : max (3 / rX ^ 2) (2 * (Qb * R)) < ((recordsK e he).static b').neck.scale / 2 :=
      max_lt (by linarith only [h6, hS, h63]) (by linarith only [hQbQ, h8, hS])
    linarith only [hmx]
  have hRa' : 1 ≤ R * vI := hRa
  have haL : (vJ : ℝ) - (L / 2) ^ 2 / R ≤ vI := by
    have h1L : 1 / R ≤ (L / 2) ^ 2 / R :=
      div_le_div_of_nonneg_right (by nlinarith only [hL2]) hR.le
    change v - (L / 2) ^ 2 / R ≤ v'
    linarith only [h1L, hTv]
  let w' : (K.toHistory.stageAt vJ).Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hactJ.symm) w
  have hww : HEq w' w := cast_heq _ _
  have hsJ := point_heq_of_eq_P6M2 seedTrace hactJ (K.toHistory.activeStage_mono hvJa)
    (K.toHistory.activeStage_mono hvJT) h1 h2
  have hwJ : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage vJ) vJ)
        (seedTrace.point (K.toHistory.activeStage vJ)
          (K.toHistory.activeStage_mono hvJa) (K.toHistory.activeStage_mono hvJT)) w' ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / 2 / Real.sqrt R) :=
    (K.edist_stage_eq_last_P6HF hfin hactJ (vJ : ℝ) _ w' _ w hsJ hww).trans_le hwseed
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
  have hzy : z' ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage vJ) vJ) w'
      (D / Real.sqrt R) := by
    change riemannianEDistOf _ w' z' < _
    rw [K.edist_stage_eq_last_P6HF hfin hactJ (vJ : ℝ) w' z' w z hww hz']
    exact hz
  obtain ⟨hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hnum⟩ := cstar_numerics_P6SP (Qb := Qb) (R := R)
    (Rad := D) (L := L / 2) hrX hρ hc0 hQb1 hR1 hκdef (by linarith only [hLρ])
    (by linarith only [hLc])
  have hTeq : Tt / R = 1 / (2 * max (Ctime' : ℝ) 1) / Qb / R := by rw [hTdef]
  rw [← hTeq] at hnum
  have hgood' : ∀ (v'' : Icc (0 : ℝ) K.toHistory.horizon) (hav'' : aSeed ≤ v'') (hvs'' : v'' ≤ vJ),
      (vJ : ℝ) - (L / 2) ^ 2 / R ≤ (v'' : ℝ) →
      ∀ z'' : (K.toHistory.stageAt v'').Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v'') v'')
            (seedTrace.point (K.toHistory.activeStage v'') (K.toHistory.activeStage_mono hav'')
              (K.toHistory.activeStage_mono (hvs''.trans hvJT))) z'' ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage vJ) vJ)
              (seedTrace.point (K.toHistory.activeStage vJ) (K.toHistory.activeStage_mono hvJa)
                (K.toHistory.activeStage_mono hvJT)) w' +
            ENNReal.ofReal (L / 2 / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v'') v'') z'' →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v'' z'' :=
    fun v'' hav'' hvs'' hw'' z'' hd'' hR'' => hgood v'' hav'' (hvs''.trans hvJσ)
      (hwinJ _ hw'') z'' (hd''.trans hbud) hR''
  let rec' : ∀ e : Fin K.eventCount, (vI : ℝ) ≤ K.toHistory.time e.succ →
      GeometricCutoffRecord K.toHistory e p := fun e he => recordsK e (hT₀v.trans he)
  have hOld' : ∀ e : Fin K.eventCount, (vI : ℝ) ≤ K.toHistory.time e.succ →
      (K.toHistory.event e).old = (K.toHistory.event e).transition.trace.retainedCore :=
    fun e he => hOldX e (hT₀Xv.trans he)
  have hcan' : ∀ (e : Fin K.eventCount) (he : (vI : ℝ) ≤ K.toHistory.time e.succ) b,
      ((rec' e he).static b).hasCanonicalWindow := fun e he b => hcanK e (hT₀v.trans he) b
  have hprot := ObservedHistory.hprotC_gen_of_ceiling_CXJF K haT hsmall hclock seedTrace hvJT hvJa
    w' (L / 2) hR (by linarith only [hL0]) hgood' hQb hstep hvIa hvIJ haL hdepth hzc A rec' hDm
    (fun e he w'' hw'' => hncK e (hT₀v.trans he) w'' hw'')
    (fun e he b hve => hscale' e (hT₀v.trans he) b hve)
  have hstop := ObservedHistory.hstop_final_CXJF hC2 K haT hsmall hclock seedTrace haP hpin hvJT
    hvJa w' (L / 2) hR hgood' hQb hstep hvIa hvIJ hv2 haL hdepth hRa' hzc A hℓ hKℓ hℓr hKr hKC
    hℓρ hρL le_rfl rec' hOld' hcan' hacc hDm hprot hzy hdw hnum vI le_rfl hvIJ
  have h1I : K.toHistory.activeStage aSeed ≤ i.castSucc :=
    hactI ▸ K.toHistory.activeStage_mono hvIa
  have h2I : i.castSucc ≤ K.toHistory.activeStage Tn := (Fin.castSucc_lt_last i).le.trans h2
  have hseedI := point_heq_of_eq_P6M2 seedTrace hactI (K.toHistory.activeStage_mono hvIa)
    (K.toHistory.activeStage_mono (hvIJ.trans hvJT)) h1I h2I
  have e := edist_stage_eq_P6L2 (H := K.toHistory) i hactI (vI : ℝ)
    (seedTrace.point (K.toHistory.activeStage vI) (K.toHistory.activeStage_mono hvIa)
      (K.toHistory.activeStage_mono (hvIJ.trans hvJT)))
    (A.point (K.toHistory.activeStage vI) le_rfl (K.toHistory.activeStage_mono hvIJ))
    (seedTrace.point i.castSucc h1I h2I) (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le)
    hseedI hAx
  have hstay : riemannianEDistOf ((K.toHistory.event i).incoming.flow.base.metric v')
        (seedTrace.point i.castSucc h1I h2I)
        (Btr.point i.castSucc hf (Fin.castSucc_lt_last i).le) ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R) :=
    (le_of_eq e.symm).trans (hstop.trans hbud)
  exact K.toHistory.deriv_of_hgood_slab_Cg_P6SD haT hsT has seedTrace y R L hgood i v' hv'.1 hv'.2
    hav' (hv'v.le.trans hvσ) hLτ _ _ _ hstay hRx.le

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
