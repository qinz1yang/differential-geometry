import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceScalarLowerP6SB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDProtCP6SB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SLTLocalStaySeqP6SP

/-!
# G1-C：G5 `hslabs` 槽 ⇐ (SEP-ρ⁺) + 天花板级先验供给（O-CH11-SLICE-BCBD2 G8，后缀 `_P6SB2`）

G1-B 的 stay 路径残余，按 lead 裁定改走两分情形 + (SEP-ρ⁺)（HNOT-LOCALDT 统一陈述，窗口析取形；本文件只用
左支）。记号 `Q n := max (n + 1) (ρs n (t n))⁻²`（CORE-DESIGN 天花板阈值）；先验供给 =
`EventSlabsDerivative Ctime′ (Q n)`（`TimeDerivativeSupply_C11E` 同形；**阈值 = Q n，天花板级**）。
`hslabs` 是 trace 点 `x_v` 上的逐点陈述，按 `x_v` 分三种情形：
* (A) `R(v, x_v) > Q`：先验供给逐点直接给（不经 stay、不经 (SEP′)）；
* (B) `R(v, x_v) ≤ Q` 且 `R(t, z) > 2Q`：不可能——G7 `scalar_gt_of_time_local_derivative_control_P6SB2`
  （TimeLocal clipped reciprocal 公开孪生）沿 trace 给 `R(v, x_v) > Q`；
* (C) `R(v, x_v) ≤ Q` 且 `R(t, z) ≤ 2Q`：CXJD stay（`stay_cstar_prefix_sepRho_P6SB2`，SLTPROD G3b 孪生，
  保护由 G1 guarded producer 生产）+ hgood 时间分量（SLTPROD G1 单实例核）；`Qb·R ≤ 2Q`，被跨越 record 的
  分离 `2·max(3/r², 4Q) < S` ⇐ (SEP-ρ⁺) 左支 `(n+1)·Q ≤ S` + `n + 1 ≥ 9` + `n + 1 ≥ 6/r² + 1`
  （eventually）；
  records 用 kernel `recordsK` 限制到 `v` 之后（`T₀ ≤ σ − B/R` eventually）。
主定理 **`ObservedHistory.hslabs_of_sepRho_supply_P6SB2`**：结论 = SLTPROD G1
`hslabsLoc_cstar_of_hgood_P6SP` 结论逐字 = G5 `sliceBCBD_kernel_fresh_theta_ev_P6SB` 内 `hslabs` 的类型。
前提无 `hprotC`，X-records 族只留 `hOldX`。PROVISIONAL[(SEP-ρ⁺)、先验供给（阈值 Q n）]。
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

namespace RetainedCoreHistory

/-- **先验供给 ⇒ TimeLocal 型逐点导数界（`_P6SB2`，PROVED）**：`EventSlabsDerivative C q (last)`、
`activeStage t < last` ⇒ 沿 `[a, t]` 的 trace 上 `q < R` 处 `|∂R| ≤ C·R²`（`stageMetric` 形）。 -/
theorem hbound_of_eventSlabs_P6SB2 (K : RetainedCoreHistory.{u}) {C : ℝ≥0} {q : ℝ}
    (hslab : K.EventSlabsDerivative C q (Fin.last K.eventCount))
    {a t : Icc (0 : ℝ) K.toHistory.horizon} (hat : a ≤ t)
    (htl : K.toHistory.activeStage t < Fin.last K.eventCount)
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
  intro v hav hvt htv _ hq
  have hlt : K.toHistory.activeStage v < Fin.last K.eventCount :=
    lt_of_le_of_lt (K.toHistory.activeStage_mono hvt) htl
  obtain ⟨e, he⟩ := Fin.exists_castSucc_eq.mpr (ne_of_lt hlt)
  have hvlt : (K.toHistory.activeStage v).val < K.eventCount := by
    rw [← he]
    exact e.isLt
  have hnext := K.toHistory.activeStage_before_next v hvlt
  have hfin : (⟨(K.toHistory.activeStage v).val + 1, by omega⟩ : Fin (K.eventCount + 1)) =
      e.succ := by
    apply Fin.ext
    change (K.toHistory.activeStage v).val + 1 = e.succ.val
    rw [Fin.val_succ, ← he, Fin.val_castSucc]
  have hv2 : (v : ℝ) < K.toHistory.time e.succ :=
    hnext.trans_eq (congrArg K.toHistory.time hfin)
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

/-- prefix trace ⇒ history trace（SLTPROD G3b 证明内构造的公开化，`_P6SB2`，PROVED）。 -/
theorem exists_historyTrace_of_prefix_P6SB2 (K : RetainedCoreHistory.{u}) (j : Fin K.eventCount)
    (σ : Icc (0 : ℝ) K.toHistory.horizon) (hact : K.toHistory.activeStage σ = j.castSucc)
    (i : Fin (K.prefixAt j.castSucc).eventCount)
    (first : Fin ((K.prefixAt j.castSucc).eventCount + 1)) (hf : first ≤ i.castSucc)
    (z : (K.stage j.castSucc).Carrier)
    (Btr : BackwardPointTrace (K.prefixAt j.castSucc).toHistory first
      (Fin.last (K.prefixAt j.castSucc).eventCount) (Fin.le_last first) z)
    (v' : Icc (0 : ℝ) K.toHistory.horizon) (hv1 : (K.prefixAt j.castSucc).time i.castSucc < v')
    (hv2 : (v' : ℝ) < (K.prefixAt j.castSucc).time i.succ) (hvs : v' ≤ σ) :
    ∃ (z' : (K.toHistory.stageAt σ).Carrier)
      (A : BackwardPointTrace K.toHistory (K.toHistory.activeStage v')
        (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono hvs) z'),
      HEq z' z ∧ HEq (A.point (K.toHistory.activeStage v') (K.toHistory.activeStage_mono le_rfl)
        (K.toHistory.activeStage_mono hvs)) (Btr.point i.castSucc hf (Fin.le_last _)) := by
  let z' : (K.toHistory.stageAt σ).Carrier :=
    cast (congrArg (fun m => (K.stage m).Carrier) hact.symm) z
  have hz' : HEq z' z := cast_heq _ _
  have hvact : K.toHistory.activeStage v' =
      (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i).castSucc :=
    K.activeStage_eq_of_mem_slab_P6JG3H _ v' hv1.le hv2
  have hfn : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt)) first ≤
      K.toHistory.activeStage v' := by
    rw [hvact, Fin.le_iff_val_le_val]
    exact Fin.le_iff_val_le_val.mp hf
  have hnl : K.toHistory.activeStage v' ≤
      Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
        (Fin.last (K.prefixAt j.castSucc).eventCount) := by
    rw [hvact, Fin.le_iff_val_le_val]
    exact i.isLt.le
  have hl : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      (Fin.last (K.prefixAt j.castSucc).eventCount) = K.toHistory.activeStage σ := by
    rw [hact]
    exact Fin.ext rfl
  let B1 := K.backwardPointTraceOfPrefix j.castSucc Btr
  let B2 := B1.restrictFirst hfn hnl
  obtain ⟨A, hA⟩ := exists_trace_transport_P6SP (K.toHistory.activeStage_mono hvs) z' hl
    hz'.symm B2
  refine ⟨z', A, hz', ?_⟩
  have e1 := hA (K.toHistory.activeStage v') (K.toHistory.activeStage_mono le_rfl) hnl
    (K.toHistory.activeStage_mono hvs)
  exact (heq_of_eq e1).trans (ofPrefix_point_heq_P6SP K j.castSucc Btr i.castSucc hf
    (Fin.le_last _) _ (by rw [hvact]; rfl) (hfn.trans (K.toHistory.activeStage_mono le_rfl)) hnl)

/-- **情形 (B) 排除（`_P6SB2`，PROVED）**：先验供给（阈值 `Q`）+ 端点 `R(σ, z) > 2Q` +
`Ctime·R(σ, z)·(σ − v′) ≤ 1/2` ⇒ prefix trace 点 `R(v′, x) > Q`。 -/
theorem scalar_gt_of_slabs_prefix_P6SB2 (K : RetainedCoreHistory.{u}) {C : ℝ≥0} {Q : ℝ}
    (hQ : 0 < Q) (hslab : K.EventSlabsDerivative C Q (Fin.last K.eventCount))
    (j : Fin K.eventCount) (σ : Icc (0 : ℝ) K.toHistory.horizon)
    (hact : K.toHistory.activeStage σ = j.castSucc)
    (i : Fin (K.prefixAt j.castSucc).eventCount)
    (first : Fin ((K.prefixAt j.castSucc).eventCount + 1)) (hf : first ≤ i.castSucc)
    (z : (K.stage j.castSucc).Carrier)
    (Btr : BackwardPointTrace (K.prefixAt j.castSucc).toHistory first
      (Fin.last (K.prefixAt j.castSucc).eventCount) (Fin.le_last first) z)
    (v' : Icc (0 : ℝ) K.toHistory.horizon) (hv1 : (K.prefixAt j.castSucc).time i.castSucc < v')
    (hv2 : (v' : ℝ) < (K.prefixAt j.castSucc).time i.succ) (hvs : v' ≤ σ)
    (hend : 2 * Q < (K.toHistory.event j).incoming.flow.scalar σ z)
    (htime : C * (K.toHistory.event j).incoming.flow.scalar σ z * ((σ : ℝ) - v') ≤ 1 / 2) :
    Q < ((K.prefixAt j.castSucc).toHistory.event i).incoming.flow.scalar v'
      (Btr.point i.castSucc hf (Fin.le_last _)) := by
  obtain ⟨z', A, hz', hAx⟩ := K.exists_historyTrace_of_prefix_P6SB2 j σ hact i first hf z Btr v'
    hv1 hv2 hvs
  have hsc := K.scalar_of_incoming_P6JG3H j hact.symm (σ : ℝ) z z' hz'
  have htl : K.toHistory.activeStage σ < Fin.last K.eventCount := by
    rw [hact]
    exact Fin.castSucc_lt_last j
  have hlow := BackwardPointTrace.scalar_gt_of_time_local_derivative_control_P6SB2 hvs A hQ
    (K.hbound_of_eventSlabs_P6SB2 hslab hvs htl A) (by rw [hsc]; exact hend)
    (by rw [hsc]; exact htime) v' le_rfl hvs
  let e : Fin K.eventCount := Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i
  have hvact : K.toHistory.activeStage v' = e.castSucc :=
    K.activeStage_eq_of_mem_slab_P6JG3H e v' hv1.le hv2
  have hsc2 := K.scalar_of_incoming_P6JG3H e hvact.symm v'
    (Btr.point i.castSucc hf (Fin.le_last _)) _ hAx
  rw [hsc2] at hlow
  exact hlow

end RetainedCoreHistory

namespace ObservedHistory

/-- **情形 (C) 的 stay（`_P6SB2`，PROVED）**：SLTPROD G3b `stay_cstar_prefix_of_firstExit_P6SP` 的孪生，
`hprotC` 不再是前提——由 G1 guarded producer 生产；records 用 kernel `recordsK` 限制到 `v′` 之后；输入是被跨越 record
的 scale 分离 `hscaleK`（`Qb·R` 形，由主定理从 (SEP-ρ⁺) 推出）与单 record 窗口排除 `hncK`。结论 = G3b 逐字。 -/
theorem stay_cstar_prefix_sepRho_P6SB2 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg Qb T Kc ℓ D : ℝ} (hC2 : 0 ≤ C2') (hCg : 1 ≤ Cg) (K : RetainedCoreHistory.{u})
    (j : Fin K.eventCount) {t : ℝ} (hjt : K.time j.castSucc < t) (htj : t < K.time j.succ)
    {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon} (hσt : (σ : ℝ) = t) (haT : aSeed ≤ Tn)
    {pT : (K.toHistory.stageAt Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (s : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt s).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage s) s)
        (a₀ + s) x)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (K.toHistory.stageAt σ).Carrier)
    (yG : (K.stage j.castSucc).Carrier) (hyG : HEq y yG) {R : ℝ} (L : ℝ) (hR : 0 < R)
    (hgood : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (i : Fin (K.prefixAt j.castSucc).eventCount)
    (first : Fin ((K.prefixAt j.castSucc).eventCount + 1)) (hf : first ≤ i.castSucc)
    (z : (K.stage j.castSucc).Carrier)
    (hz : z ∈ riemannianBallOf ((K.toHistory.event j).incoming.flow.base.metric t) yG
      (D / Real.sqrt R))
    (Btr : BackwardPointTrace (K.prefixAt j.castSucc).toHistory first
      (Fin.last (K.prefixAt j.castSucc).eventCount) (Fin.le_last first) z)
    (v' : Icc (0 : ℝ) K.toHistory.horizon)
    (hv1 : (K.prefixAt j.castSucc).time i.castSucc < v')
    (hv2 : (v' : ℝ) < (K.prefixAt j.castSucc).time i.succ)
    (hav : aSeed ≤ v') (hvs : v' ≤ σ) (haL : (σ : ℝ) - L ^ 2 / R ≤ v') (hRa : 1 ≤ R * v')
    (hQbdef : Qb = max (max ((K.toHistory.event j).incoming.flow.scalar t z / R) Cg) 1)
    (hTdef : T = 1 / (2 * max (Ctime' : ℝ) 1) / Qb)
    (hguard : (t - v') * max (Cg * R) ((K.toHistory.event j).incoming.flow.scalar t z) ≤
      1 / (2 * max (Ctime' : ℝ) 1))
    (hℓ : 0 < ℓ) (hKℓ : Kc * ℓ ^ 2 ≤ 1) (hℓr : ℓ ≤ r / 50) (hKr : 1 / r ^ 2 ≤ Kc)
    (hKC : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ Kc)
    (hℓρ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (hρL : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    {T₀X : ℝ} (hT₀X : T₀X ≤ (v' : ℝ))
    (hOldX : ∀ e : Fin K.eventCount, T₀X ≤ K.toHistory.time e.succ →
      (K.toHistory.event e).old = (K.toHistory.event e).transition.trace.retainedCore)
    {p : CutoffParameters} {T₀K : ℝ}
    (recordsK : ∀ e : Fin K.eventCount, T₀K ≤ K.time e.succ →
      GeometricCutoffRecord K.toHistory e p) (hT₀v : T₀K ≤ (v' : ℝ))
    (hcanK : ∀ (e : Fin K.eventCount) (he : T₀K ≤ K.time e.succ) b,
      ((recordsK e he).static b).hasCanonicalWindow)
    (hacc : p.modelAccuracy ≤ 1 / 2) (hDm : StandardCap.transitionEnd + 10 < p.modelRadius)
    (hncK : ∀ (e : Fin K.eventCount) (he : T₀K ≤ K.time e.succ)
      (w : (K.toHistory.stage e.succ).Carrier),
      (∀ b, metricScalarAt (K.toHistory.event e).outputMetric w <
        ((recordsK e he).static b).neck.scale / 2) →
      ¬ ∃ (b : (K.toHistory.event e).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        w = ((recordsK e he).static b).window x ∧ ‖x.val‖ < p.modelRadius)
    (hscaleK : ∀ (e : Fin K.eventCount) (he : T₀K ≤ K.time e.succ) b,
      (v' : ℝ) < K.toHistory.time e.succ → e.succ ≤ K.toHistory.activeStage σ →
      2 * max (3 / r ^ 2) (2 * (Qb * R)) < ((recordsK e he).static b).neck.scale)
    (hL0 : 0 ≤ L)
    (hdσ : riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
        (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
          (K.toHistory.activeStage_mono hσT)) y ≠ ⊤)
    (hnum : D / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R) :
    ∀ x : (K.toHistory.stageAt v').Carrier,
      HEq x (Btr.point i.castSucc hf (Fin.le_last _)) →
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v') v')
          (seedTrace.point (K.toHistory.activeStage v') (K.toHistory.activeStage_mono hav)
            (K.toHistory.activeStage_mono (hvs.trans hσT))) x ≤
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
            (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
              (K.toHistory.activeStage_mono hσT)) y +
          ENNReal.ofReal (L / Real.sqrt R)  := by
  subst hσt
  have hact : K.toHistory.activeStage σ = j.castSucc :=
    K.activeStage_eq_of_mem_slab_P6JG3H j σ hjt.le htj
  have hσlast : K.toHistory.activeStage σ < Fin.last K.eventCount := by
    rw [hact]
    exact Fin.castSucc_lt_last j
  have hR0 : 0 < R := hR
  have hCgR : R ≤ Cg * R := by nlinarith
  have hQbM : Qb * R ≤ max (Cg * R) ((K.toHistory.event j).incoming.flow.scalar σ z) := by
    have hle : Qb ≤ max (Cg * R) ((K.toHistory.event j).incoming.flow.scalar σ z) / R := by
      rw [hQbdef]
      refine max_le (max_le ?_ ?_) ?_
      · exact div_le_div_of_nonneg_right (le_max_right _ _) hR0.le
      · rw [le_div_iff₀ hR0]
        exact le_max_left _ _
      · rw [le_div_iff₀ hR0, one_mul]
        exact hCgR.trans (le_max_left _ _)
    calc Qb * R ≤ max (Cg * R) ((K.toHistory.event j).incoming.flow.scalar σ z) / R * R :=
          mul_le_mul_of_nonneg_right hle hR0.le
      _ = _ := div_mul_cancel₀ _ hR0.ne'
  have hQb1 : (1 : ℝ) ≤ Qb := by rw [hQbdef]; exact le_max_right _ _
  have hQbpos : 0 < Qb := by linarith
  have hm1 : (0 : ℝ) < max (Ctime' : ℝ) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsv : 0 ≤ (σ : ℝ) - v' := sub_nonneg.mpr (show (v' : ℝ) ≤ σ from hvs)
  have hdepth : (σ : ℝ) - v' ≤ T / R := by
    rw [hTdef, div_div, le_div_iff₀ (mul_pos hQbpos hR0)]
    exact (mul_le_mul_of_nonneg_left hQbM hsv).trans hguard
  have hstep : 2 * (Ctime' : ℝ) * Qb * T ≤ 1 := by
    have hT : 2 * (Ctime' : ℝ) * Qb * T = (Ctime' : ℝ) / max (Ctime' : ℝ) 1 := by
      rw [hTdef]
      field_simp
    rw [hT, div_le_one hm1]
    exact le_max_left _ _
  let rec' : ∀ e : Fin K.eventCount, (v' : ℝ) ≤ K.toHistory.time e.succ →
      GeometricCutoffRecord K.toHistory e p := fun e he => recordsK e (hT₀v.trans he)
  have hOld' : ∀ e : Fin K.eventCount, (v' : ℝ) ≤ K.toHistory.time e.succ →
      (K.toHistory.event e).old = (K.toHistory.event e).transition.trace.retainedCore :=
    fun e he => hOldX e (hT₀X.trans he)
  have hcan' : ∀ (e : Fin K.eventCount) (he : (v' : ℝ) ≤ K.toHistory.time e.succ) b,
      ((rec' e he).static b).hasCanonicalWindow := fun e he b => hcanK e (hT₀v.trans he) b
  have hzc : ∀ (z'' : (K.toHistory.stageAt σ).Carrier), HEq z'' z →
      metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ) z'' ≤
        (K.toHistory.event j).incoming.flow.scalar σ z / R * R := by
    intro z'' hz''
    rw [K.scalar_of_incoming_P6JG3H j hact.symm σ z z'' hz'', div_mul_cancel₀ _ hR0.ne']
  have hQb : max (max ((K.toHistory.event j).incoming.flow.scalar σ z / R) Cg) 1 ≤ Qb :=
    le_of_eq hQbdef.symm
  exact ObservedHistory.stay_cstar_prefix_of_firstExit_P6SP hC2 hCg K j hjt htj rfl haT hsmall
    hclock seedTrace ha₀ hpin hσT has y yG hyG L hR hgood i first hf z hz Btr v' hv1 hv2 hav hvs
    haL hRa hQbdef hTdef hguard hℓ hKℓ hℓr hKr hKC hℓρ hρL le_rfl rec' hOld' hcan' hacc hDm
    (fun z'' hz'' A => ObservedHistory.hprotC_of_ceiling_guarded_P6SB2 K.toHistory haT hsmall
      hclock seedTrace hσT has y L hR hL0 hgood hQb hstep hav hvs hσlast haL hdepth (hzc z'' hz'')
      A rec' hDm (fun e he w hw => hncK e (hT₀v.trans he) w hw)
      (fun e he b hve he4 => hscaleK e (hT₀v.trans he) b hve he4)) hdσ hnum

/-- **G5 `hslabs` 槽 ⇐ (SEP-ρ⁺) + 天花板级先验供给（`_P6SB2`，PROVISIONAL[(SEP-ρ⁺)、先验供给（阈值
`Q n = max(n+1, ρ̃⁻²)`）]）**：结论 = SLTPROD G1 `hslabsLoc_cstar_of_hgood_P6SP` 结论逐字（= G5 内 `hslabs`
类型）。三情形 (A)/(B)/(C) 见模块注释；前提无 `hprotC`，X-records 族只留 `hOldX`。 -/
theorem hslabs_of_sepRho_supply_P6SB2 {eps C1' C2' : ℝ}
    {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2') (hCg : 1 ≤ Cg) {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ} (hjt : ∀ n, (K n).time (j n).castSucc < t n)
    (htj : ∀ n, t n < (K n).time (j n).succ) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (j n).castSucc).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hR1 : ∀ n, 1 ≤ R n)
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    (a₀ : ℕ → ℝ) (ha₀ : ∀ n, 0 ≤ a₀ n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage s) s)
        (a₀ n + s) x)
    (hRa : ∀ n, 1 ≤ R n * aSeed n)
    (T₀X : ℕ → ℝ) (hT₀X : ∀ n, T₀X n ≤ aSeed n)
    (hOldX : ∀ n (e : Fin (K n).eventCount), T₀X n ≤ (K n).toHistory.time e.succ →
      ((K n).toHistory.event e).old = ((K n).toHistory.event e).transition.trace.retainedCore)
    (hdσ : ∀ n, riemannianEDistOf ((K n).toHistory.stageMetric
        ((K n).toHistory.activeStage (σ n)) (σ n))
        ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono (has n))
          ((K n).toHistory.activeStage_mono (hsT n))) (y n) ≠ ⊤)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (ρs : ℕ → ℝ → ℝ) {θ₀ : ℝ}
    (hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
        (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        (t n - B / R n ≤ (K n).time i.succ ∨
          t n - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
        ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ ≤
          ((recordsK n i hi).static b).neck.scale)
    (hslabK : ∀ n, (K n).EventSlabsDerivative Ctime' (max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹)
      (Fin.last (K n).eventCount)) :
    ∀ Rad B : ℝ, ∀ᶠ n in atTop,
      ∀ i : Fin ((K n).prefixAt (j n).castSucc).eventCount,
      ∀ (first : Fin (((K n).prefixAt (j n).castSucc).eventCount + 1)) (hf : first ≤ i.castSucc),
      ∀ z ∈ riemannianBallOf (((K n).toHistory.event (j n)).incoming.flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))),
      ∀ Btr : BackwardPointTrace ((K n).prefixAt (j n).castSucc).toHistory first
        (Fin.last ((K n).prefixAt (j n).castSucc).eventCount) (Fin.le_last first) z,
      ∀ v ∈ Ioo (((K n).prefixAt (j n).castSucc).time i.castSucc)
        (((K n).prefixAt (j n).castSucc).time i.succ),
      t n - B / ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n) ≤ v →
      (t n - v) * max (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) ≤
        1 / (2 * max (Ctime' : ℝ) 1) →
      Cg * R n < (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
        (Btr.point i.castSucc hf (Fin.le_last _)) →
      |derivWithin (fun w =>
          (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar w
            (Btr.point i.castSucc hf (Fin.le_last _))) (Iic v) v| ≤
        Ctime' * (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
          (Btr.point i.castSucc hf (Fin.le_last _)) ^ 2 := by
  obtain ⟨ε₀, hε₀, hnc0⟩ := exists_hnc_of_records_P6SB2.{u}
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min (min (r / 50) (localPropagationRadius C2' / 2))
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
  intro Rad B
  filter_upwards [hL.eventually_ge_atTop (max (max (4 * localPropagationRadius C2')
    (2 * (Rad + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κ) + 2)) 1), hwin 1 one_pos,
    hT₀ (max B 1), hsepρ (max B 1) (by positivity),
    hnat.eventually_gt_atTop (StandardCap.transitionEnd + 10), hnat.eventually_ge_atTop 9,
    hnat.eventually_ge_atTop (6 / r ^ 2 + 1),
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (ge_mem_nhds (lt_min hε₀ (by norm_num : (0 : ℝ) < 1 / 2)))]
    with n hLn hwn hT₀n hsepn hTEn h9 hr6 hacn
  intro i first hf z hz Btr v hv hBv hguard hq
  have hR0 := hR n
  have hQ1 : (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ := le_max_left _ _
  have hQ0 : 0 < max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ :=
    lt_of_lt_of_le (Nat.cast_add_one_pos n) hQ1
  have hL4 : 4 * localPropagationRadius C2' ≤ L n :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans hLn
  have hL5 : 2 * (Rad + 8 * (1 / (2 * max (Ctime' : ℝ) 1)) / κ) + 2 ≤ L n :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hLn
  have hL6 : (1 : ℝ) ≤ L n := (le_max_right _ _).trans hLn
  have hlast : ((K n).prefixAt (j n).castSucc).time i.succ ≤ (K n).time (j n).castSucc :=
    (((K n).prefixAt (j n).castSucc).time_strictMono.monotone (Fin.le_last _)).trans_eq
      ((K n).prefixAt_time_last _)
  have hvt : v < t n := hv.2.trans_le (hlast.trans (hjt n).le)
  have htv0 : 0 ≤ t n - v := sub_nonneg.mpr hvt.le
  have hRle : (t n - v) * R n ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by
    have h3 := mul_le_mul_of_nonneg_left ((le_mul_of_one_le_left hR0.le hCg).trans
      (le_max_left (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z)))
      htv0
    exact h3.trans hguard
  have hTv : t n - v ≤ 1 / R n := by
    rw [le_div_iff₀ hR0]
    exact hRle.trans hc1
  have hBR : t n - max B 1 / R n ≤ v := by
    have hBv' : t n - B / R n ≤ v := by rw [hRn n]; exact hBv
    have : B / R n ≤ max B 1 / R n := div_le_div_of_nonneg_right (le_max_left _ _) hR0.le
    linarith only [hBv', this]
  have hv0 : 0 ≤ v := (((K n).prefixAt (j n).castSucc).toHistory.time_nonneg _).trans hv.1.le
  have hvH : v ≤ (K n).toHistory.horizon :=
    (hvt.trans (htj n)).le.trans ((K n).toHistory.time_le_horizon_at (j n).succ)
  let v' : Icc (0 : ℝ) (K n).toHistory.horizon := ⟨v, hv0, hvH⟩
  have hav : aSeed n ≤ v' :=
    hwn.trans (show (σ n : ℝ) - 1 / R n ≤ v by rw [hσ n]; linarith only [hTv])
  have hav' : (aSeed n : ℝ) ≤ v := hav
  have hvs : v' ≤ σ n := show v ≤ (σ n : ℝ) by rw [hσ n]; exact hvt.le
  have hLv : (σ n : ℝ) - L n ^ 2 / R n ≤ (v' : ℝ) := by
    have : 1 / R n ≤ L n ^ 2 / R n :=
      div_le_div_of_nonneg_right (by nlinarith only [hL6]) hR0.le
    change (σ n : ℝ) - L n ^ 2 / R n ≤ v
    rw [hσ n]
    linarith only [this, hTv]
  have hact : (K n).toHistory.activeStage (σ n) = (j n).castSucc :=
    (K n).activeStage_eq_of_mem_slab_P6JG3H (j n) (σ n) (by rw [hσ n]; exact (hjt n).le)
      (by rw [hσ n]; exact htj n)
  by_cases hA : max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ <
      (((K n).prefixAt (j n).castSucc).toHistory.event i).incoming.flow.scalar v
        (Btr.point i.castSucc hf (Fin.le_last _))
  · -- (A) 天花板以上：先验供给逐点
    exact hslabK n (Fin.castLE (Nat.le_of_lt_succ (j n).castSucc.isLt) i)
      (Fin.castSucc_lt_last _) _ v ⟨hv.1, hv.2⟩ hA
  · push Not at hA
    by_cases hB : 2 * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ <
        ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z
    · -- (B) 不可能：trace 下界
      exfalso
      have hRz : (t n - v) * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z ≤
          1 / (2 * max (Ctime' : ℝ) 1) :=
        (mul_le_mul_of_nonneg_left (le_max_right _ _) htv0).trans hguard
      have htime : (Ctime' : ℝ) * ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) z *
          ((σ n : ℝ) - v') ≤ 1 / 2 := by
        change (Ctime' : ℝ) * ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) z *
          ((σ n : ℝ) - v) ≤ 1 / 2
        rw [hσ n]
        have h1 := mul_le_mul_of_nonneg_left hRz Ctime'.coe_nonneg
        calc (Ctime' : ℝ) * ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z * (t n - v)
            = (Ctime' : ℝ) * ((t n - v) *
              ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) := by ring
          _ ≤ 1 / 2 := h1.trans hCc
      have hgt := (K n).scalar_gt_of_slabs_prefix_P6SB2 hQ0 (hslabK n) (j n) (σ n) hact i first hf
        z Btr v' hv.1 hv.2 hvs (by rw [hσ n]; exact hB) htime
      exact absurd hgt (not_lt.mpr hA)
    · -- (C) 天花板以下：CXJD stay（保护由 guarded producer + (SEP-ρ⁺) 付）+ hgood
      push Not at hB
      obtain ⟨Qb, hQbdef⟩ : ∃ Qb : ℝ, Qb = max (max
          (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z / R n) Cg) 1 := ⟨_, rfl⟩
      obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 1 / (2 * max (Ctime' : ℝ) 1) / Qb := ⟨_, rfl⟩
      have hQb1 : (1 : ℝ) ≤ Qb := by rw [hQbdef]; exact le_max_right _ _
      have hQbpos : 0 < Qb := lt_of_lt_of_le one_pos hQb1
      have hQbM : Qb * R n ≤
          max (Cg * R n) (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) := by
        have hCgR : R n ≤ Cg * R n := le_mul_of_one_le_left hR0.le hCg
        have hle : Qb ≤ max (Cg * R n)
            (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) / R n := by
          rw [hQbdef]
          refine max_le (max_le ?_ ?_) ?_
          · exact div_le_div_of_nonneg_right (le_max_right _ _) hR0.le
          · rw [le_div_iff₀ hR0]
            exact le_max_left _ _
          · rw [le_div_iff₀ hR0, one_mul]
            exact hCgR.trans (le_max_left _ _)
        calc Qb * R n ≤ max (Cg * R n)
              (((K n).toHistory.event (j n)).incoming.flow.scalar (t n) z) / R n * R n :=
            mul_le_mul_of_nonneg_right hle hR0.le
          _ = _ := div_mul_cancel₀ _ hR0.ne'
      have hQbQ : Qb * R n ≤ 2 * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ :=
        hQbM.trans (max_le (by linarith only [hq, hA, hQ0]) hB)
      have hT₀v : T₀ n ≤ (v' : ℝ) := hT₀n.trans (show (σ n : ℝ) - max B 1 / R n ≤ v by
        rw [hσ n]; exact hBR)
      have hacc1 : (p n).modelAccuracy ≤ min ε₀ (1 / 2) := (hacc n).trans hacn
      have hDm' : StandardCap.transitionEnd + 10 < (p n).modelRadius := by
        linarith only [hrad n, hTEn]
      have hncK := hnc0 (H := (K n).toHistory) (q := p n) (T₀ := T₀ n) (recordsK n)
        (hacc1.trans (min_le_left _ _)) (le_trans (by omega) (hord n)) (hcanK n)
      have hscaleK : ∀ (e : Fin (K n).eventCount) (he : T₀ n ≤ (K n).time e.succ) b,
          (v' : ℝ) < (K n).toHistory.time e.succ →
          e.succ ≤ (K n).toHistory.activeStage (σ n) →
          2 * max (3 / r ^ 2) (2 * (Qb * R n)) < ((recordsK n e he).static b).neck.scale := by
        intro e he b' hve he4
        have hej : e.succ ≤ (j n).castSucc := hact ▸ he4
        have hwin' : t n - max B 1 / R n ≤ (K n).time e.succ := hBR.trans hve.le
        have hS := hsepn e he b' hej (Or.inl hwin')
        have h8 : 8 * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ <
            ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ := by nlinarith only [h9, hQ0]
        have hn1 : (1 : ℝ) ≤ max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ :=
          le_trans (by linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hQ1
        have hnQ : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ :=
          le_mul_of_one_le_right (Nat.cast_add_one_pos n).le hn1
        have h6 : 6 / r ^ 2 < ((n : ℝ) + 1) * max ((n : ℝ) + 1) (ρs n (t n) ^ 2)⁻¹ := by
          linarith only [hnQ, hr6]
        have h63 : 2 * (3 / r ^ 2) = 6 / r ^ 2 := by ring
        have hmx : max (3 / r ^ 2) (2 * (Qb * R n)) <
            ((recordsK n e he).static b').neck.scale / 2 :=
          max_lt (by linarith only [h6, hS, h63]) (by linarith only [hQbQ, h8, hS])
        linarith only [hmx]
      have hL0 : 0 ≤ L n := le_trans zero_le_one hL6
      have hRa' : 1 ≤ R n * v' := by
        have := mul_le_mul_of_nonneg_left hav' hR0.le
        change 1 ≤ R n * v
        linarith only [this, hRa n]
      have hz' := hz
      rw [← hRn n] at hz'
      obtain ⟨hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hnum⟩ := cstar_numerics_P6SP (Qb := Qb) (R := R n)
        (Rad := Rad) (L := L n) hr hρ hc0 hQb1 (hR1 n) hκdef (by linarith only [hL4])
        (by linarith only [hL5])
      have hTeq : T / R n = 1 / (2 * max (Ctime' : ℝ) 1) / Qb / R n := by rw [hTdef]
      rw [← hTeq] at hnum
      have hstay := stay_cstar_prefix_sepRho_P6SB2 hC2 hCg (K n) (j n) (hjt n) (htj n) (hσ n)
        (haT n) (hsmall n) (hclock n) (seedTrace n) (ha₀ n) (hpin n) (hsT n) (has n) (y n) (yG n)
        (hyG n) (L n) hR0 (hgood n) i first hf z hz' Btr v' hv.1 hv.2 hav hvs hLv hRa' hQbdef hTdef
        hguard hℓ hKℓ hℓr hKr hKC hℓρ hρL ((hT₀X n).trans hav') (hOldX n) (recordsK n) hT₀v
        (hcanK n) (hacc1.trans (min_le_right _ _)) hDm' hncK hscaleK hL0 (hdσ n) hnum
      exact ObservedHistory.slabDeriv_prefix_of_hgood_stay_P6SP (K n) (j n).castSucc (haT n) (hsT n)
        (has n) (seedTrace n) (y n) (R n) (L n) (hgood n) i
        (Btr.point i.castSucc hf (Fin.le_last _)) v' hav hvs hv.1 hv.2 hLv hstay hq

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
