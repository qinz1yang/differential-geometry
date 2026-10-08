import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10HRicCTopCXJF2

/-!
# σ ≤ horizon：`hstop` / ceiling / 条件保护（CX-J10FIN2 G3，后缀 `_CXJF2`）

CXJF G3 的 σ ≤ horizon 版：`hσH : σ < horizon` 换成 `hUSCtop`（仅在 `σ = horizon` 时要：final slab
度量下距离在 horizon 处的左连续；`σ < horizon` 时空真）。其余逐字。
* `hstop_top_CXJF2` / `scalar_le_two_mul_top_ceiling_CXJF2` / `hprotC_top_of_ceiling_CXJF2`；
* `exists_top_ceiling_CXJF2`：`exists_finalSlab_ceiling_CXJF` 的结论逐字，`σ < horizon` → `hUSCtop`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem lt_time_succ_of_le_castSucc_CXJF25 (H : ObservedHistory.{u})
    (v : Icc (0 : ℝ) H.horizon) (e : Fin H.eventCount) (h : H.activeStage v ≤ e.castSucc) :
    (v : ℝ) < H.time e.succ := by
  have hlt : (H.activeStage v : ℕ) < H.eventCount :=
    lt_of_le_of_lt (Fin.le_iff_val_le_val.mp h) e.isLt
  have h1 := H.activeStage_before_next v hlt
  refine h1.trans_le (H.time_strictMono.monotone ?_)
  rw [Fin.le_iff_val_le_val]
  simp only [Fin.val_succ]
  have := Fin.le_iff_val_le_val.mp h
  simp only [Fin.val_castSucc] at this
  omega

private theorem activeStage_eq_of_mem_CXJF25 (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    (v : Icc (0 : ℝ) H.horizon) (h1 : H.time e.castSucc ≤ v) (h2 : (v : ℝ) < H.time e.succ) :
    H.activeStage v = e.castSucc :=
  (H.mem_stageDomain_iff v e.castSucc).mp (by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show (v : ℝ) ∈ Ico (H.time e.castSucc) (H.time e.succ) from ⟨h1, h2⟩))

/-- **条件保护 `hprotC` 的生产（`_CXJF`）**：`[time e⁺, σ]` 上 Good ⇒ CXJT0 stopped ceiling 在 `time e⁺`
给 trace 点 `R_out ≤ 2·Q_b·R`；种子端 K0 `R ≤ 3/r²`；scale 分离 `2·max{3/r², 2Q_bR} < scale_b` ⇒ 两点都
`< scale_b/2` ⇒（`hnc`：树内 `exists_not_ageZeroCapPoint_of_scalar_lt_C11G` 的单 record 形）
不在 cap window 内区。 -/
theorem hprotC_top_of_ceiling_CXJF2
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb T : ℝ} (KH : RetainedCoreHistory.{u})
    {Tn aSeed a σ : Icc (0 : ℝ) KH.toHistory.horizon} (haT : aSeed ≤ Tn) {pT :
      (KH.toHistory.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature KH.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage aSeed)
      (KH.toHistory.activeStage Tn)
      (KH.toHistory.activeStage_mono haT) pT)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (KH.toHistory.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (hR :
      0 < R)
    (hL : 0 ≤ L)
    (hgood : ∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (KH.toHistory.stageAt v).Carrier,
        riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
            (seedTrace.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
              (KH.toHistory.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
              (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
                (KH.toHistory.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v) z →
        KH.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hQb : max (max Cball Cg) 1 ≤ Qb) (hstep : 2 * Ctime' * Qb * T ≤ 1) (haS : aSeed ≤ a)
    (haσ : a ≤ σ)
    (haL : (σ : ℝ) - L ^ 2 / R ≤ a) (hdepth : (σ : ℝ) - a ≤ T / R) {z : (KH.toHistory.stageAt
      σ).Carrier}
    (hz : metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ) z ≤ Cball * R)
    (A : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage a) (KH.toHistory.activeStage σ)
      (KH.toHistory.activeStage_mono haσ) z)
    {q : CutoffParameters} {T₀ : ℝ}
    (records : ∀ e : Fin KH.toHistory.eventCount, T₀ ≤ KH.toHistory.time e.succ →
      GeometricCutoffRecord KH.toHistory e q)
    (hDm : StandardCap.transitionEnd + 10 < q.modelRadius)
    (hnc : ∀ (e : Fin KH.toHistory.eventCount) (he : T₀ ≤ KH.toHistory.time e.succ) (w :
      (KH.toHistory.stage e.succ).Carrier),
      (∀ b, metricScalarAt (KH.toHistory.event e).outputMetric w < ((records e he).static
        b).neck.scale / 2) →
      ¬ ∃ (b : (KH.toHistory.event e).RetainedBoundaryIndex) (x : standardCapWindow q.modelRadius),
        w = ((records e he).static b).window x ∧ ‖x.val‖ < q.modelRadius)
    (hscale : ∀ (e : Fin KH.toHistory.eventCount) (he : T₀ ≤ KH.toHistory.time e.succ) b, (a : ℝ)
      < KH.toHistory.time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale) :
    ∀ (e : Fin KH.toHistory.eventCount) (h1 : KH.toHistory.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ KH.toHistory.activeStage Tn) (h3 : KH.toHistory.activeStage a ≤ e.castSucc)
        (h4 : e.succ ≤ KH.toHistory.activeStage σ) (he : T₀ ≤ KH.toHistory.time e.succ),
        (∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : a ≤ v) (hvσ : v ≤ σ), KH.toHistory.time
          e.succ ≤ (v : ℝ) →
          riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
              (seedTrace.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono
                (haS.trans hav))
                (KH.toHistory.activeStage_mono (hvσ.trans hσT)))
              (A.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
                (KH.toHistory.activeStage_mono hvσ)) <
            riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
                (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
                  (KH.toHistory.activeStage_mono hσT)) y +
              ENNReal.ofReal (L / 2 / Real.sqrt R)) → ∀ b,
        seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} ∧
          A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} := by
  intro e h1 h2 h3 h4 he hgoodE b
  have hτσ : KH.toHistory.time e.succ ≤ σ :=
    (KH.toHistory.time_strictMono.monotone h4).trans (KH.toHistory.activeStage_time_le σ)
  have haτ : (a : ℝ) < KH.toHistory.time e.succ := lt_time_succ_of_le_castSucc_CXJF25 KH.toHistory
    a e h3
  let τI : Icc (0 : ℝ) KH.toHistory.horizon := ⟨KH.toHistory.time e.succ, KH.toHistory.time_nonneg
    _, hτσ.trans σ.2.2⟩
  have haτI : a ≤ τI := haτ.le
  have hτIσ : τI ≤ σ := hτσ
  have hact : KH.toHistory.activeStage τI = e.succ := by
    rcases Fin.eq_castSucc_or_eq_last e.succ with ⟨e2, he2⟩ | hl
    · have hlt : KH.toHistory.time e.succ < KH.toHistory.time e2.succ := by
        rw [he2]
        exact KH.toHistory.time_strictMono e2.castSucc_lt_succ
      exact (activeStage_eq_of_mem_CXJF25 KH.toHistory e2 τI (by rw [← he2]) hlt).trans he2.symm
    · rw [hl]
      exact KH.toHistory.activeStage_eq_last_of_time_last_le τI (by rw [← hl])
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hXle : ∀ X : ℝ≥0∞, X + ENNReal.ofReal (L / 2 / Real.sqrt R) ≤
      X + ENNReal.ofReal (L / Real.sqrt R) := fun X =>
    add_le_add le_rfl (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (by linarith) hsR.le))
  let A' := A.restrictFirst (KH.toHistory.activeStage_mono haτI) (KH.toHistory.activeStage_mono
    hτIσ)
  have hceil := scalar_le_two_mul_stopped_ceiling_CXJT0 KH.toHistory haT hσT has seedTrace y L hR
    hgood hQb
    hstep hτIσ le_rfl (haS.trans haτI) (haL.trans haτ.le) (by
      change (σ : ℝ) - KH.toHistory.time e.succ ≤ T / R
      linarith) hz A' (fun v hav hvt => (hgoodE v (haτI.trans hav) hvt hav).le.trans (hXle _))
  have key : ∀ (m : Fin (KH.toHistory.eventCount + 1)) (hm : KH.toHistory.activeStage τI = m)
      (h3' : KH.toHistory.activeStage a ≤ m) (h4' : m ≤ KH.toHistory.activeStage σ),
      metricScalarAt (KH.toHistory.stageMetric m (KH.toHistory.time e.succ)) (A.point m h3' h4') ≤
        2 * (Qb * R) := by
    intro m hm h3' h4'
    subst hm
    exact hceil τI le_rfl hτIσ
  have hA := key e.succ hact (h3.trans e.castSucc_lt_succ.le) h4
  rw [stageMetric_succ_time_C11G] at hA
  have hS := KH.toHistory.seed_scalar_le_of_smallParabolic_C11G haT hsmall hclock seedTrace τI
    (haS.trans haτI) (hτIσ.trans hσT) e.succ hact (h1.trans e.castSucc_lt_succ.le) h2
  change metricScalarAt (KH.toHistory.stageMetric e.succ (KH.toHistory.time e.succ)) _ ≤ _ at hS
  rw [stageMetric_succ_time_C11G] at hS
  have hsc := fun b' => hscale e he b' haτ
  have hm1 : 3 / r ^ 2 ≤ max (3 / r ^ 2) (2 * (Qb * R)) := le_max_left _ _
  have hm2 : 2 * (Qb * R) ≤ max (3 / r ^ 2) (2 * (Qb * R)) := le_max_right _ _
  have hn1 := hnc e he (seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2)
    fun b' => by linarith [hsc b']
  have hn2 := hnc e he (A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4)
    fun b' => by linarith [hsc b']
  refine ⟨fun ⟨x, hx, hzx⟩ => hn1 ⟨b, x, hzx.symm, ?_⟩,
    fun ⟨x, hx, hzx⟩ => hn2 ⟨b, x, hzx.symm, ?_⟩⟩
  · have hx' : ‖x.val‖ ≤ StandardCap.transitionEnd + 10 := hx
    linarith
  · have hx' : ‖x.val‖ ≤ StandardCap.transitionEnd + 10 := hx
    linarith

/-- **跨 slab `hstop`（`_CXJF`）**：first-exit bootstrap 的整窗定位。 -/
theorem hstop_top_CXJF2 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg Cball Qb T K ℓ D : ℝ} (hC2 : 0 ≤ C2') (KH : RetainedCoreHistory.{u})
    {Tn aSeed a σ : Icc (0 : ℝ) KH.toHistory.horizon} (haT : aSeed ≤ Tn) {pT :
      (KH.toHistory.stageAt Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature KH.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage aSeed)
      (KH.toHistory.activeStage Tn)
      (KH.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) KH.toHistory.horizon) (x : (KH.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (KH.toHistory.stageMetric (KH.toHistory.activeStage t) t) (a₀ + t)
        x)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (KH.toHistory.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (hR :
      0 < R)
    (hgood : ∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (KH.toHistory.stageAt v).Carrier,
        riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
            (seedTrace.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
              (KH.toHistory.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
              (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
                (KH.toHistory.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v) z →
        KH.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hQb : max (max Cball Cg) 1 ≤ Qb) (hstep : 2 * Ctime' * Qb * T ≤ 1)
    (haS : aSeed ≤ a) (haσ : a ≤ σ) 
    (hUSCtop : (σ : ℝ) = KH.toHistory.horizon →
      ∀ (hfT : KH.toHistory.time (Fin.last KH.toHistory.eventCount) < KH.toHistory.horizon)
      (p q : (KH.toHistory.stage (Fin.last KH.toHistory.eventCount)).Carrier) (X' : ℝ≥0∞),
      riemannianEDistOf ((KH.toHistory.finalSlab hfT).flow.base.metric σ) p q < X' →
      ∃ s₁ : ℝ, s₁ < σ ∧ ∀ s' ∈ Icc s₁ (σ : ℝ),
        riemannianEDistOf ((KH.toHistory.finalSlab hfT).flow.base.metric s') p q < X')
    (haL : (σ : ℝ) - L ^ 2 / R ≤ a) (hdepth : (σ : ℝ) - a ≤ T / R) (hRa : 1 ≤ R * a)
    {z : (KH.toHistory.stageAt σ).Carrier}
    (hz : metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ) z ≤ Cball * R)
    (A : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage a) (KH.toHistory.activeStage σ)
      (KH.toHistory.activeStage_mono haσ) z)
    (hℓ : 0 < ℓ) (hKℓ : K * ℓ ^ 2 ≤ 1) (hℓr : ℓ ≤ r / 50) (hKr : 1 / r ^ 2 ≤ K)
    (hKC : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (hℓρ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (hρL : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    {q : CutoffParameters} {T₀ : ℝ} (hT₀ : T₀ ≤ (a : ℝ))
    (records : ∀ e : Fin KH.toHistory.eventCount, T₀ ≤ KH.toHistory.time e.succ →
      GeometricCutoffRecord KH.toHistory e q)
    (hOld : ∀ e : Fin KH.toHistory.eventCount, T₀ ≤ KH.toHistory.time e.succ →
      (KH.toHistory.event e).old = (KH.toHistory.event e).transition.trace.retainedCore)
    (hcan : ∀ (e : Fin KH.toHistory.eventCount) (he : T₀ ≤ KH.toHistory.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (hacc : q.modelAccuracy ≤ 1 / 2) (hDm : StandardCap.transitionEnd + 10 < q.modelRadius)
    (hprotC : ∀ (e : Fin KH.toHistory.eventCount) (h1 : KH.toHistory.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ KH.toHistory.activeStage Tn) (h3 : KH.toHistory.activeStage a ≤ e.castSucc)
        (h4 : e.succ ≤ KH.toHistory.activeStage σ) (he : T₀ ≤ KH.toHistory.time e.succ),
        (∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : a ≤ v) (hvσ : v ≤ σ), KH.toHistory.time
          e.succ ≤ (v : ℝ) →
          riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
              (seedTrace.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono
                (haS.trans hav))
                (KH.toHistory.activeStage_mono (hvσ.trans hσT)))
              (A.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
                (KH.toHistory.activeStage_mono hvσ)) <
            riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
                (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
                  (KH.toHistory.activeStage_mono hσT)) y +
              ENNReal.ofReal (L / 2 / Real.sqrt R)) → ∀ b,
        seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} ∧
          A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10})
    (hzy : z ∈ riemannianBallOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ) y (D /
      Real.sqrt R))
    (hdσ : riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
        (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
          (KH.toHistory.activeStage_mono hσT)) y ≠ ⊤)
    (hnum : D / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R) :
    ∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ σ),
      riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
          (seedTrace.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono (haS.trans
            hav))
            (KH.toHistory.activeStage_mono ((hvt.trans le_rfl).trans hσT)))
          (A.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
            (KH.toHistory.activeStage_mono hvt)) ≤
        riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
            (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
              (KH.toHistory.activeStage_mono hσT)) y +
          ENNReal.ofReal (L / Real.sqrt R) := by
  set dσ := riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
    (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
      (KH.toHistory.activeStage_mono hσT)) y
    with hdσdef
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hD0 : 0 < D / Real.sqrt R :=
    ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le hzy)
  have h8 : 0 ≤ 8 / ℓ := (div_pos (by norm_num) hℓ).le
  have hTR : 0 ≤ T / R := ((sub_nonneg.mpr (show (a : ℝ) ≤ σ from haσ))).trans hdepth
  have hdrift : 8 / ℓ * ((σ : ℝ) - a) ≤ 8 / ℓ * (T / R) := mul_le_mul_of_nonneg_left hdepth h8
  have hmargin : riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
        (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono (haS.trans
          haσ))
          (KH.toHistory.activeStage_mono hσT)) z +
      ENNReal.ofReal ((8 / ℓ) * ((σ : ℝ) - a)) < dσ + ENNReal.ofReal (L / 2 / Real.sqrt R) :=
    calc _ ≤ (dσ + riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ) y
      z) +
          ENNReal.ofReal (8 / ℓ * (T / R)) :=
          add_le_add (riemannianEDistOf_triangle _ _ _ _) (ENNReal.ofReal_le_ofReal hdrift)
      _ < (dσ + ENNReal.ofReal (D / Real.sqrt R)) + ENNReal.ofReal (8 / ℓ * (T / R)) :=
          ENNReal.add_lt_add_right ENNReal.ofReal_ne_top (ENNReal.add_lt_add_left hdσ hzy)
      _ = dσ + ENNReal.ofReal (D / Real.sqrt R + 8 / ℓ * (T / R)) := by
          rw [add_assoc, ← ENNReal.ofReal_add hD0.le (mul_nonneg h8 hTR)]
      _ ≤ dσ + ENNReal.ofReal (L / 2 / Real.sqrt R) :=
          add_le_add le_rfl (ENNReal.ofReal_le_ofReal hnum.le)
  have hL : L / 2 / Real.sqrt R ≤ L / Real.sqrt R := by
    have : 0 < L / 2 / Real.sqrt R := lt_trans (by positivity) hnum
    have hL0 : 0 < L := by
      by_contra hn
      have : L / 2 / Real.sqrt R ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hsR.le
      linarith
    exact div_le_div_of_nonneg_right (by linarith) hsR.le
  have hfe := KH.toHistory.edist_trace_le_of_firstExit_top_CXJF2 haT seedTrace haS haσ hσT A
    hUSCtop hℓ
    hT₀ records
    hOld hcan hacc hDm hprotC (hRicC_top_of_hgood_ceiling_CXJF2 hC2 KH haT hsmall hclock seedTrace
      ha₀
      hpin hσT has y L hR hgood hQb hstep haS haσ haL hdepth hRa hz A hℓ hKℓ hℓr hKr hKC hℓρ
      hρL) hmargin
  intro v hav hvt
  have hv := hfe v hav hvt
  have hdv : 8 / ℓ * ((σ : ℝ) - v) ≤ 8 / ℓ * ((σ : ℝ) - a) :=
    mul_le_mul_of_nonneg_left (by linarith [show (a : ℝ) ≤ v from hav]) h8
  exact hv.trans ((add_le_add le_rfl (ENNReal.ofReal_le_ofReal hdv)).trans
    (hmargin.le.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hL))))

/-- **consumer：跨 slab ceiling（`_CXJF`）**：`hstop_top_CXJF2` 喂 CXJT0
`scalar_le_two_mul_stopped_ceiling_CXJT0` ⇒ 沿 trace `[a, σ]`（跨 slab）`R ≤ 2·Q_b·R`。 -/
theorem scalar_le_two_mul_top_ceiling_CXJF2 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg Cball Qb T K ℓ D : ℝ} (hC2 : 0 ≤ C2') (KH : RetainedCoreHistory.{u})
    {Tn aSeed a σ : Icc (0 : ℝ) KH.toHistory.horizon} (haT : aSeed ≤ Tn) {pT :
      (KH.toHistory.stageAt Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature KH.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage aSeed)
      (KH.toHistory.activeStage Tn)
      (KH.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) KH.toHistory.horizon) (x : (KH.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (KH.toHistory.stageMetric (KH.toHistory.activeStage t) t) (a₀ + t)
        x)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (KH.toHistory.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (hR :
      0 < R)
    (hgood : ∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (KH.toHistory.stageAt v).Carrier,
        riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
            (seedTrace.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
              (KH.toHistory.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
              (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
                (KH.toHistory.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v) z →
        KH.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hQb : max (max Cball Cg) 1 ≤ Qb) (hstep : 2 * Ctime' * Qb * T ≤ 1)
    (haS : aSeed ≤ a) (haσ : a ≤ σ) 
    (hUSCtop : (σ : ℝ) = KH.toHistory.horizon →
      ∀ (hfT : KH.toHistory.time (Fin.last KH.toHistory.eventCount) < KH.toHistory.horizon)
      (p q : (KH.toHistory.stage (Fin.last KH.toHistory.eventCount)).Carrier) (X' : ℝ≥0∞),
      riemannianEDistOf ((KH.toHistory.finalSlab hfT).flow.base.metric σ) p q < X' →
      ∃ s₁ : ℝ, s₁ < σ ∧ ∀ s' ∈ Icc s₁ (σ : ℝ),
        riemannianEDistOf ((KH.toHistory.finalSlab hfT).flow.base.metric s') p q < X')
    (haL : (σ : ℝ) - L ^ 2 / R ≤ a) (hdepth : (σ : ℝ) - a ≤ T / R) (hRa : 1 ≤ R * a)
    {z : (KH.toHistory.stageAt σ).Carrier}
    (hz : metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ) z ≤ Cball * R)
    (A : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage a) (KH.toHistory.activeStage σ)
      (KH.toHistory.activeStage_mono haσ) z)
    (hℓ : 0 < ℓ) (hKℓ : K * ℓ ^ 2 ≤ 1) (hℓr : ℓ ≤ r / 50) (hKr : 1 / r ^ 2 ≤ K)
    (hKC : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (hℓρ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (hρL : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    {q : CutoffParameters} {T₀ : ℝ} (hT₀ : T₀ ≤ (a : ℝ))
    (records : ∀ e : Fin KH.toHistory.eventCount, T₀ ≤ KH.toHistory.time e.succ →
      GeometricCutoffRecord KH.toHistory e q)
    (hOld : ∀ e : Fin KH.toHistory.eventCount, T₀ ≤ KH.toHistory.time e.succ →
      (KH.toHistory.event e).old = (KH.toHistory.event e).transition.trace.retainedCore)
    (hcan : ∀ (e : Fin KH.toHistory.eventCount) (he : T₀ ≤ KH.toHistory.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (hacc : q.modelAccuracy ≤ 1 / 2) (hDm : StandardCap.transitionEnd + 10 < q.modelRadius)
    (hprotC : ∀ (e : Fin KH.toHistory.eventCount) (h1 : KH.toHistory.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ KH.toHistory.activeStage Tn) (h3 : KH.toHistory.activeStage a ≤ e.castSucc)
        (h4 : e.succ ≤ KH.toHistory.activeStage σ) (he : T₀ ≤ KH.toHistory.time e.succ),
        (∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : a ≤ v) (hvσ : v ≤ σ), KH.toHistory.time
          e.succ ≤ (v : ℝ) →
          riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
              (seedTrace.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono
                (haS.trans hav))
                (KH.toHistory.activeStage_mono (hvσ.trans hσT)))
              (A.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
                (KH.toHistory.activeStage_mono hvσ)) <
            riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
                (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
                  (KH.toHistory.activeStage_mono hσT)) y +
              ENNReal.ofReal (L / 2 / Real.sqrt R)) → ∀ b,
        seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} ∧
          A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10})
    (hzy : z ∈ riemannianBallOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ) y (D /
      Real.sqrt R))
    (hdσ : riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
        (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
          (KH.toHistory.activeStage_mono hσT)) y ≠ ⊤)
    (hnum : D / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R) :
    ∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ σ),
      metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
        (A.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
          (KH.toHistory.activeStage_mono hvt)) ≤
        2 * (Qb * R) :=
  scalar_le_two_mul_stopped_ceiling_CXJT0 KH.toHistory haT hσT has seedTrace y L hR hgood hQb
    hstep haσ le_rfl
    haS haL hdepth hz A (hstop_top_CXJF2 hC2 KH haT hsmall hclock seedTrace ha₀ hpin hσT
      has y L hR hgood hQb hstep haS haσ hUSCtop haL hdepth hRa hz A hℓ hKℓ hℓr hKr hKC hℓρ hρL hT₀
      records hOld hcan hacc hDm
      hprotC hzy hdσ hnum)

/-- **跨 slab ceiling，ε₀ 形（`_CXJF`）**：存在绝对常数 `ε₀ > 0`（树内 cap window 标量下界的常数），
records 精度 `≤ ε₀`、阶 `≥ 2`、scale 分离 `2·max{3/r², 2Q_bR} < scale_b` ⇒ 条件保护由 ceiling 自付，
`scalar_le_two_mul_top_ceiling_CXJF2` 无 `hprotC` 前提。 -/
theorem exists_top_ceiling_CXJF2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb T K ℓ D : ℝ} (_ : 0 ≤ C2')
    (KH : RetainedCoreHistory.{u}) {Tn aSeed a σ : Icc (0 : ℝ) KH.toHistory.horizon} (haT : aSeed
      ≤ Tn)
    {pT : (KH.toHistory.stageAt Tn).Carrier} {r : ℝ}
    (_ : GC.LongTime.hasSmallParabolicCurvature KH.toHistory Tn pT r)
    (_ : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage aSeed)
      (KH.toHistory.activeStage Tn)
      (KH.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (_ : 0 ≤ a₀)
    (_ : ∀ (t : Icc (0 : ℝ) KH.toHistory.horizon) (x : (KH.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (KH.toHistory.stageMetric (KH.toHistory.activeStage t) t) (a₀ + t)
        x)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (KH.toHistory.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (_ : 0
      < R)
    (_ : ∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (KH.toHistory.stageAt v).Carrier,
        riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
            (seedTrace.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
              (KH.toHistory.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
              (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
                (KH.toHistory.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v) z →
        KH.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (_ : max (max Cball Cg) 1 ≤ Qb) (_ : 2 * Ctime' * Qb * T ≤ 1) (_ : aSeed ≤ a)
    (haσ : a ≤ σ) 
    (_ : (σ : ℝ) = KH.toHistory.horizon →
      ∀ (hfT : KH.toHistory.time (Fin.last KH.toHistory.eventCount) < KH.toHistory.horizon)
      (p q : (KH.toHistory.stage (Fin.last KH.toHistory.eventCount)).Carrier) (X' : ℝ≥0∞),
      riemannianEDistOf ((KH.toHistory.finalSlab hfT).flow.base.metric σ) p q < X' →
      ∃ s₁ : ℝ, s₁ < σ ∧ ∀ s' ∈ Icc s₁ (σ : ℝ),
        riemannianEDistOf ((KH.toHistory.finalSlab hfT).flow.base.metric s') p q < X')
    (_ : (σ : ℝ) - L ^ 2 / R ≤ a) (_ : (σ : ℝ) - a ≤ T / R) (_ : 1 ≤ R * a)
    {z : (KH.toHistory.stageAt σ).Carrier}
    (_ : metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ) z ≤ Cball * R)
    (A : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage a) (KH.toHistory.activeStage σ)
      (KH.toHistory.activeStage_mono haσ) z)
    (_ : 0 < ℓ) (_ : K * ℓ ^ 2 ≤ 1) (_ : ℓ ≤ r / 50) (_ : 1 / r ^ 2 ≤ K)
    (_ : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (_ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (_ : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    {q : CutoffParameters} {T₀ : ℝ} (_ : T₀ ≤ (a : ℝ))
    (records : ∀ e : Fin KH.toHistory.eventCount, T₀ ≤ KH.toHistory.time e.succ →
      GeometricCutoffRecord KH.toHistory e q)
    (_ : ∀ e : Fin KH.toHistory.eventCount, T₀ ≤ KH.toHistory.time e.succ →
      (KH.toHistory.event e).old = (KH.toHistory.event e).transition.trace.retainedCore)
    (_ : ∀ (e : Fin KH.toHistory.eventCount) (he : T₀ ≤ KH.toHistory.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (_ : StandardCap.transitionEnd + 10 < q.modelRadius)
    (_ : q.modelAccuracy ≤ ε₀) (_ : 2 ≤ q.modelOrder)
    (_ : ∀ (e : Fin KH.toHistory.eventCount) (he : T₀ ≤ KH.toHistory.time e.succ) b, (a : ℝ) <
      KH.toHistory.time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale)
    (_ : z ∈ riemannianBallOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ) y (D /
      Real.sqrt R))
    (_ : riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
        (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
          (KH.toHistory.activeStage_mono hσT)) y ≠ ⊤)
    (_ : D / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R),
      ∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ σ),
        metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
          (A.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
            (KH.toHistory.activeStage_mono hvt)) ≤
          2 * (Qb * R) := by
  obtain ⟨ε₀, hε₀, hnc0⟩ := exists_not_ageZeroCapPoint_of_scalar_lt_C11G.{u}
  refine ⟨min ε₀ (1 / 2), lt_min hε₀ (by norm_num), ?_⟩
  intro eps C1' C2' Ctime' Cg Cball Qb T K ℓ D hC2 KH Tn aSeed a σ haT pT r hsmall
    hclock seedTrace
    a₀ ha₀ hpin hσT has y R L hR hgood hQb hstep haS haσ hUSCtop haL hdepth hRa z hz A hℓ hKℓ hℓr
    hKr
    hKC hℓρ hρL q T₀ hT₀ records hOld hcan hDm hacc hm hscale hzy hdσ hnum
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hL : 0 ≤ L := by
    have hD0 : 0 < D / Real.sqrt R := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le hzy)
    have hTR : 0 ≤ T / R := (sub_nonneg.mpr (show (a : ℝ) ≤ σ from haσ)).trans hdepth
    have h8 : 0 ≤ 8 / ℓ * (T / R) := mul_nonneg (div_pos (by norm_num) hℓ).le hTR
    have hpos : 0 < L / 2 / Real.sqrt R := by linarith
    by_contra hn
    have : L / 2 / Real.sqrt R ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith [not_le.mp hn]) hsR.le
    linarith
  have hnc : ∀ (e : Fin KH.toHistory.eventCount) (he : T₀ ≤ KH.toHistory.time e.succ) (w :
    (KH.toHistory.stage e.succ).Carrier),
      (∀ b, metricScalarAt (KH.toHistory.event e).outputMetric w < ((records e he).static
        b).neck.scale / 2) →
      ¬ ∃ (b : (KH.toHistory.event e).RetainedBoundaryIndex) (x : standardCapWindow q.modelRadius),
        w = ((records e he).static b).window x ∧ ‖x.val‖ < q.modelRadius := by
    intro e he w hw
    have h := hnc0 (records e he) (hacc.trans (min_le_left _ _)) hm (hcan e he)
      (Dcap := q.modelRadius - 1) (by linarith) w hw
    simpa only [sub_add_cancel] using h
  exact scalar_le_two_mul_top_ceiling_CXJF2 hC2 KH haT hsmall hclock seedTrace ha₀ hpin hσT has
    y L hR hgood hQb hstep haS haσ hUSCtop haL hdepth hRa hz A hℓ hKℓ hℓr hKr hKC hℓρ hρL hT₀
    records
    hOld hcan (hacc.trans (min_le_right _ _)) hDm
    (hprotC_top_of_ceiling_CXJF2 KH haT hsmall hclock seedTrace hσT has y L hR hL hgood hQb hstep
      haS haσ haL hdepth hz A records hDm hnc hscale)
    hzy hdσ hnum

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
