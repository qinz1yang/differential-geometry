import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10CrossSlabCeilingCXJD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointProtectionC11G

/-!
# crossing 条件保护的生产 + 跨 slab ceiling 的 ε₀ 形（CX-J10DIST G5，后缀 `_CXJD`）

G2/G4 的 crossing 保护 `hprotC` 是**条件**形（`[time e⁺, σ]` 上 trace 在 Ω′ 内时才要）。本文件：
* `hprotC_of_ceiling_CXJD`：Good ⇒ CXJT0 stopped ceiling 在 `time e⁺` 给 `R_out(A(e⁺)) ≤ 2·Q_b·R`，
  种子端 K0
  `R ≤ 3/r²`；scale 分离 + 树内 cap window 标量下界（`exists_not_ageZeroCapPoint_of_scalar_lt_C11G` 的单
  record 形 `hnc`）⇒ 两点不在 cap window 内区（DIST (D4) 的保护前提）。
* `exists_crossSlab_ceiling_CXJD`：`∃ ε₀ > 0`，records 精度 `≤ ε₀`、阶 `≥ 2`、scale 分离 ⇒
  跨 slab 沿 trace `R ≤ 2·Q_b·R`（无 `hprotC`、无 `hstop` 前提）。
scale 分离比较的是 surgery cap 的 `neck.scale` 与 `2Q_bR`，不是 `qcap` 与 `R`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem lt_time_succ_of_le_castSucc_CXJD5 (H : ObservedHistory.{u})
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

private theorem activeStage_eq_of_mem_CXJD5 (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    (v : Icc (0 : ℝ) H.horizon) (h1 : H.time e.castSucc ≤ v) (h2 : (v : ℝ) < H.time e.succ) :
    H.activeStage v = e.castSucc :=
  (H.mem_stageDomain_iff v e.castSucc).mp (by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show (v : ℝ) ∈ Ico (H.time e.castSucc) (H.time e.succ) from ⟨h1, h2⟩))

/-- **条件保护 `hprotC` 的生产（`_CXJD`）**：`[time e⁺, σ]` 上 Good ⇒ CXJT0 stopped ceiling 在 `time e⁺`
给 trace 点 `R_out ≤ 2·Q_b·R`；种子端 K0 `R ≤ 3/r²`；scale 分离 `2·max{3/r², 2Q_bR} < scale_b` ⇒ 两点都
`< scale_b/2` ⇒（`hnc`：树内 `exists_not_ageZeroCapPoint_of_scalar_lt_C11G` 的单 record 形）
不在 cap window 内区。 -/
theorem hprotC_of_ceiling_CXJD
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb T : ℝ} (H : ObservedHistory.{u})
    {Tn aSeed a σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (H.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (hR : 0 < R)
    (hL : 0 ≤ L)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hQb : max (max Cball Cg) 1 ≤ Qb) (hstep : 2 * Ctime' * Qb * T ≤ 1) (haS : aSeed ≤ a)
    (haσ : a ≤ σ) (hσlast : H.activeStage σ < Fin.last H.eventCount)
    (haL : (σ : ℝ) - L ^ 2 / R ≤ a) (hdepth : (σ : ℝ) - a ≤ T / R) {z : (H.stageAt σ).Carrier}
    (hz : metricScalarAt (H.stageMetric (H.activeStage σ) σ) z ≤ Cball * R)
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage σ) (H.activeStage_mono haσ) z)
    {q : CutoffParameters} {T₀ : ℝ}
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q)
    (hDm : StandardCap.transitionEnd + 10 < q.modelRadius)
    (hnc : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) (w : (H.stage e.succ).Carrier),
      (∀ b, metricScalarAt (H.event e).outputMetric w < ((records e he).static b).neck.scale / 2) →
      ¬ ∃ (b : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow q.modelRadius),
        w = ((records e he).static b).window x ∧ ‖x.val‖ < q.modelRadius)
    (hscale : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b, (a : ℝ) < H.time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale) :
    ∀ (e : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ e.castSucc)
        (h2 : e.succ ≤ H.activeStage Tn) (h3 : H.activeStage a ≤ e.castSucc)
        (h4 : e.succ ≤ H.activeStage σ) (he : T₀ ≤ H.time e.succ),
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvσ : v ≤ σ), H.time e.succ ≤ (v : ℝ) →
          riemannianEDistOf (H.stageMetric (H.activeStage v) v)
              (seedTrace.point (H.activeStage v) (H.activeStage_mono (haS.trans hav))
                (H.activeStage_mono (hvσ.trans hσT)))
              (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvσ)) <
            riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
                (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                  (H.activeStage_mono hσT)) y +
              ENNReal.ofReal (L / 2 / Real.sqrt R)) → ∀ b,
        seedTrace.point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} ∧
          A.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
            ((records e he).static b).window ''
              {w : standardCapWindow q.modelRadius | ‖w.val‖ ≤ StandardCap.transitionEnd + 10} := by
  intro e h1 h2 h3 h4 he hgoodE b
  have hτσ : H.time e.succ ≤ σ :=
    (H.time_strictMono.monotone h4).trans (H.activeStage_time_le σ)
  have haτ : (a : ℝ) < H.time e.succ := lt_time_succ_of_le_castSucc_CXJD5 H a e h3
  let τI : Icc (0 : ℝ) H.horizon := ⟨H.time e.succ, H.time_nonneg _, hτσ.trans σ.2.2⟩
  have haτI : a ≤ τI := haτ.le
  have hτIσ : τI ≤ σ := hτσ
  obtain ⟨e2, he2⟩ := Fin.exists_castSucc_eq.mpr (ne_of_lt (h4.trans_lt hσlast))
  have hlt : H.time e.succ < H.time e2.succ := by
    rw [← he2]
    exact H.time_strictMono e2.castSucc_lt_succ
  have hact : H.activeStage τI = e.succ :=
    (activeStage_eq_of_mem_CXJD5 H e2 τI (by rw [he2]) hlt).trans he2
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hXle : ∀ X : ℝ≥0∞, X + ENNReal.ofReal (L / 2 / Real.sqrt R) ≤
      X + ENNReal.ofReal (L / Real.sqrt R) := fun X =>
    add_le_add le_rfl (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (by linarith) hsR.le))
  let A' := A.restrictFirst (H.activeStage_mono haτI) (H.activeStage_mono hτIσ)
  have hceil := scalar_le_two_mul_stopped_ceiling_CXJT0 H haT hσT has seedTrace y L hR hgood hQb
    hstep hτIσ le_rfl (haS.trans haτI) (haL.trans haτ.le) (by
      change (σ : ℝ) - H.time e.succ ≤ T / R
      linarith) hz A' (fun v hav hvt => (hgoodE v (haτI.trans hav) hvt hav).le.trans (hXle _))
  have key : ∀ (m : Fin (H.eventCount + 1)) (hm : H.activeStage τI = m)
      (h3' : H.activeStage a ≤ m) (h4' : m ≤ H.activeStage σ),
      metricScalarAt (H.stageMetric m (H.time e.succ)) (A.point m h3' h4') ≤ 2 * (Qb * R) := by
    intro m hm h3' h4'
    subst hm
    exact hceil τI le_rfl hτIσ
  have hA := key e.succ hact (h3.trans e.castSucc_lt_succ.le) h4
  rw [stageMetric_succ_time_C11G] at hA
  have hS := H.seed_scalar_le_of_smallParabolic_C11G haT hsmall hclock seedTrace τI
    (haS.trans haτI) (hτIσ.trans hσT) e.succ hact (h1.trans e.castSucc_lt_succ.le) h2
  change metricScalarAt (H.stageMetric e.succ (H.time e.succ)) _ ≤ _ at hS
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

/-- **跨 slab ceiling，ε₀ 形（`_CXJD`）**：存在绝对常数 `ε₀ > 0`（树内 cap window 标量下界的常数），
records 精度 `≤ ε₀`、阶 `≥ 2`、scale 分离 `2·max{3/r², 2Q_bR} < scale_b` ⇒ 条件保护由 ceiling 自付，
`scalar_le_two_mul_crossSlab_ceiling_CXJD` 无 `hprotC` 前提。 -/
theorem exists_crossSlab_ceiling_CXJD :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb T K ℓ D : ℝ} (_ : 0 ≤ C2')
    (H : ObservedHistory.{u}) {Tn aSeed a σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (_ : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (_ : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (_ : 0 ≤ a₀)
    (_ : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (H.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (_ : 0 < R)
    (_ : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hσT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (_ : max (max Cball Cg) 1 ≤ Qb) (_ : 2 * Ctime' * Qb * T ≤ 1) (_ : aSeed ≤ a)
    (haσ : a ≤ σ) (_ : H.activeStage σ < Fin.last H.eventCount)
    (_ : (σ : ℝ) - L ^ 2 / R ≤ a) (_ : (σ : ℝ) - a ≤ T / R) (_ : 1 ≤ R * a)
    {z : (H.stageAt σ).Carrier}
    (_ : metricScalarAt (H.stageMetric (H.activeStage σ) σ) z ≤ Cball * R)
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage σ) (H.activeStage_mono haσ) z)
    (_ : 0 < ℓ) (_ : K * ℓ ^ 2 ≤ 1) (_ : ℓ ≤ r / 50) (_ : 1 / r ^ 2 ≤ K)
    (_ : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (_ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (_ : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R)
    {q : CutoffParameters} {T₀ : ℝ} (_ : T₀ ≤ (a : ℝ))
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q)
    (_ : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ →
      (H.event e).old = (H.event e).transition.trace.retainedCore)
    (_ : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (_ : StandardCap.transitionEnd + 10 < q.modelRadius)
    (_ : q.modelAccuracy ≤ ε₀) (_ : 2 ≤ q.modelOrder)
    (_ : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b, (a : ℝ) < H.time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale)
    (_ : z ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y (D / Real.sqrt R))
    (_ : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
        (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
          (H.activeStage_mono hσT)) y ≠ ⊤)
    (_ : D / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / Real.sqrt R),
      ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ σ),
        metricScalarAt (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤
          2 * (Qb * R) := by
  obtain ⟨ε₀, hε₀, hnc0⟩ := exists_not_ageZeroCapPoint_of_scalar_lt_C11G.{u}
  refine ⟨min ε₀ (1 / 2), lt_min hε₀ (by norm_num), ?_⟩
  intro eps C1' C2' Ctime' Cg Cball Qb T K ℓ D hC2 H Tn aSeed a σ haT pT r hsmall hclock seedTrace
    a₀ ha₀ hpin hσT has y R L hR hgood hQb hstep haS haσ hσlast haL hdepth hRa z hz A hℓ hKℓ hℓr hKr
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
  have hnc : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) (w : (H.stage e.succ).Carrier),
      (∀ b, metricScalarAt (H.event e).outputMetric w < ((records e he).static b).neck.scale / 2) →
      ¬ ∃ (b : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow q.modelRadius),
        w = ((records e he).static b).window x ∧ ‖x.val‖ < q.modelRadius := by
    intro e he w hw
    have h := hnc0 (records e he) (hacc.trans (min_le_left _ _)) hm (hcan e he)
      (Dcap := q.modelRadius - 1) (by linarith) w hw
    simpa only [sub_add_cancel] using h
  exact scalar_le_two_mul_crossSlab_ceiling_CXJD hC2 H haT hsmall hclock seedTrace ha₀ hpin hσT has
    y L hR hgood hQb hstep haS haσ hσlast haL hdepth hRa hz A hℓ hKℓ hℓr hKr hKC hℓρ hρL hT₀ records
    hOld hcan (hacc.trans (min_le_right _ _)) hDm
    (hprotC_of_ceiling_CXJD H haT hsmall hclock seedTrace hσT has y L hR hL hgood hQb hstep
      haS haσ hσlast haL hdepth hz A records hDm hnc hscale)
    hzy hdσ hnum

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
