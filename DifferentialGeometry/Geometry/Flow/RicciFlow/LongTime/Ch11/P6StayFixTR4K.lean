import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StayTRpcP6KA

/-!
# R4KAP G1：固定 `t` 的跨 slab stay（`hstopE_body_deep_pc_P6KA` 的固定 t 孪生，后缀 `_R4K`）

`hstopE_body_deep_pc_P6KA` 的 `∀ᶠ t ↑ σ` 只来自 (a) `surgery_no_shortcut_C11D` 的平移界（δ = L/(2√R)）
与 (b) `σ − ¾L²/R < t < time i⁺`、`time i⁻ < t`——都不依赖 `(T, ρb, K, ℓ, β)`。本孪生把 `t` 固定：
(a) 换成前提 `hdy`（d_t(O, y′) ≤ d_σ(O, y) + L/(2√R)；R4 中心由 E2a′ 的 hcompR 付），(b) 换成三条点态
前提；端点球界 / 格点界 `hbt` / `hgt` 由 `∀ᶠ t` 内蕴含改为点态前提。去掉 (a) 后 `hscale` 只在
`hprotC_scalC_CXJP` 处用、且只需 `a < time e.succ`，故收窄到窗口事件 `Tlo < time e.succ`（`Tlo ≤ t − T/R`）。
其余证明逐字。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **固定 `t` 的 stay 体（`_R4K`，PROVED）**：见模块文档。 -/
theorem hstopE_body_deep_fixT_R4K :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg Cball Qb T K ℓ ρb β : ℝ} (_ : 0 ≤ C2')
    (KH : RetainedCoreHistory.{u}) (H : ObservedHistory.{u}) (_ : KH.toHistory = H)
    {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    {pT : (H.stageAt Tn).Carrier} {r : ℝ}
    (_ : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (_ : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (_ : 0 ≤ a₀)
    (_ : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (H.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (_ : 0 < R)
    (_ : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (_ : max (max Cball Cg) 1 ≤ Qb) (_ : 0 < β) (_ : 2 * Ctime' * Qb * β ≤ 1)
    (_ : 0 < T)
    (_ : T ≤ (L / 2) ^ 2) (_ : 0 ≤ L) (_ : 1 ≤ R * aSeed) (_ : (aSeed : ℝ) < σ)
    (_ : 0 < ℓ) (_ : K * ℓ ^ 2 ≤ 1) (_ : ℓ ≤ r / 50) (_ : 1 / r ^ 2 ≤ K)
    (_ : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (_ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (_ : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / 2 / Real.sqrt R)
    (_ : ρb / Real.sqrt R + 8 / ℓ * (T / R) < L / 2 / 2 / Real.sqrt R)
    {q : CutoffParameters} {T₀ : ℝ} (_ : T₀ ≤ (aSeed : ℝ))
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → GeometricCutoffRecord H e q)
    (_ : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ →
      (H.event e).old = (H.event e).transition.trace.retainedCore)
    (_ : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
      ((records e he).static b).hasCanonicalWindow)
    (_ : StandardCap.transitionEnd + 10 < q.modelRadius)
    (_ : q.modelAccuracy ≤ ε₀) (_ : 2 ≤ q.modelOrder)
    {Tlo t : ℝ} (_ : Tlo ≤ t - T / R)
    (_ : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b, Tlo < H.time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale)
    (_ : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
        (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
          (H.activeStage_mono hsT)) y ≠ ⊤)
    (i : Fin H.eventCount) (_ : (σ : ℝ) = H.time i.succ)
    (p' : (H.stage i.castSucc).Carrier)
    (_ : H.time i.castSucc < t) (_ : t < H.time i.succ)
    (_ : (σ : ℝ) - 3 / 4 * (L ^ 2 / R) < t)
    (_ : ∀ (tt : Icc (0 : ℝ) H.horizon), (tt : ℝ) = t → ∀ (haStt : aSeed ≤ tt) (httT : tt ≤ Tn)
      (y' : (H.stageAt tt).Carrier), HEq y' p' →
      riemannianEDistOf (H.stageMetric (H.activeStage tt) tt)
          (seedTrace.point (H.activeStage tt) (H.activeStage_mono haStt)
            (H.activeStage_mono httT)) y' ≤
        riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
            (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y +
          ENNReal.ofReal (L / 2 / Real.sqrt R))
    (_ : ∀ z ∈ riemannianBallOf ((H.event i).incoming.flow.base.metric t) p' (ρb / Real.sqrt R),
        metricScalarAt ((H.event i).incoming.flow.base.metric t) z ≤ Cball * R)
    (_ : ∀ (tt : Icc (0 : ℝ) H.horizon), (tt : ℝ) = t → tt ≤ σ →
      ∀ (a : Icc (0 : ℝ) H.horizon), aSeed ≤ a → ∀ (hat : a ≤ tt), t - T / R ≤ (a : ℝ) →
      ∀ z' : (H.stageAt tt).Carrier,
        (∀ z : (H.stage i.castSucc).Carrier, HEq z' z →
          z ∈ riemannianBallOf ((H.event i).incoming.flow.base.metric t) p'
            (ρb / Real.sqrt R)) →
      ∀ (A : BackwardPointTrace H (H.activeStage a) (H.activeStage tt) (H.activeStage_mono hat) z')
        (j : ℕ), 1 ≤ j → ∀ (w : Icc (0 : ℝ) H.horizon) (haw : a ≤ w) (hwt : w ≤ tt),
        (w : ℝ) = t - j * β / R →
        metricScalarAt (H.stageMetric (H.activeStage w) w)
          (A.point (H.activeStage w) (H.activeStage_mono haw) (H.activeStage_mono hwt)) ≤
          Qb * R),
      ∀ (tt : Icc (0 : ℝ) H.horizon), (tt : ℝ) = t → ∀ (htσ : tt ≤ σ)
        (a : Icc (0 : ℝ) H.horizon) (haS' : aSeed ≤ a) (hat : a ≤ tt), t - T / R ≤ (a : ℝ) →
      ∀ z' : (H.stageAt tt).Carrier,
        (∀ z : (H.stage i.castSucc).Carrier, HEq z' z →
          z ∈ riemannianBallOf ((H.event i).incoming.flow.base.metric t) p'
            (ρb / Real.sqrt R)) →
      ∀ (A : BackwardPointTrace H (H.activeStage a) (H.activeStage tt) (H.activeStage_mono hat) z')
        (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ tt),
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono (haS'.trans hav))
              (H.activeStage_mono ((hvt.trans htσ).trans hsT)))
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) := by
  obtain ⟨ε₀, hε₀, hnc0⟩ := exists_not_ageZeroCapPoint_of_scalar_lt_C11G.{u}
  refine ⟨min ε₀ (1 / 2), lt_min hε₀ (by norm_num), ?_⟩
  intro eps C1' C2' Ctime' Cg Cball Qb T K ℓ ρb β hC2 KH H hKH Tn aSeed σ haT pT r hsmall hclock
    seedTrace a₀ ha₀ hpin hsT has y R L hR hgood hQb hβ hβs hT hTL hL hRa haσ hℓ hKℓ hℓr hKr hKC
    hℓρ hρL hnum q T₀ hT₀ records hOld hcan hDm hacc hm Tlo t hTlo hscale hfin i hσi p' ht1 ht2
    ht3 hdy0 hbt hgt
  have hnc : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) (w : (H.stage e.succ).Carrier),
      (∀ b, metricScalarAt (H.event e).outputMetric w < ((records e he).static b).neck.scale / 2) →
      ¬ ∃ (b : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow q.modelRadius),
        w = ((records e he).static b).window x ∧ ‖x.val‖ < q.modelRadius := by
    intro e he w hw
    have h := hnc0 (records e he) (hacc.trans (min_le_left _ _)) hm (hcan e he)
      (Dcap := q.modelRadius - 1) (by linarith) w hw
    simpa only [sub_add_cancel] using h
  have hiT : H.time i.succ ≤ (Tn : ℝ) := by
    rw [← hσi]
    exact hsT
  have h2i : i.succ ≤ H.activeStage Tn := H.le_activeStage Tn i.succ hiT
  have h1i : H.activeStage aSeed ≤ i.castSucc := by
    rw [Fin.le_castSucc_iff]
    by_contra hle
    have h1 := H.time_strictMono.monotone (not_lt.mp hle)
    have h2 := H.activeStage_time_le aSeed
    have h3 : (aSeed : ℝ) = aSeed.1 := rfl
    linarith
  have h2c : i.castSucc ≤ H.activeStage Tn := i.castSucc_lt_succ.le.trans h2i
  have hLpos : 0 < L := by nlinarith
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hδ : 0 < L / 2 / Real.sqrt R := div_pos (div_pos hLpos two_pos) hsR
  have hhalf : ENNReal.ofReal (L / 2 / Real.sqrt R) + ENNReal.ofReal (L / 2 / Real.sqrt R) =
      ENNReal.ofReal (L / Real.sqrt R) := by
    rw [← ENNReal.ofReal_add hδ.le hδ.le]
    congr 1
    ring
  have hsum : ∀ X : ℝ≥0∞, X + ENNReal.ofReal (L / 2 / Real.sqrt R) +
      ENNReal.ofReal (L / 2 / Real.sqrt R) = X + ENNReal.ofReal (L / Real.sqrt R) := fun X => by
    rw [add_assoc, hhalf]
  have hq4 : (L / 2) ^ 2 / R = 1 / 4 * (L ^ 2 / R) := by ring
  intro tt htt htσ a haS' hat hlo z' hP A v hav hvt
  have he : H.activeStage tt = i.castSucc :=
    H.activeStage_eq_of_mem_slab_P6F3 i tt (by rw [htt]; exact ht1.le) (by rw [htt]; exact ht2)
  have haStt : aSeed ≤ tt := haS'.trans hat
  have httT : tt ≤ Tn := htσ.trans hsT
  obtain ⟨y', hy'⟩ := H.exists_heq_stageAt_P6JW he p'
  have hdy := hdy0 tt htt haStt httT y' hy'
  have htt' : (tt : ℝ) = t := htt
  have hgood' : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ tt),
      (tt : ℝ) - (L / 2) ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans httT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage tt) tt)
              (seedTrace.point (H.activeStage tt) (H.activeStage_mono haStt)
                (H.activeStage_mono httT)) y' +
            ENNReal.ofReal (L / 2 / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z := by
    intro w haw hwt hwL z hz hRz
    refine hgood w haw (hwt.trans htσ) (by linarith) z (hz.trans ?_) hRz
    exact (add_le_add hdy le_rfl).trans (le_of_eq (hsum _))
  have hTR : T / R ≤ (L / 2) ^ 2 / R := (div_le_div_iff_of_pos_right hR).2 hTL
  have haL : (tt : ℝ) - (L / 2) ^ 2 / R ≤ a := by linarith
  have hdepth : (tt : ℝ) - a ≤ T / R := by linarith
  have haS'' : (aSeed : ℝ) ≤ a := haS'
  have hRa' : 1 ≤ R * a := hRa.trans (mul_le_mul_of_nonneg_left haS'' hR.le)
  obtain ⟨zc, hzc⟩ := H.exists_heq_stage_P6JW he z'
  have hzball := hP zc hzc
  obtain ⟨-, hRzeq, hballeq⟩ := H.transport_at_stage_P6JW haT seedTrace haStt httT he htt z' zc
    hzc h1i h2c
  have hzy : z' ∈ riemannianBallOf (H.stageMetric (H.activeStage tt) tt) y'
      (ρb / Real.sqrt R) := by
    rw [hballeq y' p' hy' (ρb / Real.sqrt R), stageMetric_castSucc_apply]
    exact hzball
  have hz' : metricScalarAt (H.stageMetric (H.activeStage tt) tt) z' ≤ Cball * R := by
    rw [hRzeq, stageMetric_castSucc_apply]
    exact hbt zc hzball
  have hdfin : riemannianEDistOf (H.stageMetric (H.activeStage tt) tt)
      (seedTrace.point (H.activeStage tt) (H.activeStage_mono haStt) (H.activeStage_mono httT))
      y' ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.ofReal_ne_top⟩) hdy
  have httH : (tt : ℝ) < H.horizon := by
    have h1 : (tt : ℝ) < H.time i.succ := by rw [htt]; exact ht2
    have h2 : (σ : ℝ) ≤ H.horizon := σ.2.2
    linarith
  subst hKH
  have hgrid0 : ∀ (j : ℕ) (w : Icc (0 : ℝ) KH.toHistory.horizon) (haw : a ≤ w) (hwt : w ≤ tt),
      (w : ℝ) = tt - j * β / R →
      metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage w) w)
        (A.point (KH.toHistory.activeStage w) (KH.toHistory.activeStage_mono haw)
          (KH.toHistory.activeStage_mono hwt)) ≤ Qb * R := by
    intro j w haw hwt hw
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have hwtt : w = tt := Subtype.ext (by simpa using hw)
      subst hwtt
      have hpt : A.point (KH.toHistory.activeStage w) (KH.toHistory.activeStage_mono haw)
          (KH.toHistory.activeStage_mono hwt) = z' := A.endpoint_eq
      rw [hpt]
      have hCQ : Cball ≤ Qb := (le_max_left _ _).trans ((le_max_left _ _).trans hQb)
      exact hz'.trans (mul_le_mul_of_nonneg_right hCQ hR.le)
    · exact hgt tt htt htσ a haS' hat hlo z' hP A j hj w haw hwt (by rw [hw, htt'])
  have hQb' : max Cg 1 ≤ Qb := (max_le_max (le_max_right _ _) le_rfl).trans hQb
  have hQQ : max (max Qb Cg) 1 ≤ Qb :=
    max_le (max_le le_rfl ((le_max_right _ _).trans ((le_max_left _ _).trans hQb)))
      ((le_max_right _ _).trans hQb)
  have hscalC := hballT_grid_of_depthInduction_P6BB KH.toHistory haT seedTrace httT haStt y'
    (L / 2) hR (by linarith) hgood' hβ hβs hQQ haS' hat haL A hgrid0
  have hprotC := hprotC_scalC_CXJP KH haT hsmall hclock seedTrace httT haStt y' (L / 2) haS' hat A
    hscalC records hDm hnc (fun e he' b hlt => hscale e he' b (lt_of_le_of_lt (hTlo.trans hlo) hlt))
  have hres := hgoodV_scalC_CXJP hC2 KH haT hsmall hclock seedTrace ha₀ hpin httT haStt y' (L / 2)
    hR hgood' hQb' haS' hat (fun h => absurd h (ne_of_lt httH)) haL hdepth hRa' A hscalC hℓ hKℓ hℓr
    hKr hKC hℓρ hρL (hT₀.trans haS'') records hOld hcan (hacc.trans (min_le_right _ _)) hDm hprotC
    hzy hdfin hnum v hav hvt
  have hq : L / 2 / 2 / Real.sqrt R ≤ L / 2 / Real.sqrt R :=
    div_le_div_of_nonneg_right (by linarith) hsR.le
  exact hres.le.trans ((add_le_add hdy (ENNReal.ofReal_le_ofReal hq)).trans (le_of_eq (hsum _)))

/-- consumer。 -/
example : True := by
  have := hstopE_body_deep_fixT_R4K.{0}
  trivial

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
