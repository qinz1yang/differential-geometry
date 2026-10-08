import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BCDBootstrapTowerP6BB

/-!
# BCDBOOT stay 链窗口孪生：hscale 窗 `σ − 2T/R`（driver hsepWK 形）+ 端点有限 ∀ᶠ（O-CH11-DISTLAWIRE G4a）

* `ObservedHistory.hstopE_body_deep_win_DLW`：`hstopE_body_deep_P6BB` 逐字，只把 hscale 窗
  `aSeed < time e⁺` 收窄为 `σ − 2T/R < time e⁺`（原证明只在 event `i`（time = σ）与
  `a ≥ t − T/R`、`t > σ − T/R` 之后的事件处用它；后者由 `∀ᶠ t` 里多取一个 `Ioo` 付）。
* `hstopE_deep_tower_win_DLW`：`hstopE_deep_tower_P6BB` 逐字，`hfamT` 体去掉 `∀ k, d_σ ≠ ⊤` 与
  `WindowNeckScaleBudget_P6HS`，换成同一 records 上的 hsepWK 窗形（`∀ i, σ = time i⁺ → ∀ T C, ∀ᶠ k,
  σ − T/R < time e⁺ → 2·max(3/(1/100)², C·R) < scale`，= driver `hsepWK` 逐字形）；端点有限改为结论里
  的 `∀ᶠ k` 前提。hscale 由该窗形在 `(2T, 2Q)` 处付，`3/1² ≤ 3/(1/100)²`。
无新 def / Prop。生成器 `build-logs/scratch/DLW/gen/gen_g4a.py`（源文本逐字 + 断言替换）。
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


universe u

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

/-- **G4a body 孪生（`_DLW`）**：hscale 窗 `σ − 2T/R < time e⁺`，其余逐字。 -/
theorem hstopE_body_deep_win_DLW :
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
    (_ : R = metricScalarAt (H.stageMetric (H.activeStage σ) σ) y)
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
    (_ : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b,
      (σ : ℝ) - 2 * T / R < H.time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale)
    (_ : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
        (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
          (H.activeStage_mono hsT)) y ≠ ⊤)
    (i : Fin H.eventCount) (_ : (σ : ℝ) = H.time i.succ)
    (p' : (H.stage i.castSucc).Carrier) (q' : (H.stage i.succ).Carrier) (_ : HEq y q')
    (_ : (H.event i).RegularCrossing p' q')
    (_ : ∀ᶠ t in 𝓝[<] H.time i.succ,
      ∀ z ∈ riemannianBallOf ((H.event i).incoming.flow.base.metric t) p' (ρb / Real.sqrt R),
        metricScalarAt ((H.event i).incoming.flow.base.metric t) z ≤ Cball * R)
    (_ : ∀ᶠ t in 𝓝[<] H.time i.succ,
      ∀ (tt : Icc (0 : ℝ) H.horizon), (tt : ℝ) = t → tt ≤ σ →
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
    ∀ᶠ t in 𝓝[<] H.time i.succ,
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
    seedTrace
    a₀ ha₀ hpin hsT has y R L hR hgood hQb hβ hβs hT hTL hL hRa haσ hRy hℓ hKℓ hℓr hKr hKC hℓρ hρL
    hnum q T₀ hT₀ records hOld hcan hDm hacc hm hscale hfin i hσi p' q' hyq hcross hball hgrid
  have hnc : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) (w : (H.stage e.succ).Carrier),
      (∀ b, metricScalarAt (H.event e).outputMetric w < ((records e he).static b).neck.scale / 2) →
      ¬ ∃ (b : (H.event e).RetainedBoundaryIndex) (x : standardCapWindow q.modelRadius),
        w = ((records e he).static b).window x ∧ ‖x.val‖ < q.modelRadius := by
    intro e he w hw
    have h := hnc0 (records e he) (hacc.trans (min_le_left _ _)) hm (hcan e he)
      (Dcap := q.modelRadius - 1) (by linarith) w hw
    simpa only [sub_add_cancel] using h
  have hprot : ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) (w : (H.stage e.succ).Carrier),
      (∀ b, metricScalarAt (H.event e).outputMetric w < ((records e he).static b).neck.scale / 2) →
      ∀ b, w ∉ ((records e he).static b).window ''
        {x : standardCapWindow q.modelRadius | ‖x.val‖ ≤ StandardCap.transitionEnd + 10} := by
    intro e he w hw b hmem
    obtain ⟨x, hx, hzx⟩ := hmem
    have hx' : ‖x.val‖ ≤ StandardCap.transitionEnd + 10 := hx
    exact hnc e he w hw ⟨b, x, hzx.symm, by linarith⟩
  -- σ = time i⁺
  have hσact : H.activeStage σ = i.succ := by
    refine le_antisymm ?_ (H.le_activeStage σ i.succ (le_of_eq hσi.symm))
    by_contra hlt
    have h1 := H.time_strictMono (not_le.mp hlt)
    have h2 := H.activeStage_time_le σ
    have h3 : (σ : ℝ) = σ.1 := rfl
    linarith
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
  have h1s : H.activeStage aSeed ≤ i.succ := h1i.trans i.castSucc_lt_succ.le
  have h2c : i.castSucc ≤ H.activeStage Tn := i.castSucc_lt_succ.le.trans h2i
  have hiT₀ : T₀ ≤ H.time i.succ := by linarith
  have hQ1 : 1 ≤ Qb := (le_max_right _ _).trans hQb
  have hscI := fun b => hscale i hiT₀ b (by
    have : 0 < 2 * T / R := by positivity
    linarith)
  -- 两点保护
  have hseedS := H.seed_scalar_le_of_smallParabolic_C11G haT hsmall hclock seedTrace σ has hsT
    i.succ hσact h1s h2i
  have hseedO : metricScalarAt (H.event i).outputMetric (seedTrace.point i.succ h1s h2i) ≤
      3 / r ^ 2 := by
    rw [← H.stageMetric_succ_time_C11G i, ← hσi]
    exact hseedS
  obtain ⟨hdσ_eq, hRσ_eq, -⟩ := H.transport_at_stage_P6JW haT seedTrace has hsT hσact hσi y q'
    hyq h1s h2i
  have hqS : metricScalarAt (H.event i).outputMetric q' = R := by
    rw [← H.stageMetric_succ_time_C11G i, ← hRσ_eq, hRy]
  have hpprot := hprot i hiT₀ (seedTrace.point i.succ h1s h2i) (fun b => by
    have := hscI b
    have hm1 : 3 / r ^ 2 ≤ max (3 / r ^ 2) (2 * (Qb * R)) := le_max_left _ _
    linarith)
  have hqprot := hprot i hiT₀ q' (fun b => by
    rw [hqS]
    have := hscI b
    have hm2 : 2 * (Qb * R) ≤ max (3 / r ^ 2) (2 * (Qb * R)) := le_max_right _ _
    nlinarith [mul_nonneg (sub_nonneg.2 hQ1) hR.le])
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
  have hshift := H.surgery_no_shortcut_C11D i (records i hiT₀).static (hOld i hiT₀) (hcan i hiT₀)
    (hacc.trans (min_le_right _ _)) hDm (seedTrace.crossing i h1i h2i) hcross hpprot hqprot hδ
  have hcs : H.time i.castSucc < H.time i.succ := H.time_strictMono Fin.castSucc_lt_succ
  have hLR : 0 < L ^ 2 / R := div_pos (pow_pos hLpos 2) hR
  have hq4 : (L / 2) ^ 2 / R = 1 / 4 * (L ^ 2 / R) := by ring
  filter_upwards [hshift, hball, hgrid, Ioo_mem_nhdsLT (show max (H.time i.castSucc)
      ((σ : ℝ) - 3 / 4 * (L ^ 2 / R)) < H.time i.succ from max_lt hcs (by linarith)),
    Ioo_mem_nhdsLT (show (σ : ℝ) - T / R < H.time i.succ by
      have := div_pos hT hR
      linarith)]
    with t hsh hbt hgt hti hti'
  intro tt htt htσ a haS' hat hlo z' hP A v hav hvt
  have ht1 : H.time i.castSucc < t := lt_of_le_of_lt (le_max_left _ _) hti.1
  have ht2 : (σ : ℝ) - 3 / 4 * (L ^ 2 / R) < t := lt_of_le_of_lt (le_max_right _ _) hti.1
  have he : H.activeStage tt = i.castSucc :=
    H.activeStage_eq_of_mem_slab_P6F3 i tt (by rw [htt]; exact ht1.le) (by rw [htt]; exact hti.2)
  have haStt : aSeed ≤ tt := haS'.trans hat
  have httT : tt ≤ Tn := htσ.trans hsT
  obtain ⟨y', hy'⟩ := H.exists_heq_stageAt_P6JW he p'
  obtain ⟨hdtt, -, hballT⟩ := H.transport_at_stage_P6JW haT seedTrace haStt httT he htt y' p' hy'
    h1i h2c
  have hdy : riemannianEDistOf (H.stageMetric (H.activeStage tt) tt)
        (seedTrace.point (H.activeStage tt) (H.activeStage_mono haStt) (H.activeStage_mono httT))
        y' ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has) (H.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / 2 / Real.sqrt R) := by
    rw [hdtt, hdσ_eq]
    exact hsh
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
    have h1 : (tt : ℝ) < H.time i.succ := by rw [htt]; exact hti.2
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
    hscalC records hDm hnc (fun e he' b hlt => hscale e he' b (by
      have e2 : 2 * T / R = T / R + T / R := by ring
      linarith [hti'.1]))
  have hres := hgoodV_scalC_CXJP hC2 KH haT hsmall hclock seedTrace ha₀ hpin httT haStt y' (L / 2)
    hR hgood' hQb' haS' hat (fun h => absurd h (ne_of_lt httH)) haL hdepth hRa' A hscalC hℓ hKℓ hℓr
    hKr hKC hℓρ hρL (hT₀.trans haS'') records hOld hcan (hacc.trans (min_le_right _ _)) hDm hprotC
    hzy hdfin hnum v hav hvt
  have hq : L / 2 / 2 / Real.sqrt R ≤ L / 2 / Real.sqrt R :=
    div_le_div_of_nonneg_right (by linarith) hsR.le
  exact hres.le.trans ((add_le_add hdy (ENNReal.ofReal_le_ofReal hq)).trans (le_of_eq (hsum _)))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-- **G4a tower 孪生（`_DLW`，PROVISIONAL[`hfamT` 窗形, `hballT`, `hgridT`]）**：`hfamT` 去 hfin / budget，
换 hsepWK 窗形；端点有限为结论 `∀ᶠ k` 前提。 -/
theorem hstopE_deep_tower_win_DLW :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {Cball : ℝ → ℝ} {qp : CutoffParameters}
      {Cgrid β : ℝ → ℝ → ℝ},
    0 ≤ C2 → StandardCap.transitionEnd + 10 < qp.modelRadius → qp.modelAccuracy ≤ ε₀ →
    2 ≤ qp.modelOrder → Tendsto qp.delta atTop (𝓝 0) →
    (∀ r T, 0 < β r T) →
    (∀ r T, 2 * (Ctime : ℝ) * max (max (max (Cball r) (Cgrid r T)) 4) 1 * β r T ≤ 1) →
    (
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∃ (a₀ T₀ : ℕ → ℝ) (records : ∀ k (e : Fin (Kh k).eventCount),
            T₀ k ≤ (Kh k).time e.succ →
              GeometricCutoffRecord (Kh k) e (qp.rescale_P6N (c k) (hc k))),
          (∀ k, 0 ≤ a₀ k) ∧
          (∀ k (τ : Icc (0 : ℝ) (Kh k).horizon) (x : ((Kh k).stageAt τ).Carrier),
            InFixedHamiltonIveyRegion ((Kh k).stageMetric ((Kh k).activeStage τ) τ)
              (a₀ k + τ) x) ∧
          (∀ k, T₀ k ≤ (aSeed k : ℝ)) ∧
          (∀ k (e : Fin (Kh k).eventCount), T₀ k ≤ (Kh k).time e.succ →
            ((Kh k).event e).old = ((Kh k).event e).transition.trace.retainedCore) ∧
          (∀ k (e : Fin (Kh k).eventCount) (he : T₀ k ≤ (Kh k).time e.succ) b,
            ((records k e he).static b).hasCanonicalWindow) ∧
          ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
          ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ k in atTop,
            ∀ (e : Fin (Kh k).eventCount) (he : T₀ k ≤ (Kh k).time e.succ) b,
              (σ k : ℝ) - T / R k < (Kh k).time e.succ →
              2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R k) <
                ((records k e he).static b).neck.scale
    ) →
    (
      ∀ r : ℝ, 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
              metricScalarAt (((Kh k).event (i k)).incoming.flow.base.metric t) z ≤
                Cball r * R k
    ) →
    (
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ (tt : Icc (0 : ℝ) (Kh k).horizon), (tt : ℝ) = t → tt ≤ σ k →
            ∀ (a : Icc (0 : ℝ) (Kh k).horizon), aSeed k ≤ a → ∀ (hat : a ≤ tt),
              t - T / R k ≤ (a : ℝ) →
            ∀ z' : ((Kh k).stageAt tt).Carrier,
              (∀ z : ((Kh k).stage (i k).castSucc).Carrier, HEq z' z →
                z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k))) →
            ∀ (A : BackwardPointTrace (Kh k) ((Kh k).activeStage a) ((Kh k).activeStage tt)
                ((Kh k).activeStage_mono hat) z')
              (j : ℕ), 1 ≤ j → ∀ (w : Icc (0 : ℝ) (Kh k).horizon) (haw : a ≤ w) (hwt : w ≤ tt),
              (w : ℝ) = t - j * β r T / R k →
              metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage w) w)
                  (A.point ((Kh k).activeStage w) ((Kh k).activeStage_mono haw)
                    ((Kh k).activeStage_mono hwt)) ≤
                Cgrid r T * R k
    ) →
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        (∀ᶠ k in atTop, riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) ≠ ⊤) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ (tt : Icc (0 : ℝ) (Kh k).horizon), (tt : ℝ) = t → ∀ (htσ : tt ≤ σ k)
              (a : Icc (0 : ℝ) (Kh k).horizon) (haS' : aSeed k ≤ a) (hat : a ≤ tt),
              t - T / R k ≤ (a : ℝ) →
            ∀ z' : ((Kh k).stageAt tt).Carrier,
              (∀ z : ((Kh k).stage (i k).castSucc).Carrier, HEq z' z →
                z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k))) →
            ∀ (A : BackwardPointTrace (Kh k) ((Kh k).activeStage a) ((Kh k).activeStage tt)
                ((Kh k).activeStage_mono hat) z')
              (v : Icc (0 : ℝ) (Kh k).horizon) (hav : a ≤ v) (hvt : v ≤ tt),
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v)
                    ((Kh k).activeStage_mono (haS'.trans hav))
                    ((Kh k).activeStage_mono ((hvt.trans htσ).trans (hsT k))))
                  (A.point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono hvt)) ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) := by
  obtain ⟨ε₀, hε₀, hG4⟩ := ObservedHistory.hstopE_body_deep_win_DLW.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F ε C1 C2 Ctime Cball qp Cgrid β hC2 hDm hacc hm hδlim hβ hβs hfamT hballT hgridT T r hT
    hr
    ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL
    hsel hgood haS hTnS hroom hradii i hi hfinE
  obtain ⟨a₀, T₀, records, ha₀, hpin, hT₀, hOld, hcan, hW⟩ := hfamT ind c hc Tn pT hTc
    aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL hsel hgood haS hTnS
    hroom hradii
  have hball := hballT r hr ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has
    L hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hgrid := hgridT T r hT hr ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT
    has L hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hQ1 : (1 : ℝ) ≤ max (max (max (Cball r) (Cgrid r T)) 4) 1 := le_max_right _ _
  have hQB : max (max (Cball r) 4) 1 ≤ max (max (max (Cball r) (Cgrid r T)) 4) 1 :=
    max_le_max (max_le_max (le_max_left _ _) le_rfl) le_rfl
  have hCG : Cgrid r T ≤ max (max (max (Cball r) (Cgrid r T)) 4) 1 :=
    (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hsc := hW i hi (2 * T) (by linarith) (2 * max (max (max (Cball r) (Cgrid r T)) 4) 1)
    (by positivity)
  obtain ⟨cn, hcn, hnumF⟩ := crossSlab_numerics_P6JW (C2' := C2) hC2 hQ1 one_pos
  filter_upwards [hsc, hfinE, hball, hgrid,
    haS T hT, hL.eventually_ge_atTop (4 * (r + 8 * T / cn) + 1),
    hL.eventually_ge_atTop
      (8 * (localPropagationRadius C2 / Real.sqrt (2 * max (max (max (Cball r) (Cgrid r T)) 4) 1))),
    hL.eventually_ge_atTop (2 * T + 2)] with k hsck hfk hbk hgk haSk hL1 hL2 hL3
  intro p' q hq hcross
  have hRk := hRpos k
  have hR1 : (1 : ℝ) ≤ R k := by
    have h := hRr k
    have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  obtain ⟨ℓ, K, hℓ, hKℓ, hℓr, hKr, hKC, hℓρ, hρL, hnum⟩ :=
    hnumF (R := R k) (L := L k / 2) (D := r) (T := T) hR1 (by linarith) (by linarith)
  have hh : T + 1 ≤ L k / 2 := by linarith
  have hTL : T ≤ (L k / 2) ^ 2 := by nlinarith [mul_le_mul hh hh (by linarith) (by linarith)]
  have hL0 : 0 ≤ L k := by linarith
  have haσ : (aSeed k : ℝ) < σ k := by
    have h := div_pos hT hRk
    linarith
  have hRa : 1 ≤ R k * aSeed k := by nlinarith [hone k]
  exact hG4 (Cg := 4) (Cball := Cball r) (Qb := max (max (max (Cball r) (Cgrid r T)) 4) 1)
    (ρb := r) hC2
    ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)) (Kh k) rfl
    (haT k) (hsm k) (hclock k) (seedTrace k) (ha₀ k) (hpin k) (hsT k) (has k) (y k) (L k) hRk
    (hgood k) hQB (hβ r T) (hβs r T) hT hTL hL0 hRa haσ (hRdef k) hℓ hKℓ hℓr hKr hKC hℓρ hρL hnum
    (hT₀ k) (records k) (hOld k) (hcan k) hDm hacc hm
    (fun e he b hlt => lt_of_le_of_lt (mul_le_mul_of_nonneg_left (max_le_max (by norm_num)
      (le_of_eq (by ring))) (by norm_num)) (hsck e he b hlt)) hfk (i k) (hi k) p' q hq hcross
    (hbk p' q hq hcross) ((hgk p' q hq hcross).mono fun t ht tt h1 h2 a h3 hat h4 z' hP A j hj w
      haw hwt hw => (ht tt h1 h2 a h3 hat h4 z' hP A j hj w haw hwt hw).trans
        (mul_le_mul_of_nonneg_right hCG hRk.le))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
