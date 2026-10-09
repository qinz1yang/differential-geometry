import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10TopCeilingCXJF2

/-!
# hextend 深度步 G1：抽象标量源的 first-exit 定位（CX-J10DEPTH，后缀 `_CXJP`）

CXJF2 G2/G3（`hRicC_top_of_hgood_ceiling_CXJF2` / `hprotC_top_of_ceiling_CXJF2` / `hstop_top_CXJF2`）的
"trace 点标量上界"抽象版：原文由 ceiling-from-σ（CXJT0 stopped ceiling，深度受 `2·Ctime′·Q_b·T ≤ 1` 限制）
给 `R(t′, A(t′)) ≤ 2·Q_b·R`；此处换成**条件**前提 `hscalC`（`[t′, σ]` 上 trace 在 Ω′ 内时
`R(t′, A(t′)) ≤ 2·Q_b·R`），其余（hgood 梯度局部传播、K0 + pinching 端点 Ricci、first-exit、(D4) 保护）逐字。
hextend 中 `hscalC` 由已有 traced region（`[a, t]`）+ anchor 出发的 ceiling ODE（`[w, a)`）给（G2）。
* `hRicC_scalC_CXJP` / `hprotC_scalC_CXJP` / `hgoodV_scalC_CXJP`（整窗严格定位）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem activeStage_eq_of_mem_CXJF2b (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    (v : Icc (0 : ℝ) H.horizon) (h1 : H.time e.castSucc ≤ v) (h2 : (v : ℝ) < H.time e.succ) :
    H.activeStage v = e.castSucc :=
  (H.mem_stageDomain_iff v e.castSucc).mp (by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show (v : ℝ) ∈ Ico (H.time e.castSucc) (H.time e.succ) from ⟨h1, h2⟩))

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

/-- **`hRicC`，trace 点标量由 `hscalC` 给（`_CXJP`）**：CXJF2 G2 的 ceiling-from-σ 换成条件形 `hscalC`。 -/
theorem hRicC_scalC_CXJP {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg Qb K ℓ : ℝ} (hC2 : 0 ≤ C2') (KH : RetainedCoreHistory.{u})
    {Tn aSeed a σ : Icc (0 : ℝ) KH.toHistory.horizon} (haT : aSeed ≤ Tn) {pT : (KH.toHistory.stageAt
      Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature KH.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage aSeed)
      (KH.toHistory.activeStage Tn)
      (KH.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) KH.toHistory.horizon) (x : (KH.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (KH.toHistory.stageMetric (KH.toHistory.activeStage t) t)
        (a₀ + t) x)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (KH.toHistory.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (hR : 0
      < R)
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
    (hQb : max Cg 1 ≤ Qb)
    (haS : aSeed ≤ a) (haσ : a ≤ σ) (haL : (σ : ℝ) - L ^ 2 / R ≤ a)
    (hRa : 1 ≤ R * a)
    {z : (KH.toHistory.stageAt σ).Carrier}
    (A : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage a) (KH.toHistory.activeStage σ)
      (KH.toHistory.activeStage_mono haσ) z)
    (hscalC : ∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : a ≤ v) (hvσ : v ≤ σ),
      (∀ (v' : Icc (0 : ℝ) KH.toHistory.horizon) (hav' : a ≤ v') (hv'σ : v' ≤ σ), (v : ℝ) ≤ v' →
        riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v') v')
            (seedTrace.point (KH.toHistory.activeStage v')
              (KH.toHistory.activeStage_mono (haS.trans hav'))
              (KH.toHistory.activeStage_mono (hv'σ.trans hσT)))
            (A.point (KH.toHistory.activeStage v') (KH.toHistory.activeStage_mono hav')
              (KH.toHistory.activeStage_mono hv'σ)) <
          riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
              (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
                (KH.toHistory.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / 2 / Real.sqrt R)) →
      metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
        (A.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
          (KH.toHistory.activeStage_mono hvσ)) ≤ 2 * (Qb * R))
    (hℓ : 0 < ℓ) (hKℓ : K * ℓ ^ 2 ≤ 1) (hℓr : ℓ ≤ r / 50) (hKr : 1 / r ^ 2 ≤ K)
    (hKC : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (hℓρ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (hρL : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R) :
    ∀ (k : Fin (KH.toHistory.eventCount + 1)) (hka : KH.toHistory.activeStage a ≤ k)
        (hkσ : k ≤ KH.toHistory.activeStage σ) (t : ℝ), KH.toHistory.time k < t →
        (∀ e : Fin KH.toHistory.eventCount, k = e.castSucc → t < KH.toHistory.time e.succ) → (a : ℝ)
          < t → t < σ →
        (∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : a ≤ v) (hvσ : v ≤ σ), t ≤ (v : ℝ) →
          riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
              (seedTrace.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono
                (haS.trans hav))
                (KH.toHistory.activeStage_mono (hvσ.trans hσT)))
              (A.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
                (KH.toHistory.activeStage_mono hvσ)) <
            riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
                (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
                  (KH.toHistory.activeStage_mono hσT)) y +
              ENNReal.ofReal (L / 2 / Real.sqrt R)) →
        ∀ w : (KH.toHistory.stage k).Carrier, ∀ ξ : TangentSpace ThreeModel w,
          (riemannianEDistOf (KH.toHistory.stageMetric k t)
              (seedTrace.point k ((KH.toHistory.activeStage_mono haS).trans hka)
                (hkσ.trans (KH.toHistory.activeStage_mono hσT))) w < ENNReal.ofReal ℓ ∨
            riemannianEDistOf (KH.toHistory.stageMetric k t) (A.point k hka hkσ) w <
              ENNReal.ofReal ℓ) →
          ricciTensor (KH.toHistory.stageMetric k t) w ξ ξ ≤
            (3 / ℓ ^ 2) * (KH.toHistory.stageMetric k t).inner w ξ ξ := by
  intro k hka hkσ t hkt hnext hat htσ hgoodF w ξ hw
  have hQ1 : 1 ≤ Qb := (le_max_right _ _).trans hQb
  have hCgQ : Cg ≤ Qb := (le_max_left _ _).trans hQb
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hQb0 : 0 < Qb := by linarith
  have hQR : 0 < Qb * R := mul_pos hQb0 hR
  have hQ0 : 0 < 2 * (Qb * R) := by linarith
  have hCgR : Cg * R ≤ Qb * R := mul_le_mul_of_nonneg_right hCgQ hR.le
  have hρ0 : 0 < localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)) :=
    div_pos (localPropagationRadius_pos hC2) (Real.sqrt_pos.2 hQ0)
  have hL0 : 0 ≤ L := by
    have h := hρ0.trans_le (le_of_lt (lt_of_lt_of_le (by linarith) hρL))
    have : 0 < L / 2 / Real.sqrt R := by linarith
    have h2 : 0 < L / 2 := by
      by_contra hn
      have : L / 2 / Real.sqrt R ≤ 0 := div_nonpos_of_nonpos_of_nonneg (not_lt.mp hn) hsR.le
      linarith
    linarith
  have ht0 : 0 ≤ t := a.2.1.trans hat.le
  let tI : Icc (0 : ℝ) KH.toHistory.horizon := ⟨t, ht0, htσ.le.trans σ.2.2⟩
  have hatI : a ≤ tI := hat.le
  have htIσ : tI ≤ σ := htσ.le
  have h1 : KH.toHistory.activeStage aSeed ≤ k := (KH.toHistory.activeStage_mono haS).trans hka
  have h2 : k ≤ KH.toHistory.activeStage Tn := hkσ.trans (KH.toHistory.activeStage_mono hσT)
  set dσ := riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
    (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
      (KH.toHistory.activeStage_mono hσT)) y
    with hdσ
  have hhalf : ENNReal.ofReal (L / 2 / Real.sqrt R) + ENNReal.ofReal (L / 2 / Real.sqrt R) =
      ENNReal.ofReal (L / Real.sqrt R) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  -- (1) stopped ceiling on `[t, σ]`（slab 无关）
  have hceil := hscalC tI hatI htIσ (fun v hav hvσ hv => hgoodF v hav hvσ hv)
  have hceilk : ∀ (m : Fin (KH.toHistory.eventCount + 1)) (hm : KH.toHistory.activeStage tI = m)
      (h3 : KH.toHistory.activeStage a ≤ m) (h4 : m ≤ KH.toHistory.activeStage σ),
      metricScalarAt (KH.toHistory.stageMetric m t) (A.point m h3 h4) ≤ 2 * (Qb * R) := by
    intro m hm h3 h4
    subst hm
    exact hceil
  have hdk : ∀ (m : Fin (KH.toHistory.eventCount + 1)) (hm : KH.toHistory.activeStage tI = m)
      (h1 : KH.toHistory.activeStage aSeed ≤ m) (h2 : m ≤ KH.toHistory.activeStage Tn)
      (h3 : KH.toHistory.activeStage a ≤ m) (h4 : m ≤ KH.toHistory.activeStage σ),
      riemannianEDistOf (KH.toHistory.stageMetric m t) (seedTrace.point m h1 h2) (A.point m h3 h4) <
        dσ + ENNReal.ofReal (L / 2 / Real.sqrt R) := by
    intro m hm h1 h2 h3 h4
    subst hm
    exact hgoodF tI hatI htIσ le_rfl
  have hσL : (σ : ℝ) - L ^ 2 / R ≤ t := haL.trans hat.le
  have hRt : 1 ≤ R * t := hRa.trans (mul_le_mul_of_nonneg_left hat.le hR.le)
  -- 三角不等式：`2ρ/√Q₀` 球落在 Ω 内（度量 `g` 抽象）
  have htri : ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold ThreeModel ∞ M] (g : SmoothRiemannianMetric ThreeModel M) (p x w : M),
      riemannianEDistOf g p x < dσ + ENNReal.ofReal (L / 2 / Real.sqrt R) →
      w ∈ riemannianBallOf g x (2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))) →
      riemannianEDistOf g p w ≤ dσ + ENNReal.ofReal (L / Real.sqrt R) := by
    intro M _ _ _ g p x w hpx hw
    calc _ ≤ riemannianEDistOf g p x + riemannianEDistOf g x w := riemannianEDistOf_triangle _ _ _ _
      _ ≤ (dσ + ENNReal.ofReal (L / 2 / Real.sqrt R)) + ENNReal.ofReal (L / 2 / Real.sqrt R) :=
          add_le_add hpx.le (hw.le.trans (ENNReal.ofReal_le_ofReal hρL))
      _ = dσ + ENNReal.ofReal (L / Real.sqrt R) := by rw [add_assoc, hhalf]
  have hgradle : ∀ (C s g : ℝ), 0 ≤ s → 0 ≤ g → C = C2' →
      ∀ d : ℝ, |d| ≤ C * s * Real.sqrt s * Real.sqrt g →
        |d| ≤ 2 * C2' * (s * Real.sqrt s) * Real.sqrt g := by
    intro C s g hs hg hC d hd
    subst hC
    have hterm : 0 ≤ C * s * Real.sqrt s * Real.sqrt g := by positivity
    nlinarith
  rcases Fin.eq_castSucc_or_eq_last k with ⟨e, rfl⟩ | rfl
  · -- event slab `e`
    have hte := hnext e rfl
    have hact : KH.toHistory.activeStage tI = e.castSucc :=
      activeStage_eq_of_mem_CXJF2b KH.toHistory e tI hkt.le hte
    have hxR : (KH.toHistory.event e).incoming.flow.scalar t (A.point e.castSucc hka hkσ) ≤
        2 * (Qb * R) := by
      have h := hceilk e.castSucc hact hka hkσ
      rw [stageMetric_castSucc_apply] at h
      exact h
    have hdx : riemannianEDistOf ((KH.toHistory.event e).incoming.flow.base.metric t)
        (seedTrace.point e.castSucc h1 h2) (A.point e.castSucc hka hkσ) <
        dσ + ENNReal.ofReal (L / 2 / Real.sqrt R) := by
      have h := hdk e.castSucc hact h1 h2 hka hkσ
      rw [stageMetric_castSucc_apply] at h
      exact h
    let U : Set (KH.toHistory.stage e.castSucc).Carrier := {w | riemannianEDistOf
      ((KH.toHistory.event e).incoming.flow.base.metric t) (seedTrace.point e.castSucc h1 h2) w ≤
        dσ + ENNReal.ofReal (L / Real.sqrt R)}
    have hU : riemannianBallOf ((KH.toHistory.event e).incoming.flow.base.metric t)
        (A.point e.castSucc hka hkσ)
        (2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))) ⊆ U :=
      fun w hwb => htri _ _ _ w hdx hwb
    have hball : ∀ w : (KH.toHistory.stage e.castSucc).Carrier, w ∈ riemannianClosedBallOf
        ((KH.toHistory.event e).incoming.flow.base.metric t) (A.point e.castSucc hka hkσ)
          (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) →
        (KH.toHistory.event e).incoming.flow.scalar t w ≤ 3 * (2 * (Qb * R)) := fun w0 hw0 =>
      scalar_le_on_ball_of_gradient_bound_P6L (KH.toHistory.event e).incoming.flow hC2 hQ0 U hU
      (fun w hwU hw v => by
        have hRw : Cg * R ≤ (KH.toHistory.event e).incoming.flow.scalar t w := by linarith
        have hg := gradient_of_hgood_slab_Cg_P6LS3 (Ctime' := Ctime') hC2 KH.toHistory haT hσT has
          seedTrace y R L hgood e t hkt hte (show (aSeed : ℝ) ≤ t from (haS.trans hatI)) htσ.le
          hσL h1 h2 w hwU hRw v
        exact hgradle _ _ _ (by linarith) (metric_inner_self_nonneg _ w v)
          (Real.coe_toNNReal _ hC2) _ hg) hxR hw0
    have hscal : ∀ w : (KH.toHistory.stage e.castSucc).Carrier,
        riemannianEDistOf ((KH.toHistory.event e).incoming.flow.base.metric t)
          (A.point e.castSucc hka hkσ) w < ENNReal.ofReal ℓ →
        (KH.toHistory.event e).incoming.flow.scalar t w ≤ 6 * Qb * R := by
      intro w hw'
      have h := hball w (hw'.le.trans (ENNReal.ofReal_le_ofReal hℓρ))
      linarith
    have hric := KH.toHistory.ricci_seed_or_scal_P6L4 haT hsmall hclock seedTrace ha₀ hpin e h1 h2
      (A.point e.castSucc hka hkσ) (Q := R) (C := 6 * Qb) hR hℓ hKℓ hℓr hKr (by linarith) hKC
      hkt hte (show (aSeed : ℝ) ≤ t from haS.trans hatI) (htσ.le.trans hσT) hRt hscal
    rw [stageMetric_castSucc_apply] at hw ⊢
    exact hric w ξ hw
  · -- final slab
    have hfin : KH.time (Fin.last KH.eventCount) < KH.horizon :=
      hkt.trans (htσ.trans_le σ.2.2)
    have hact : KH.toHistory.activeStage tI = Fin.last KH.toHistory.eventCount :=
      KH.toHistory.activeStage_eq_last_of_time_last_le tI hkt.le
    have hmet : ∀ τ : ℝ, KH.toHistory.stageMetric (Fin.last KH.toHistory.eventCount) τ =
        ((KH.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.base.metric τ :=
      fun τ => stageMetric_last_of_lt (h := hfin) τ
    have hxR : ((KH.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar t
        (A.point (Fin.last KH.toHistory.eventCount) hka hkσ) ≤ 2 * (Qb * R) := by
      have h := hceilk (Fin.last KH.toHistory.eventCount) hact hka hkσ
      rw [hmet] at h
      exact h
    have hdx : riemannianEDistOf
        (((KH.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.base.metric t)
        (seedTrace.point (Fin.last KH.toHistory.eventCount) h1 h2)
        (A.point (Fin.last KH.toHistory.eventCount) hka hkσ) <
        dσ + ENNReal.ofReal (L / 2 / Real.sqrt R) := by
      have h := hdk (Fin.last KH.toHistory.eventCount) hact h1 h2 hka hkσ
      rw [hmet] at h
      exact h
    let U : Set (KH.toHistory.stage (Fin.last KH.toHistory.eventCount)).Carrier :=
      {w | riemannianEDistOf
      (((KH.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.base.metric t)
        (seedTrace.point (Fin.last KH.toHistory.eventCount) h1 h2) w ≤
        dσ + ENNReal.ofReal (L / Real.sqrt R)}
    have hU : riemannianBallOf
        (((KH.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.base.metric t)
        (A.point (Fin.last KH.toHistory.eventCount) hka hkσ)
        (2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))) ⊆ U :=
      fun w hwb => htri _ _ _ w hdx hwb
    have hball : ∀ w : (KH.toHistory.stage (Fin.last KH.toHistory.eventCount)).Carrier,
        w ∈ riemannianClosedBallOf
        (((KH.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.base.metric t)
        (A.point (Fin.last KH.toHistory.eventCount) hka hkσ)
          (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) →
        ((KH.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar t w ≤
          3 * (2 * (Qb * R)) := fun w0 hw0 =>
      scalar_le_on_ball_of_gradient_bound_P6L
      ((KH.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow hC2 hQ0 U hU
      (fun w hwU hw v => by
        have hRw : Cg * R ≤
            ((KH.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar t w := by
          linarith
        have hg := RetainedCoreHistory.gradient_of_hgood_final_P6HF (Ctime' := Ctime') hC2 KH hfin
          haT hσT has
          seedTrace y R L hgood t hkt (show (aSeed : ℝ) ≤ t from (haS.trans hatI)) htσ.le
          hσL h1 h2 w hwU hRw v
        exact hgradle _ _ _ (by linarith) (metric_inner_self_nonneg _ w v)
          (Real.coe_toNNReal _ hC2) _ hg) hxR hw0
    have hscal : ∀ w : (KH.toHistory.stage (Fin.last KH.toHistory.eventCount)).Carrier,
        riemannianEDistOf (KH.toHistory.stageMetric (Fin.last KH.toHistory.eventCount) t)
          (A.point (Fin.last KH.toHistory.eventCount) hka hkσ) w < ENNReal.ofReal ℓ →
        metricScalarAt (KH.toHistory.stageMetric (Fin.last KH.toHistory.eventCount) t) w ≤
          6 * Qb * R := by
      intro w hw'
      rw [hmet] at hw' ⊢
      have h := hball w (hw'.le.trans (ENNReal.ofReal_le_ofReal hℓρ))
      change ((KH.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar t w ≤ _
      linarith
    exact KH.toHistory.ricci_seed_or_scal_final_P6M6 haT hsmall hclock seedTrace ha₀ hpin h1 h2
      (A.point (Fin.last KH.toHistory.eventCount) hka hkσ) (Q := R) (C := 6 * Qb) hR hℓ hKℓ hℓr hKr
      (by linarith) hKC hkt (show (aSeed : ℝ) ≤ t from haS.trans hatI) (htσ.le.trans hσT) hRt
      hscal w ξ hw

/-- **条件保护 `hprotC` 的生产（`_CXJF`）**：`[time e⁺, σ]` 上 Good ⇒ CXJT0 stopped ceiling 在 `time e⁺`
给 trace 点 `R_out ≤ 2·Q_b·R`；种子端 K0 `R ≤ 3/r²`；scale 分离 `2·max{3/r², 2Q_bR} < scale_b` ⇒ 两点都
`< scale_b/2` ⇒（`hnc`：树内 `exists_not_ageZeroCapPoint_of_scalar_lt_C11G` 的单 record 形）
不在 cap window 内区。 -/
theorem hprotC_scalC_CXJP
    {Qb : ℝ} (KH : RetainedCoreHistory.{u})
    {Tn aSeed a σ : Icc (0 : ℝ) KH.toHistory.horizon} (haT : aSeed ≤ Tn) {pT :
      (KH.toHistory.stageAt Tn).Carrier} {r : ℝ}
    (hsmall : GC.LongTime.hasSmallParabolicCurvature KH.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage aSeed)
      (KH.toHistory.activeStage Tn)
      (KH.toHistory.activeStage_mono haT) pT)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (KH.toHistory.stageAt σ).Carrier) {R : ℝ} (L : ℝ)
    (haS : aSeed ≤ a)
    (haσ : a ≤ σ)
    {z : (KH.toHistory.stageAt
      σ).Carrier}
    (A : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage a) (KH.toHistory.activeStage σ)
      (KH.toHistory.activeStage_mono haσ) z)
    (hscalC : ∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : a ≤ v) (hvσ : v ≤ σ),
      (∀ (v' : Icc (0 : ℝ) KH.toHistory.horizon) (hav' : a ≤ v') (hv'σ : v' ≤ σ), (v : ℝ) ≤ v' →
        riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v') v')
            (seedTrace.point (KH.toHistory.activeStage v')
              (KH.toHistory.activeStage_mono (haS.trans hav'))
              (KH.toHistory.activeStage_mono (hv'σ.trans hσT)))
            (A.point (KH.toHistory.activeStage v') (KH.toHistory.activeStage_mono hav')
              (KH.toHistory.activeStage_mono hv'σ)) <
          riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
              (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
                (KH.toHistory.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / 2 / Real.sqrt R)) →
      metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
        (A.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
          (KH.toHistory.activeStage_mono hvσ)) ≤ 2 * (Qb * R))
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
  have key : ∀ (m : Fin (KH.toHistory.eventCount + 1)) (hm : KH.toHistory.activeStage τI = m)
      (h3' : KH.toHistory.activeStage a ≤ m) (h4' : m ≤ KH.toHistory.activeStage σ),
      metricScalarAt (KH.toHistory.stageMetric m (KH.toHistory.time e.succ)) (A.point m h3' h4') ≤
        2 * (Qb * R) := by
    intro m hm h3' h4'
    subst hm
    exact hscalC τI haτI hτIσ (fun v hav hvσ hv => hgoodE v hav hvσ hv)
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


/-- **整窗严格定位（`_CXJP`）**：first-exit ⇒ `[a, σ]` 上 `d_v(seed, A(v)) < d_σ(O, y) + L/(2√R)`（预算 Ω′，
供 `hscalC` 的 Good 前提；CXJF2 `hstop_top` 的抽象标量、严格版）。 -/
theorem hgoodV_scalC_CXJP {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg Qb T K ℓ D : ℝ} (hC2 : 0 ≤ C2') (KH : RetainedCoreHistory.{u})
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
    (hQb : max Cg 1 ≤ Qb)
    (haS : aSeed ≤ a) (haσ : a ≤ σ) 
    (hUSCtop : (σ : ℝ) = KH.toHistory.horizon →
      ∀ (hfT : KH.toHistory.time (Fin.last KH.toHistory.eventCount) < KH.toHistory.horizon)
      (p q : (KH.toHistory.stage (Fin.last KH.toHistory.eventCount)).Carrier) (X' : ℝ≥0∞),
      riemannianEDistOf ((KH.toHistory.finalSlab hfT).flow.base.metric σ) p q < X' →
      ∃ s₁ : ℝ, s₁ < σ ∧ ∀ s' ∈ Icc s₁ (σ : ℝ),
        riemannianEDistOf ((KH.toHistory.finalSlab hfT).flow.base.metric s') p q < X')
    (haL : (σ : ℝ) - L ^ 2 / R ≤ a) (hdepth : (σ : ℝ) - a ≤ T / R) (hRa : 1 ≤ R * a)
    {z : (KH.toHistory.stageAt σ).Carrier}
    (A : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage a) (KH.toHistory.activeStage σ)
      (KH.toHistory.activeStage_mono haσ) z)
    (hscalC : ∀ (v : Icc (0 : ℝ) KH.toHistory.horizon) (hav : a ≤ v) (hvσ : v ≤ σ),
      (∀ (v' : Icc (0 : ℝ) KH.toHistory.horizon) (hav' : a ≤ v') (hv'σ : v' ≤ σ), (v : ℝ) ≤ v' →
        riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage v') v')
            (seedTrace.point (KH.toHistory.activeStage v')
              (KH.toHistory.activeStage_mono (haS.trans hav'))
              (KH.toHistory.activeStage_mono (hv'σ.trans hσT)))
            (A.point (KH.toHistory.activeStage v') (KH.toHistory.activeStage_mono hav')
              (KH.toHistory.activeStage_mono hv'σ)) <
          riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
              (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
                (KH.toHistory.activeStage_mono hσT)) y +
            ENNReal.ofReal (L / 2 / Real.sqrt R)) →
      metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage v) v)
        (A.point (KH.toHistory.activeStage v) (KH.toHistory.activeStage_mono hav)
          (KH.toHistory.activeStage_mono hvσ)) ≤ 2 * (Qb * R))
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
            (KH.toHistory.activeStage_mono hvt)) <
        riemannianEDistOf (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ)
            (seedTrace.point (KH.toHistory.activeStage σ) (KH.toHistory.activeStage_mono has)
              (KH.toHistory.activeStage_mono hσT)) y +
          ENNReal.ofReal (L / 2 / Real.sqrt R) := by
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
  have hfe := KH.toHistory.edist_trace_le_of_firstExit_top_CXJF2 haT seedTrace haS haσ hσT A
    hUSCtop hℓ
    hT₀ records
    hOld hcan hacc hDm hprotC (hRicC_scalC_CXJP hC2 KH haT hsmall hclock seedTrace
      ha₀
      hpin hσT has y L hR hgood hQb haS haσ haL hRa A hscalC hℓ hKℓ hℓr hKr hKC hℓρ
      hρL) hmargin
  intro v hav hvt
  have hv := hfe v hav hvt
  have hdv : 8 / ℓ * ((σ : ℝ) - v) ≤ 8 / ℓ * ((σ : ℝ) - a) :=
    mul_le_mul_of_nonneg_left (by linarith [show (a : ℝ) ≤ v from hav]) h8
  exact lt_of_le_of_lt (hv.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hdv))) hmargin


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
