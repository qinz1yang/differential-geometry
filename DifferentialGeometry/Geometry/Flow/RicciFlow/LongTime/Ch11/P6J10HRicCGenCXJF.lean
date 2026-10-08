import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10FirstExitTraceGenCXJF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10CrossSlabProtCXJD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FirstExitFinalP6M6
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HUVFinalP6HF

/-!
# final slab 覆盖：条件 Ricci `hRicC` 的通用生产（CX-J10FIN G2，后缀 `_CXJF`）

CXJD G3 `hRicC_of_hgood_ceiling_CXJD` 的 event / final 通用版（`activeStage σ < last` 换成 `σ < horizon`）。
`k = e⁻` 支同 CXJD；`k = Fin.last` 支用 final 孪生：梯度
`RetainedCoreHistory.gradient_of_hgood_final_P6HF`（hgood 空间分量，
final slab）、局部传播在 `(finalSlab).restrictIncoming` 的 flow 上、端点 Ricci `ricci_seed_or_scal_final_P6M6`。
时间导数仍只取 hgood 的时间分量（CXJT0 stopped ceiling，slab 无关）——**不用** horizon cap 阈值、
也不用 time-last 阈值，故无"由 horizon 阈值单调推 time-last 阈值"。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem activeStage_eq_of_mem_CXJF2 (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    (v : Icc (0 : ℝ) H.horizon) (h1 : H.time e.castSucc ≤ v) (h2 : (v : ℝ) < H.time e.succ) :
    H.activeStage v = e.castSucc :=
  (H.mem_stageDomain_iff v e.castSucc).mp (by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show (v : ℝ) ∈ Ico (H.time e.castSucc) (H.time e.succ) from ⟨h1, h2⟩))

/-- **`hRicC` 的通用生产（`_CXJF`）**：event slab 支同 CXJD G3；final slab 支用 final 孪生。 -/
theorem hRicC_gen_of_hgood_ceiling_CXJF {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg Cball Qb T K ℓ : ℝ} (hC2 : 0 ≤ C2') (KH : RetainedCoreHistory.{u})
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
    (hQb : max (max Cball Cg) 1 ≤ Qb) (hstep : 2 * Ctime' * Qb * T ≤ 1)
    (haS : aSeed ≤ a) (haσ : a ≤ σ) (hσH : (σ : ℝ) < KH.toHistory.horizon)
    (haL : (σ : ℝ) - L ^ 2 / R ≤ a) (hdepth : (σ : ℝ) - a ≤ T / R) (hRa : 1 ≤ R * a)
    {z : (KH.toHistory.stageAt σ).Carrier}
    (hz : metricScalarAt (KH.toHistory.stageMetric (KH.toHistory.activeStage σ) σ) z ≤ Cball * R)
    (A : BackwardPointTrace KH.toHistory (KH.toHistory.activeStage a) (KH.toHistory.activeStage σ)
      (KH.toHistory.activeStage_mono haσ) z)
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
  have hCgQ : Cg ≤ Qb := ((le_max_right _ _).trans (le_max_left _ _)).trans hQb
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
  have hXle : dσ + ENNReal.ofReal (L / 2 / Real.sqrt R) ≤
      dσ + ENNReal.ofReal (L / Real.sqrt R) :=
    add_le_add le_rfl (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (by linarith) hsR.le))
  have hhalf : ENNReal.ofReal (L / 2 / Real.sqrt R) + ENNReal.ofReal (L / 2 / Real.sqrt R) =
      ENNReal.ofReal (L / Real.sqrt R) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  -- (1) stopped ceiling on `[t, σ]`（slab 无关）
  let A' := A.restrictFirst (KH.toHistory.activeStage_mono hatI)
    (KH.toHistory.activeStage_mono htIσ)
  have hceil := scalar_le_two_mul_stopped_ceiling_CXJT0 KH.toHistory haT hσT has seedTrace y L hR
    hgood hQb
    hstep htIσ le_rfl (haS.trans hatI) (haL.trans hat.le) (by
      change (σ : ℝ) - t ≤ T / R
      linarith) hz A' (fun v hav hvt => (hgoodF v (hatI.trans hav) hvt hav).le.trans hXle)
  have hceilk : ∀ (m : Fin (KH.toHistory.eventCount + 1)) (hm : KH.toHistory.activeStage tI = m)
      (h3 : KH.toHistory.activeStage a ≤ m) (h4 : m ≤ KH.toHistory.activeStage σ),
      metricScalarAt (KH.toHistory.stageMetric m t) (A.point m h3 h4) ≤ 2 * (Qb * R) := by
    intro m hm h3 h4
    subst hm
    exact hceil tI le_rfl htIσ
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
      activeStage_eq_of_mem_CXJF2 KH.toHistory e tI hkt.le hte
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
      hkt.trans (htσ.trans hσH)
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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
