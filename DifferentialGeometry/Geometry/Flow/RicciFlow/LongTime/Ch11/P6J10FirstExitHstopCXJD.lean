import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10FirstExitTraceCXJD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J10PreTraceCeilingCXJT0
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HclosFirstExit_P6L4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.HUVSlabGoodCg_P6LS3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.LocalPropagation_P6L

/-!
# 跨 slab `hstop` 的 first-exit producer（CX-J10DIST G3，后缀 `_CXJD`）

R-C11-16 D-2 T0 跨 slab 定位：给 `scalar_le_two_mul_stopped_ceiling_CXJT0` 的 `hstop`。
* `hRicC_of_hgood_ceiling_CXJD`：G2 的条件 Ricci 前提 `hRicC`。时刻 `t`（slab `e` 内部）、`[t, σ]` 上
  trace 在 Ω′（预算 `L/(2√R)`）内 ⇒
  (1) CXJT0 stopped ceiling（`hstop` 只在 `[t, σ]` 上）⇒ `R(t, A(t)) ≤ 2·Q_b·R`；
  (2) hgood 空间分量（`gradient_of_hgood_slab_Cg_P6LS3`，Ω 内 `R ≥ Cg·R` 处 `|∇R| ≤ C₂′R^{3/2}`）+
      局部传播 `scalar_le_on_ball_of_gradient_bound_P6L`（球 `2ρ/√(2Q_bR)` 由三角不等式落在 Ω 内）⇒
      `B_t(A(t), ρ/√(2Q_bR))` 上 `R ≤ 6·Q_b·R`；
  (3) `ricci_seed_or_scal_P6L4`（seed 端 K0、trace 端标量 + Hamilton–Ivey pinching）⇒
      两端 `ℓ`-球 Ricci 界。
  **只在 `[t, σ]` 上用 ceiling**，不假设整窗 ceiling——first-exit 的循环由 G1 打破。
* `hstop_of_firstExit_CXJD`：G2 + 上式 + 余量 `D/√R + (8/ℓ)(T/R) < L/(2√R)` ⇒ 整窗 `[a, σ]` 的 `hstop`
  （预算 `L/√R`）。
* `scalar_le_two_mul_crossSlab_ceiling_CXJD`（consumer，G4）：`hstop` 喂
  `scalar_le_two_mul_stopped_ceiling_CXJT0`
  ⇒ 跨 slab 沿 trace `R ≤ 2·Q_b·R`。
不出现 `qcap`；不以 traced region 为前提；crossing 比较只经树内 (D4)（RegularCrossing + no-shortcut）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem activeStage_eq_of_mem_CXJD3 (H : ObservedHistory.{u}) (e : Fin H.eventCount)
    (v : Icc (0 : ℝ) H.horizon) (h1 : H.time e.castSucc ≤ v) (h2 : (v : ℝ) < H.time e.succ) :
    H.activeStage v = e.castSucc :=
  (H.mem_stageDomain_iff v e.castSucc).mp (by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show (v : ℝ) ∈ Ico (H.time e.castSucc) (H.time e.succ) from ⟨h1, h2⟩))

/-- **G2 `hRicC` 的生产（`_CXJD`）**：hgood（时间 + 空间分量）+ CXJT0 stopped ceiling + 局部传播 +
K0 + pinching。 -/
theorem hRicC_of_hgood_ceiling_CXJD {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg Cball Qb T K ℓ : ℝ} (hC2 : 0 ≤ C2') (H : ObservedHistory.{u})
    {Tn aSeed a σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn) {pT : (H.stageAt Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (hσT : σ ≤ Tn) (has : aSeed ≤ σ) (y : (H.stageAt σ).Carrier) {R : ℝ} (L : ℝ) (hR : 0 < R)
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
    (hQb : max (max Cball Cg) 1 ≤ Qb) (hstep : 2 * Ctime' * Qb * T ≤ 1)
    (haS : aSeed ≤ a) (haσ : a ≤ σ) (hσlast : H.activeStage σ < Fin.last H.eventCount)
    (haL : (σ : ℝ) - L ^ 2 / R ≤ a) (hdepth : (σ : ℝ) - a ≤ T / R) (hRa : 1 ≤ R * a)
    {z : (H.stageAt σ).Carrier}
    (hz : metricScalarAt (H.stageMetric (H.activeStage σ) σ) z ≤ Cball * R)
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage σ) (H.activeStage_mono haσ) z)
    (hℓ : 0 < ℓ) (hKℓ : K * ℓ ^ 2 ≤ 1) (hℓr : ℓ ≤ r / 50) (hKr : 1 / r ^ 2 ≤ K)
    (hKC : 2 * Real.sqrt 3 * (6 * Qb / 2 + max (6 * Qb) (2 * Real.exp 4)) * R ≤ K)
    (hℓρ : ℓ ≤ localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))
    (hρL : 2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) ≤ L / 2 / Real.sqrt R) :
    ∀ (k : Fin (H.eventCount + 1)) (hka : H.activeStage a ≤ k)
        (hkσ : k ≤ H.activeStage σ) (t : ℝ), H.time k < t →
        (∀ e : Fin H.eventCount, k = e.castSucc → t < H.time e.succ) → (a : ℝ) < t → t < σ →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvσ : v ≤ σ), t ≤ (v : ℝ) →
          riemannianEDistOf (H.stageMetric (H.activeStage v) v)
              (seedTrace.point (H.activeStage v) (H.activeStage_mono (haS.trans hav))
                (H.activeStage_mono (hvσ.trans hσT)))
              (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvσ)) <
            riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
                (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                  (H.activeStage_mono hσT)) y +
              ENNReal.ofReal (L / 2 / Real.sqrt R)) →
        ∀ w : (H.stage k).Carrier, ∀ ξ : TangentSpace ThreeModel w,
          (riemannianEDistOf (H.stageMetric k t)
              (seedTrace.point k ((H.activeStage_mono haS).trans hka)
                (hkσ.trans (H.activeStage_mono hσT))) w < ENNReal.ofReal ℓ ∨
            riemannianEDistOf (H.stageMetric k t) (A.point k hka hkσ) w <
              ENNReal.ofReal ℓ) →
          ricciTensor (H.stageMetric k t) w ξ ξ ≤
            (3 / ℓ ^ 2) * (H.stageMetric k t).inner w ξ ξ := by
  intro k hka hkσ t hkt hnext hat htσ hgoodF w ξ hw
  obtain ⟨e, rfl⟩ := Fin.exists_castSucc_eq.mpr (ne_of_lt (hkσ.trans_lt hσlast))
  have hte := hnext e rfl
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
  -- 时刻 `t` 与 stage
  have ht0 : 0 ≤ t := a.2.1.trans hat.le
  let tI : Icc (0 : ℝ) H.horizon := ⟨t, ht0, htσ.le.trans σ.2.2⟩
  have hatI : a ≤ tI := hat.le
  have htIσ : tI ≤ σ := htσ.le
  have hact : H.activeStage tI = e.castSucc := activeStage_eq_of_mem_CXJD3 H e tI hkt.le hte
  have h1 : H.activeStage aSeed ≤ e.castSucc := (H.activeStage_mono haS).trans hka
  have h2 : e.castSucc ≤ H.activeStage Tn := hkσ.trans (H.activeStage_mono hσT)
  set dσ := riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
    (seedTrace.point (H.activeStage σ) (H.activeStage_mono has) (H.activeStage_mono hσT)) y
    with hdσ
  have hXle : dσ + ENNReal.ofReal (L / 2 / Real.sqrt R) ≤
      dσ + ENNReal.ofReal (L / Real.sqrt R) :=
    add_le_add le_rfl (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (by linarith) hsR.le))
  -- (1) stopped ceiling on `[t, σ]`
  let A' := A.restrictFirst (H.activeStage_mono hatI) (H.activeStage_mono htIσ)
  have hceil := scalar_le_two_mul_stopped_ceiling_CXJT0 H haT hσT has seedTrace y L hR hgood hQb
    hstep htIσ le_rfl (haS.trans hatI) (haL.trans hat.le) (by
      change (σ : ℝ) - t ≤ T / R
      linarith) hz A' (fun v hav hvt => (hgoodF v (hatI.trans hav) hvt hav).le.trans hXle)
  have hceilk : ∀ (m : Fin (H.eventCount + 1)) (hm : H.activeStage tI = m)
      (h3 : H.activeStage a ≤ m) (h4 : m ≤ H.activeStage σ),
      metricScalarAt (H.stageMetric m t) (A.point m h3 h4) ≤ 2 * (Qb * R) := by
    intro m hm h3 h4
    subst hm
    exact hceil tI le_rfl htIσ
  have hxR : (H.event e).incoming.flow.scalar t (A.point e.castSucc hka hkσ) ≤ 2 * (Qb * R) := by
    have h := hceilk e.castSucc hact hka hkσ
    rw [stageMetric_castSucc_apply] at h
    exact h
  -- trace 点在 `t` 的距离
  have hdk : ∀ (m : Fin (H.eventCount + 1)) (hm : H.activeStage tI = m)
      (h1 : H.activeStage aSeed ≤ m) (h2 : m ≤ H.activeStage Tn)
      (h3 : H.activeStage a ≤ m) (h4 : m ≤ H.activeStage σ),
      riemannianEDistOf (H.stageMetric m t) (seedTrace.point m h1 h2) (A.point m h3 h4) <
        dσ + ENNReal.ofReal (L / 2 / Real.sqrt R) := by
    intro m hm h1 h2 h3 h4
    subst hm
    exact hgoodF tI hatI htIσ le_rfl
  have hdx : riemannianEDistOf ((H.event e).incoming.flow.base.metric t)
      (seedTrace.point e.castSucc h1 h2) (A.point e.castSucc hka hkσ) <
      dσ + ENNReal.ofReal (L / 2 / Real.sqrt R) := by
    have h := hdk e.castSucc hact h1 h2 hka hkσ
    rw [stageMetric_castSucc_apply] at h
    exact h
  -- (2) 局部传播
  let U : Set (H.stage e.castSucc).Carrier := {w | riemannianEDistOf
    ((H.event e).incoming.flow.base.metric t) (seedTrace.point e.castSucc h1 h2) w ≤
      dσ + ENNReal.ofReal (L / Real.sqrt R)}
  have hU : riemannianBallOf ((H.event e).incoming.flow.base.metric t)
      (A.point e.castSucc hka hkσ)
      (2 * (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R)))) ⊆ U := by
    intro w hwb
    change riemannianEDistOf _ _ w ≤ _
    calc _ ≤ riemannianEDistOf ((H.event e).incoming.flow.base.metric t)
          (seedTrace.point e.castSucc h1 h2) (A.point e.castSucc hka hkσ) +
          riemannianEDistOf ((H.event e).incoming.flow.base.metric t)
            (A.point e.castSucc hka hkσ) w := riemannianEDistOf_triangle _ _ _ _
      _ ≤ (dσ + ENNReal.ofReal (L / 2 / Real.sqrt R)) +
          ENNReal.ofReal (L / 2 / Real.sqrt R) :=
          add_le_add hdx.le (hwb.le.trans (ENNReal.ofReal_le_ofReal hρL))
      _ = dσ + ENNReal.ofReal (L / Real.sqrt R) := by
          rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 2
          ring
  have hσL : (σ : ℝ) - L ^ 2 / R ≤ t := haL.trans hat.le
  have hball : ∀ w : (H.stage e.castSucc).Carrier, w ∈ riemannianClosedBallOf
      ((H.event e).incoming.flow.base.metric t) (A.point e.castSucc hka hkσ)
        (localPropagationRadius C2' / Real.sqrt (2 * (Qb * R))) →
      (H.event e).incoming.flow.scalar t w ≤ 3 * (2 * (Qb * R)) := fun w0 hw0 =>
    scalar_le_on_ball_of_gradient_bound_P6L (H.event e).incoming.flow hC2 hQ0 U hU
    (fun w hwU hw v => by
      have hRw : Cg * R ≤ (H.event e).incoming.flow.scalar t w := by linarith
      have hg := gradient_of_hgood_slab_Cg_P6LS3 (Ctime' := Ctime') hC2 H haT hσT has seedTrace y R
        L hgood e t hkt hte (show (aSeed : ℝ) ≤ t from (haS.trans hatI)) htσ.le hσL h1 h2 w hwU
        hRw v
      rw [Real.coe_toNNReal _ hC2] at hg
      have hpos : 0 ≤ (H.event e).incoming.flow.scalar t w := by linarith
      have hterm : 0 ≤ C2' * (H.event e).incoming.flow.scalar t w *
          Real.sqrt ((H.event e).incoming.flow.scalar t w) *
          Real.sqrt (((H.event e).incoming.flow.base.metric t).inner w v v) := by positivity
      have hring : 2 * C2' * ((H.event e).incoming.flow.scalar t w *
          Real.sqrt ((H.event e).incoming.flow.scalar t w)) *
          Real.sqrt (((H.event e).incoming.flow.base.metric t).inner w v v) =
          2 * (C2' * (H.event e).incoming.flow.scalar t w *
          Real.sqrt ((H.event e).incoming.flow.scalar t w) *
          Real.sqrt (((H.event e).incoming.flow.base.metric t).inner w v v)) := by ring
      rw [hring]
      linarith) hxR hw0
  -- (3) 端点 Ricci
  have hscal : ∀ w : (H.stage e.castSucc).Carrier,
      riemannianEDistOf ((H.event e).incoming.flow.base.metric t) (A.point e.castSucc hka hkσ) w <
        ENNReal.ofReal ℓ → (H.event e).incoming.flow.scalar t w ≤ 6 * Qb * R := by
    intro w hw'
    have h := hball w (hw'.le.trans (ENNReal.ofReal_le_ofReal hℓρ))
    linarith
  have hRt : 1 ≤ R * t := hRa.trans (mul_le_mul_of_nonneg_left hat.le hR.le)
  have hric := H.ricci_seed_or_scal_P6L4 haT hsmall hclock seedTrace ha₀ hpin e h1 h2
    (A.point e.castSucc hka hkσ) (Q := R) (C := 6 * Qb) hR hℓ hKℓ hℓr hKr (by linarith) hKC hkt hte
    (show (aSeed : ℝ) ≤ t from haS.trans hatI) (htσ.le.trans hσT) hRt hscal
  rw [stageMetric_castSucc_apply] at hw ⊢
  exact hric w ξ hw

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
