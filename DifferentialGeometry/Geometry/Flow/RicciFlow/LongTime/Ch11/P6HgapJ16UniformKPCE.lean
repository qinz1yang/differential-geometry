import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HscalCrossEventP6E

/-!
# hgap J16（含跨 event）⇐ 半径一致 traced 曲率 `huni`：缺口见证（O-CH11-P6CE 续 PCE，后缀 `_PCE`）

**状态：GAP-WITNESS（BLOCKED[一致 K = 新上游义务]）**，不进主链、不登记 binder。
* P6M2 `hcross` 已由 `hscal_crossEvent_of_traced_P6E`（P6HscalCrossEventP6E）付；J16 跨 event 部分里
  "w 不是 trace 点" 也由 P6CE G1 `survives_of_traced_ball_P6E` 处理（对任意 stage `j ≤ activeStage σ`，
  `j = activeStage σ` 即同 slab），故同 slab / 跨 event 用同一个证明。
* `scalar_le_of_twoStep_survival_PCE`（单 history）：G1 用两次——`v` 时刻 `x` 离 `tr.point j` 不足 `ℓ₁`
  ⇒ `x` = 某 `x′ ∈ B_σ(y, r + e^{9Kθ}ℓ₁)` 的 trace 点；`τ` 时刻 `z` 离 `x` 不足 `ℓ₂` ⇒ `|Rm(τ, z)| ≤ K`
  ⇒ `R(τ, z) ≤ 9K`。覆盖条件 `r + e^{9Kθ}(ℓ₁ + ℓ₂) ≤ ρ`。
* **`j16_of_uniformK_PCE`**：KT2c `hOpenJ` / `hOpen8J` 的 J16 合取逐字 ⇐ 内联 `huni`
  （= `P6HclosCCondP6HC` 的 `huni` 逐字：每个深度 `θ` 一个与半径 `A` 无关的 `K`）。取
  `θb := max B 0 − σ₁ + 1`、`ρb := Dw + e^{9Kθb}(Dd + max Rad 0) + e^{9Kθb}`、`C := max (9K) 1`。
  J16 的两个 footprint 前提不用。
**为何不由 `hDext` 付**：`DepthExtendable` 是 `∀ A ∃ K`（`K` 随半径变），而 J16 的 `Dw, Dd, Rad` 不可收小，
覆盖条件 `Dw + e^{9K(ρ)θ}(Dd + Rad + 1) ≤ ρ` 对 `ρ` 循环——与 hclosG（`P6HclosCCondP6HC`）、
`hclosC_of_cover_P6M3` 的 `hcover`（DF-1）是同一个义务；同 slab 部分同样受此限制。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **两步 survival ⇒ 标量界（单 history，`_PCE`）**：traced region `(ρ, θ, K)` 于 `(σ, y)`、
`x₁ ∈ B_σ(y, r)`、`tr` = `x₁` 在 `[j⁻, activeStage σ]` 的 trace、`r + e^{9Kθ}ℓ₁ + e^{9Kθ}ℓ₂ ≤ ρ`；
slab `j` 内 `v, τ ∈ [σ − θ, σ]`，`d_v(tr.point, x) < ℓ₁`、`d_τ(x, z) < ℓ₂` ⇒ `R(τ, z) ≤ 9K`。 -/
theorem scalar_le_of_twoStep_survival_PCE (H : ObservedHistory.{u})
    (σ : Icc (0 : ℝ) H.horizon) (y : (H.stageAt σ).Carrier) {ρ θ K r ℓ₁ ℓ₂ : ℝ}
    (htr : H.isTracedRegion σ y ρ θ K) (hK : 0 ≤ K) (hℓ₁ : 0 < ℓ₁) (hℓ₂ : 0 < ℓ₂)
    (hrad : r + Real.exp (9 * K * θ) * ℓ₁ + Real.exp (9 * K * θ) * ℓ₂ ≤ ρ)
    (x₁ : (H.stageAt σ).Carrier)
    (hx₁ : x₁ ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y r)
    (j : Fin H.eventCount) (hjσ : j.castSucc ≤ H.activeStage σ)
    (tr : BackwardPointTrace H j.castSucc (H.activeStage σ) hjσ x₁)
    (v : ℝ) (hvθ : (σ : ℝ) - θ ≤ v) (hvσ : v ≤ σ) (hv1 : H.time j.castSucc ≤ v)
    (hv2 : v < H.time j.succ) (x : (H.stage j.castSucc).Carrier)
    (hx : riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
      (tr.point j.castSucc le_rfl hjσ) x < ENNReal.ofReal ℓ₁)
    (τ : ℝ) (hτθ : (σ : ℝ) - θ ≤ τ) (hτσ : τ ≤ σ) (hτ1 : H.time j.castSucc ≤ τ)
    (hτ2 : τ < H.time j.succ) (z : (H.stage j.castSucc).Carrier)
    (hz : riemannianEDistOf ((H.event j).incoming.flow.base.metric τ) x z < ENNReal.ofReal ℓ₂) :
    (H.event j).incoming.flow.scalar τ z ≤ 9 * K := by
  set L : ℝ := Real.exp (9 * K * θ) with hLdef
  have hL : 0 < L := Real.exp_pos _
  have hdomv : v ∈ H.stageDomain j.castSucc := by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show v ∈ Ico (H.time j.castSucc) (H.time j.succ) from ⟨hv1, hv2⟩)
  have hdomτ : τ ∈ H.stageDomain j.castSucc := by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show τ ∈ Ico (H.time j.castSucc) (H.time j.succ) from ⟨hτ1, hτ2⟩)
  have hx' : riemannianEDistOf (H.stageMetric j.castSucc v) (tr.point j.castSucc le_rfl hjσ) x <
      ENNReal.ofReal ℓ₁ := by
    rw [ObservedHistory.stageMetric_castSucc_apply]
    exact hx
  have hrad1 : r + L * ℓ₁ ≤ ρ := by nlinarith [mul_pos hL hℓ₂]
  obtain ⟨x', -, hxx', A, hA, -⟩ := H.survives_of_traced_ball_P6E σ y htr hK hℓ₁ hrad1 x₁ hx₁
    j.castSucc hjσ tr v hvθ hvσ hdomv x hx'
  have hr : 0 ≤ r := by
    have h0 : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) y x₁ < ENNReal.ofReal r := hx₁
    by_contra hneg
    rw [ENNReal.ofReal_of_nonpos (by linarith)] at h0
    exact (ENNReal.not_lt_zero h0).elim
  have hx'r : x' ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y (r + L * ℓ₁) := by
    change riemannianEDistOf _ y x' < ENNReal.ofReal (r + L * ℓ₁)
    have h0 : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) y x₁ < ENNReal.ofReal r := hx₁
    calc riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) y x'
        ≤ riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) y x₁ +
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ) x₁ x' :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal r + ENNReal.ofReal (L * ℓ₁) :=
          ENNReal.add_lt_add_of_lt_of_le
            (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxx') h0 hxx'
      _ = ENNReal.ofReal (r + L * ℓ₁) := (ENNReal.ofReal_add hr (mul_pos hL hℓ₁).le).symm
  have hrad2 : r + L * ℓ₁ + L * ℓ₂ ≤ ρ := hrad
  have hz' : riemannianEDistOf (H.stageMetric j.castSucc τ) (A.point j.castSucc le_rfl hjσ) z <
      ENNReal.ofReal ℓ₂ := by
    rw [hA, ObservedHistory.stageMetric_castSucc_apply]
    exact hz
  obtain ⟨-, -, -, -, -, hRm⟩ := H.survives_of_traced_ball_P6E σ y htr hK hℓ₂ hrad2 x' hx'r
    j.castSucc hjσ A τ hτθ hτσ hdomτ z hz'
  have h := scalar_le_of_normSq_le_P6E (H.stageMetric j.castSucc τ) z hRm
  rw [abs_of_nonneg hK, ObservedHistory.stageMetric_castSucc_apply] at h
  exact h

end ObservedHistory

/-- **J16 ⇐ 半径一致 traced 曲率（GAP-WITNESS，`_PCE`）**：结论 = KT2c `hOpenJ` J16 合取逐字；`huni` =
`P6HclosCCondP6HC` 的内联 `huni` 逐字（不是树内已登记 binder）。 -/
theorem ObservedHistory.j16_of_uniformK_PCE (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (huni : ∀ θ : ℝ, 0 < θ → ∃ K : ℝ, 0 ≤ K ∧ ∀ A : ℝ, 0 < A → ∀ᶠ n in atTop,
      (Kh n).isTracedRegion (σ n) (y n) (A / Real.sqrt (R n)) (θ / R n) (K * R n)) :
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
        ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
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
          ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
            (Kh n).time j'.castSucc < s →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n)) →
            ∀ z : ((Kh n).stage j'.castSucc).Carrier,
              riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
                  ENNReal.ofReal
                    (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) →
                ((Kh n).event j').incoming.flow.scalar s z ≤
                  C * ((Kh n).event j').incoming.flow.scalar v w := by
  intro Rad B σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  have hθ : 0 < max B 0 - σ₁ + 1 := by linarith [le_max_right B 0]
  obtain ⟨K, hK, hev⟩ := huni (max B 0 - σ₁ + 1) hθ
  set θb : ℝ := max B 0 - σ₁ + 1 with hθbdef
  set E : ℝ := Real.exp (9 * K * θb) with hEdef
  have hE : 0 < E := Real.exp_pos _
  have hM : 0 ≤ max Rad 0 := le_max_right _ _
  have hρb : 0 < Dw + E * (Dd + max Rad 0) + E * 1 := by
    have := mul_pos hE (show 0 < Dd + max Rad 0 by linarith)
    linarith
  refine ⟨max (9 * K) 1, le_max_right _ _, ?_⟩
  filter_upwards [hev _ hρb] with n htrn
  intro j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w _hwseed hwnear hRw x hx s hs hsv hs1
    _hxseed z hz
  set C : ℝ := max (9 * K) 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  have hC9 : 9 * K ≤ C := le_max_left _ _
  have hRn := hR n
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  set Rw : ℝ := ((Kh n).event j').incoming.flow.scalar v w with hRwdef
  have hRw0 : 0 < Rw := hRn.trans_le hRw
  -- near-trace：`d_v(tr.point, x) < (Dd + max Rad 0)/√R`
  have hrad' : Rad / Real.sqrt Rw ≤ max Rad 0 / Real.sqrt (R n) :=
    (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans
      (div_le_div_of_nonneg_left hM hsR (Real.sqrt_le_sqrt hRw))
  have hzx : riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) x < ENNReal.ofReal ((Dd + max Rad 0) / Real.sqrt (R n)) :=
    calc riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
          (tr.point j'.castSucc le_rfl hjσ) x
        ≤ riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w +
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v) w x :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal (Dd / Real.sqrt (R n)) + ENNReal.ofReal (max Rad 0 / Real.sqrt (R n)) :=
          ENNReal.add_lt_add hwnear (lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal hrad'))
      _ = ENNReal.ofReal ((Dd + max Rad 0) / Real.sqrt (R n)) := by
          rw [← ENNReal.ofReal_add (div_nonneg hDd.le hsR.le) (div_nonneg hM hsR.le), ← add_div]
  -- `d_s(x, z) < 1/√R`
  have hball : 1 / Real.sqrt (C * Rw) ≤ 1 / Real.sqrt (R n) := by
    apply one_div_le_one_div_of_le hsR
    apply Real.sqrt_le_sqrt
    nlinarith
  have hz' : riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
      ENNReal.ofReal (1 / Real.sqrt (R n)) :=
    lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal hball)
  -- 深度：`v, s ≥ σ − θb/R`
  have hB : B / Rw ≤ max B 0 / R n :=
    (div_le_div_of_nonneg_right (le_max_left _ _) hRw0.le).trans
      (div_le_div_of_nonneg_left (le_max_right _ _) hRn hRw)
  have hθR : θb / R n = max B 0 / R n - σ₁ / R n + 1 / R n := by
    rw [hθbdef]
    ring
  have h1R : 0 < 1 / R n := one_div_pos.2 hRn
  have hB0 : 0 ≤ max B 0 / R n := div_nonneg (le_max_right _ _) hRn.le
  have hvθ : (σ n : ℝ) - θb / R n ≤ v := by linarith
  have hsθ : (σ n : ℝ) - θb / R n ≤ s := by linarith
  have hvσ : v ≤ (σ n : ℝ) := by
    have : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ hRn
    linarith
  have hexp : Real.exp (9 * (K * R n) * (θb / R n)) = E := by
    rw [hEdef]
    congr 1
    field_simp
  have hrad : Dw / Real.sqrt (R n) +
      Real.exp (9 * (K * R n) * (θb / R n)) * ((Dd + max Rad 0) / Real.sqrt (R n)) +
      Real.exp (9 * (K * R n) * (θb / R n)) * (1 / Real.sqrt (R n)) ≤
      (Dw + E * (Dd + max Rad 0) + E * 1) / Real.sqrt (R n) := by
    rw [hexp]
    apply le_of_eq
    ring
  have hsc := ObservedHistory.scalar_le_of_twoStep_survival_PCE (Kh n) (σ n) (y n) htrn
    (mul_nonneg hK hRn.le) (div_pos (by linarith) hsR) (div_pos one_pos hsR) hrad x₁ hx₁ j' hjσ
    tr v hvθ hvσ hv1.le hv2 x hzx s hsθ (hsv.trans hvσ) hs1.le (lt_of_le_of_lt hsv hv2) z hz'
  calc ((Kh n).event j').incoming.flow.scalar s z ≤ 9 * (K * R n) := hsc
    _ = 9 * K * R n := by ring
    _ ≤ C * R n := mul_le_mul_of_nonneg_right hC9 hRn.le
    _ ≤ C * Rw := mul_le_mul_of_nonneg_left hRw (by linarith)

/-- consumer：`huni` 下 J16 在具体参数处给出常数 `C ≥ 1`（`_PCE`）。 -/
example (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (huni : ∀ θ : ℝ, 0 < θ → ∃ K : ℝ, 0 ≤ K ∧ ∀ A : ℝ, 0 < A → ∀ᶠ n in atTop,
      (Kh n).isTracedRegion (σ n) (y n) (A / Real.sqrt (R n)) (θ / R n) (K * R n)) :
    ∃ C : ℝ, 1 ≤ C := by
  obtain ⟨C, hC, -⟩ := ObservedHistory.j16_of_uniformK_PCE Kh Tn aSeed σ haT hsT has pT seedTrace
    y R L hR huni 1 1 (-1) (-1) le_rfl (by norm_num) 1 1 one_pos one_pos
  exact ⟨C, hC⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
