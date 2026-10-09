import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TracedBallSurvivalHIJ16
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorP6AN
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionMaximalDepth

/-!
# hgap J16 ⇐ hPN 中心 driver 输出 `hDext` + HI pinching（J16PT G2，后缀 `_J16`）

KT2c `hOpenJ` / `hOpen8J` 的 J16 合取（同 slab **与** 跨 event，同一证明）⇐
* `hDext : ∀ φ StrictMono, ∃ ψ StrictMono, ∀ T > 0, DepthExtendable Kh σ y R (φ ∘ ψ) T`
  （hOpenJ 内已有的 driver 输出合取，J14 同源，`j14_of_depthExt_P6HA`）；
* `hpin`（stage 度量处于参数 `aP n + s` 的 fixed HI region，`0 ≤ aP n`；guarded driver
  `exists_subseq_forall_depthExtendable_of_hPN_anyPos_guarded_P6HK` 的既有输入，同形）；
* hgap 现成前提：`1 ≤ aSeed n`、`hwin`、`n + 1 ≤ R n`。
**为何没有 K(A) 循环**：G1 `scalar_le_of_twoStep_survival_HI_J16` 的覆盖因子是
`exp(3Φ(9K·R)·θ/R)`（单侧 Grönwall + HI 的 Ric 下界），`Φ(s)/s → 0` ⇒ K 固定后 n 充分大时 ≤ 2
（`eventually_exp_le_two_J16`）。于是先取半径 `ρb := Dw + 2(Dd + max Rad 0) + 2`、深度
`θb := max B 0 − σ₁ + 1`，再由 `hDext` 取 `K(ρb)`，`C := max (9K) 1`；子列 → `∀ᶠ n` 由
`exists_const_eventually_of_subseq_P6AN`（结论对 `C ≥ C₀` 一致成立）。
J16 的两个 footprint 前提不用。不需要半径一致 `K`（`huni`）、F7、w 尺度深度延伸。
* `j16_slice_of_traced_HI_J16`：单 history 版（固定 n）。
* **`j16_of_depthExt_HI_J16`**：结论 = J16 合取逐字（与 `j16_of_uniformK_PCE` 结论同文）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

/-- **覆盖因子最终 ≤ 2（`_J16`）**：`Φ` 允许、`n + 1 ≤ R n`、`K ≥ 0`、`θ > 0` ⇒
`∀ᶠ n, exp(3Φ(9(K·R n))·(θ / R n)) ≤ 2`。 -/
theorem eventually_exp_le_two_J16 {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (R : ℕ → ℝ) (hR : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n) {K θ : ℝ} (hK : 0 ≤ K) (hθ : 0 < θ) :
    ∀ᶠ n in atTop, Real.exp (3 * Phi (9 * (K * R n)) * (θ / R n)) ≤ 2 := by
  set M : ℝ := 9 * K + 1 with hMdef
  have hM : 0 < M := by rw [hMdef]; linarith
  have hRt : Tendsto R atTop atTop :=
    tendsto_atTop_mono hR (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hMR : Tendsto (fun n => M * R n) atTop atTop := hRt.const_mul_atTop hM
  have hq := hPhi.quotientTendsto.comp hMR
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set ε : ℝ := Real.log 2 / (3 * M * θ) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  filter_upwards [hq (Iio_mem_nhds hε)] with n hn
  have hn' : Phi (M * R n) / (M * R n) < ε := hn
  have hRn : 0 < R n := by have := hR n; have h0 : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  have hMRn : 0 < M * R n := mul_pos hM hRn
  have hPle : Phi (9 * (K * R n)) ≤ Phi (M * R n) := hPhi.mono (by rw [hMdef]; nlinarith)
  have hPlt : Phi (M * R n) < ε * (M * R n) := (div_lt_iff₀ hMRn).mp hn'
  have hkey : 3 * Phi (9 * (K * R n)) * (θ / R n) ≤ Real.log 2 := by
    have h1 : 3 * Phi (9 * (K * R n)) * (θ / R n) ≤ 3 * (ε * (M * R n)) * (θ / R n) := by
      have hθR : 0 ≤ θ / R n := div_nonneg hθ.le hRn.le
      nlinarith
    have h2 : 3 * (ε * (M * R n)) * (θ / R n) = Real.log 2 := by
      rw [hεdef]
      field_simp
    linarith
  calc Real.exp (3 * Phi (9 * (K * R n)) * (θ / R n)) ≤ Real.exp (Real.log 2) :=
        Real.exp_le_exp.2 hkey
    _ = 2 := Real.exp_log two_pos

/-- **J16 单 history 版（`_J16`）**：固定 `n` 的 J16 体（`Kh n ↦ H` 等），前提为半径
`(Dw + 2(Dd + max Rad 0) + 2·1)/√R`、深度 `(max B 0 − σ₁ + 1)/R` 的 traced region（`K·R`）、
覆盖因子 ≤ 2、HI（`hpin`）与 `1 ≤ aSeed ≤ σ − θb/R`；对任意 `C ≥ max (9K) 1` 成立。 -/
theorem j16_slice_of_traced_HI_J16 (H : ObservedHistory.{u})
    (Tn aSeed σ : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn) (has : aSeed ≤ σ)
    (pT : (H.stageAt Tn).Carrier)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    (y : (H.stageAt σ).Carrier) (Rn Ln : ℝ) (hR : 0 < Rn)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hbound : ∀ a : ℝ, 1 ≤ a → ∀ R ν : ℝ, (R, ν) ∈ fixedHamiltonIveyRegion a → -ν ≤ Phi R)
    (aP : ℝ) (haP : 0 ≤ aP)
    (hpin : ∀ (s : Icc (0 : ℝ) H.horizon) (x : (H.stageAt s).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage s) s) (aP + s) x)
    (Rad B σ₁ σ₂ : ℝ) (hσ₂ : σ₂ < 0) (Dw Dd : ℝ) (hDd : 0 < Dd)
    (K : ℝ) (hK : 0 ≤ K)
    (htr : H.isTracedRegion σ y ((Dw + 2 * (Dd + max Rad 0) + 2 * 1) / Real.sqrt Rn)
      ((max B 0 - σ₁ + 1) / Rn) (K * Rn))
    (hE : Real.exp (3 * Phi (9 * (K * Rn)) * ((max B 0 - σ₁ + 1) / Rn)) ≤ 2)
    (ha1 : 1 ≤ (aSeed : ℝ)) (hwin : (aSeed : ℝ) ≤ σ - (max B 0 - σ₁ + 1) / Rn)
    (C : ℝ) (hC : max (9 * K) 1 ≤ C) :
    ∀ (j' : Fin H.eventCount) (v : ℝ), H.time j'.castSucc < v →
      v < H.time j'.succ → (σ : ℝ) + σ₁ / Rn ≤ v → v ≤ σ + σ₂ / Rn →
    ∀ x₁ ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y (Dw / Real.sqrt Rn),
    ∀ (hjσ : j'.castSucc ≤ H.activeStage σ)
      (tr : BackwardPointTrace H j'.castSucc (H.activeStage σ) hjσ x₁),
    ∀ (h1 : H.activeStage aSeed ≤ j'.castSucc)
      (h2 : j'.castSucc ≤ H.activeStage Tn) (w : (H.stage j'.castSucc).Carrier),
      riemannianEDistOf ((H.event j').incoming.flow.base.metric v)
          (seedTrace.point j'.castSucc h1 h2) w ≤
        riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
            (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y +
          ENNReal.ofReal (Ln / 2 / Real.sqrt Rn) →
      riemannianEDistOf ((H.event j').incoming.flow.base.metric v)
          (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt Rn) →
      Rn ≤ (H.event j').incoming.flow.scalar v w →
      ∀ x ∈ riemannianBallOf ((H.event j').incoming.flow.base.metric v) w
          (Rad / Real.sqrt ((H.event j').incoming.flow.scalar v w)),
      ∀ s : ℝ, v - B / (H.event j').incoming.flow.scalar v w ≤ s → s ≤ v →
        H.time j'.castSucc < s →
        riemannianEDistOf ((H.event j').incoming.flow.base.metric s)
            (seedTrace.point j'.castSucc h1 h2) x ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (Ln / Real.sqrt Rn) →
        ∀ z : (H.stage j'.castSucc).Carrier,
          riemannianEDistOf ((H.event j').incoming.flow.base.metric s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C * (H.event j').incoming.flow.scalar v w)) →
            (H.event j').incoming.flow.scalar s z ≤
              C * (H.event j').incoming.flow.scalar v w := by
  intro j' v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w _hwseed hwnear hRw x hx s hs hsv hs1
    _hxseed z hz
  set θb : ℝ := max B 0 - σ₁ + 1 with hθbdef
  have hC1 : 1 ≤ C := (le_max_right _ _).trans hC
  have hC9 : 9 * K ≤ C := (le_max_left _ _).trans hC
  have hsR : 0 < Real.sqrt Rn := Real.sqrt_pos.2 hR
  set Rw : ℝ := (H.event j').incoming.flow.scalar v w with hRwdef
  have hRw0 : 0 < Rw := hR.trans_le hRw
  have hM : 0 ≤ max Rad 0 := le_max_right _ _
  have hrad' : Rad / Real.sqrt Rw ≤ max Rad 0 / Real.sqrt Rn :=
    (div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans
      (div_le_div_of_nonneg_left hM hsR (Real.sqrt_le_sqrt hRw))
  have hzx : riemannianEDistOf ((H.event j').incoming.flow.base.metric v)
      (tr.point j'.castSucc le_rfl hjσ) x < ENNReal.ofReal ((Dd + max Rad 0) / Real.sqrt Rn) :=
    calc riemannianEDistOf ((H.event j').incoming.flow.base.metric v)
          (tr.point j'.castSucc le_rfl hjσ) x
        ≤ riemannianEDistOf ((H.event j').incoming.flow.base.metric v)
            (tr.point j'.castSucc le_rfl hjσ) w +
          riemannianEDistOf ((H.event j').incoming.flow.base.metric v) w x :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal (Dd / Real.sqrt Rn) + ENNReal.ofReal (max Rad 0 / Real.sqrt Rn) :=
          ENNReal.add_lt_add hwnear (lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal hrad'))
      _ = ENNReal.ofReal ((Dd + max Rad 0) / Real.sqrt Rn) := by
          rw [← ENNReal.ofReal_add (div_nonneg hDd.le hsR.le) (div_nonneg hM hsR.le), ← add_div]
  have hball : 1 / Real.sqrt (C * Rw) ≤ 1 / Real.sqrt Rn := by
    apply one_div_le_one_div_of_le hsR
    apply Real.sqrt_le_sqrt
    nlinarith
  have hz' : riemannianEDistOf ((H.event j').incoming.flow.base.metric s) x z <
      ENNReal.ofReal (1 / Real.sqrt Rn) :=
    lt_of_lt_of_le hz (ENNReal.ofReal_le_ofReal hball)
  have hB : B / Rw ≤ max B 0 / Rn :=
    (div_le_div_of_nonneg_right (le_max_left _ _) hRw0.le).trans
      (div_le_div_of_nonneg_left (le_max_right _ _) hR hRw)
  have hθR : θb / Rn = max B 0 / Rn - σ₁ / Rn + 1 / Rn := by
    rw [hθbdef]
    ring
  have h1R : 0 < 1 / Rn := one_div_pos.2 hR
  have hB0 : 0 ≤ max B 0 / Rn := div_nonneg (le_max_right _ _) hR.le
  have hvθ : (σ : ℝ) - θb / Rn ≤ v := by linarith
  have hsθ : (σ : ℝ) - θb / Rn ≤ s := by linarith
  have hvσ : v ≤ (σ : ℝ) := by
    have : σ₂ / Rn < 0 := div_neg_of_neg_of_pos hσ₂ hR
    linarith
  -- HI 在 stage 形
  have hpinJ : ∀ (k : Fin (H.eventCount + 1)) (τ : ℝ), τ ∈ H.stageDomain k →
      (σ : ℝ) - θb / Rn ≤ τ → τ ≤ σ → ∀ q : (H.stage k).Carrier,
        InFixedHamiltonIveyRegion (H.stageMetric k τ) (aP + τ) q := by
    intro k τ hdom hτθ hτσ q
    let τI : Icc (0 : ℝ) H.horizon := ⟨τ, by linarith, hτσ.trans σ.2.2⟩
    have hk : H.activeStage τI = k := (H.mem_stageDomain_iff τI k).mp hdom
    subst hk
    exact hpin τI q
  have haP' : 1 ≤ aP + ((σ : ℝ) - θb / Rn) := by linarith
  set E : ℝ := Real.exp (3 * Phi (9 * (K * Rn)) * (θb / Rn)) with hEdef
  have hDM : 0 ≤ (Dd + max Rad 0) / Real.sqrt Rn := div_nonneg (by linarith) hsR.le
  have h1s : 0 ≤ 1 / Real.sqrt Rn := div_nonneg zero_le_one hsR.le
  have hrad : Dw / Real.sqrt Rn + E * ((Dd + max Rad 0) / Real.sqrt Rn) +
      E * (1 / Real.sqrt Rn) ≤ (Dw + 2 * (Dd + max Rad 0) + 2 * 1) / Real.sqrt Rn := by
    have e1 := mul_le_mul_of_nonneg_right hE hDM
    have e2 := mul_le_mul_of_nonneg_right hE h1s
    have e3 : Dw / Real.sqrt Rn + 2 * ((Dd + max Rad 0) / Real.sqrt Rn) +
        2 * (1 / Real.sqrt Rn) = (Dw + 2 * (Dd + max Rad 0) + 2 * 1) / Real.sqrt Rn := by ring
    linarith
  have hsc := ObservedHistory.scalar_le_of_twoStep_survival_HI_J16 H σ y hPhi hbound hpinJ haP'
    htr (mul_nonneg hK hR.le) (div_pos (by linarith) hsR) (div_pos one_pos hsR) hrad x₁ hx₁ j'
    hjσ tr v hvθ hvσ hv1.le hv2 x hzx s hsθ (hsv.trans hvσ) hs1.le (lt_of_le_of_lt hsv hv2) z hz'
  calc (H.event j').incoming.flow.scalar s z ≤ 9 * (K * Rn) := hsc
    _ = 9 * K * Rn := by ring
    _ ≤ C * Rn := mul_le_mul_of_nonneg_right hC9 hR.le
    _ ≤ C * Rw := mul_le_mul_of_nonneg_left hRw (by linarith)

end ObservedHistory

/-- **J16 ⇐ `hDext` + HI（`_J16`，PROVED 相对 `hDext`、`hpin`）**：结论 = KT2c `hOpenJ` J16 合取逐字
（同 slab 与跨 event）。 -/
theorem ObservedHistory.j16_of_depthExt_HI_J16 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRr : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n) (ha1 : ∀ n, 1 ≤ (aSeed n : ℝ))
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (aP : ℕ → ℝ) (haP : ∀ n, 0 ≤ aP n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s) (aP n + s) x)
    (hDext : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T) :
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
  obtain ⟨Phi, hPhi, hbound⟩ :=
    Perelman.exists_admissiblePinchingFunction_neg_le_of_fixedHamiltonIveyRegion
      (a₀ := 1) one_pos
  have hθ : 0 < max B 0 - σ₁ + 1 := by linarith [le_max_right B 0]
  have hρ : 0 < Dw + 2 * (Dd + max Rad 0) + 2 * 1 := by
    have := le_max_right Rad 0
    linarith
  refine exists_const_eventually_of_subseq_P6AN (P := fun n C =>
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
                  C * ((Kh n).event j').incoming.flow.scalar v w) ?_
  intro φ hφ
  obtain ⟨ψ, hψ, hdx⟩ := hDext φ hφ
  obtain ⟨K, hK, htr⟩ := hdx _ hθ _ hρ
  have hφψ : Tendsto (φ ∘ ψ) atTop atTop := (hφ.comp hψ).tendsto_atTop
  have hE := hφψ.eventually (ObservedHistory.eventually_exp_le_two_J16 hPhi R hRr hK hθ)
  have hW := hφψ.eventually (hwin _ hθ)
  refine ⟨ψ, hψ, max (9 * K) 1, ?_⟩
  filter_upwards [htr, hE, hW] with i htri hEi hWi
  intro C hC
  simp only [Function.comp_apply] at htri hEi hWi
  exact ObservedHistory.j16_slice_of_traced_HI_J16 (Kh (φ (ψ i))) (Tn (φ (ψ i)))
    (aSeed (φ (ψ i))) (σ (φ (ψ i))) (haT _) (hsT _) (has _) (pT _) (seedTrace _) (y _)
    (R (φ (ψ i))) (L (φ (ψ i))) (hR _) hPhi hbound (aP _) (haP _) (hpin _) Rad B σ₁ σ₂ hσ₂
    Dw Dd hDd K hK htri hEi (ha1 _) hWi C hC

/-- consumer：`hDext` + HI 下 J16 在具体参数处给出常数 `C ≥ 1`（`_J16`）。 -/
example (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRr : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n) (ha1 : ∀ n, 1 ≤ (aSeed n : ℝ))
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (aP : ℕ → ℝ) (haP : ∀ n, 0 ≤ aP n)
    (hpin : ∀ n (s : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt s).Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage s) s) (aP n + s) x)
    (hDext : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R (φ ∘ ψ) T) :
    ∃ C : ℝ, 1 ≤ C := by
  obtain ⟨C, hC, -⟩ := ObservedHistory.j16_of_depthExt_HI_J16 Kh Tn aSeed σ haT hsT has pT
    seedTrace y R L hR hRr ha1 hwin aP haP hpin hDext 1 1 (-1) (-1) le_rfl (by norm_num) 1 1
    one_pos one_pos
  exact ⟨C, hC⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
