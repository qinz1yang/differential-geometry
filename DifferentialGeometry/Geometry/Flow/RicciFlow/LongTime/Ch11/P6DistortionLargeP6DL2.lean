import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistortionLocalP6DL
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BCDBootstrapBallP6BB

/-!
# 大球短窗距离畸变 ⇐ traced-region 合同（O-CH11-DISTLA2 G1，后缀 `_P6DL2`）

HP6B2 v2 `hdistLA` 槽（`∀ Aseed T r`：`d_τ(O, z) ≤ d_t(O, z) + 1`，`z ∈ B_t(p′, r/√R_k)`，
`τ ∈ [t − T/R_k, t]` ∩ slab）的**大球形**。DISTLA 结论 2：大球 = 空间 BCD + 深窗格点 anchor；本文件把两者都换成
BCDBOOT 的**单一** traced-region 合同 `hTR`（+ J10WIRE2 族 `hfamT`）：
* `chain_backward_P6DL2`（PROVED）：分段求和（对段数归纳）。
* `cDist_P6DL2` / `large_numerics_P6DL2`（PROVED）：显式常数 `c_dist(C2, Q)`、`K := c_dist·R`、`ℓ := 1/√K`、
  段长 `h := 1/(2·max(Ctime,1)·Q·R)`；两条显式终值不等式 (E1) `8·T·√c_dist ≤ √R`、(E2) `16·√c_dist + 2 ≤ L`。
* `ObservedHistory.hdistL_large_single_P6DL2`（PROVED）：单 history 大形 = 整窗逐点界 + 整窗 stay +
  DISTLA `hdistL_of_witness_P6DL` 逐段 + 分段求和。
* `trace_point_heq_P6DL2`（PROVED）：trace 在端点 stage 的点 ≍ 端点。
* **G1 `hdistL_large_of_TR_P6DL2`（PROVISIONAL[`hTR`, `hfamT`]）**：塔层，结论 = 槽内层逐字。
**深度随 `n`**：窗深 `T/R_k`（`T` 任意）上的逐点曲率界**只**取自 `hTR` 在同一 `(T, r)` 的 ∀ 深度形
（traced region 沿 worldline），不由固定深度 eventual 界拼接、不由 ODE ceiling 逐段归纳（R-C11-19 Q3）。
非循环：不经 hlocBCD′ / hstop / hclosG / hscalU / BCBD / CanonicalLateCore / hspine；`hTR` 是输入，不回填。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section Chain

/-- **分段求和（`_P6DL2`，PROVED）**：`f : ℝ → ℝ≥0∞`，局部向后界 `f s ≤ f v + c·(v − s)`（`v − h ≤ s ≤ v`，
都在 `[τ₀, t]` 内）⇒ 整窗 `f s ≤ f t + c·(t − s)`。对段数 `n`（`t − s ≤ n·h`）归纳，`v := min t (s + h)`。 -/
theorem chain_backward_P6DL2 {f : ℝ → ℝ≥0∞} {τ₀ t h c : ℝ} (hh : 0 < h) (hc : 0 ≤ c)
    (hstep : ∀ v ∈ Icc τ₀ t, ∀ s ∈ Icc τ₀ v, v - h ≤ s →
      f s ≤ f v + ENNReal.ofReal (c * (v - s))) :
    ∀ s ∈ Icc τ₀ t, f s ≤ f t + ENNReal.ofReal (c * (t - s)) := by
  have key : ∀ n : ℕ, ∀ s ∈ Icc τ₀ t, t - s ≤ n * h →
      f s ≤ f t + ENNReal.ofReal (c * (t - s)) := by
    intro n
    induction n with
    | zero =>
      intro s hs hn
      have hst : s = t := by
        have h0 : t - s ≤ 0 := by simpa using hn
        linarith [hs.2]
      subst hst
      exact le_self_add
    | succ n ih =>
      intro s hs hn
      by_cases hle : t - s ≤ n * h
      · exact ih s hs hle
      · have hn' : t - s ≤ (n : ℝ) * h + h := by push_cast at hn; linarith
        have hvt : min t (s + h) ≤ t := min_le_left _ _
        have hsv : s ≤ min t (s + h) := le_min hs.2 (by linarith)
        have hvs : min t (s + h) - h ≤ s := by
          have := min_le_right t (s + h)
          linarith
        have htv : t - min t (s + h) ≤ n * h := by
          rcases le_total t (s + h) with h' | h'
          · rw [min_eq_left h', sub_self]
            positivity
          · rw [min_eq_right h']
            linarith
        have h1 := hstep (min t (s + h)) ⟨hs.1.trans hsv, hvt⟩ s ⟨hs.1, hsv⟩ hvs
        have h2 := ih (min t (s + h)) ⟨hs.1.trans hsv, hvt⟩ htv
        calc f s ≤ f (min t (s + h)) + ENNReal.ofReal (c * (min t (s + h) - s)) := h1
          _ ≤ (f t + ENNReal.ofReal (c * (t - min t (s + h)))) +
                ENNReal.ofReal (c * (min t (s + h) - s)) := add_le_add h2 le_rfl
          _ = f t + ENNReal.ofReal (c * (t - s)) := by
            rw [add_assoc, ← ENNReal.ofReal_add (mul_nonneg hc (by linarith))
              (mul_nonneg hc (by linarith))]
            congr 2
            ring
  intro s hs
  obtain ⟨n, hn⟩ := exists_nat_ge ((t - s) / h)
  exact key n s hs (by rwa [div_le_iff₀ hh] at hn)

end Chain

section Numerics

/-- **距离常数 `c_dist`（`_P6DL2`）**：`c_dist(C2, Q) := A·(2Q) + 4·C2·Q + 2500`，
`A := 2√3·(2C2/2 + max(2C2, 2e⁴))`（P6L4 的 Ricci 常数）。大球形取 `K := c_dist·R_k`、`ℓ := 1/√K`。 -/
def cDist_P6DL2 (C2 Q : ℝ) : ℝ :=
  2 * Real.sqrt 3 * (2 * C2 / 2 + max (2 * C2) (2 * Real.exp 4)) * (2 * Q) + 4 * C2 * Q + 2500

/-- **大球形数值（`_P6DL2`，PROVED）**：`1 ≤ C2`、`1 ≤ Q`、`1 ≤ R`、`0 < T`，两条**显式**终值不等式
(E1) `8·T·√c_dist ≤ √R`（⇔ 漂移 `8T·√c_dist/√R ≤ 1`）、(E2) `16·√c_dist + 2 ≤ L` ⇒
`hdistL_of_witness_P6DL` 的全部数值前提（`M := Q·R`、`K := c_dist·R`、`ℓ := 1/√K`、
段长 `h := 1/(2·max(Ctime,1)·M)`）+ stay 余量 `(L/2)/√R + (8/ℓ)h < (3L/4)/√R` + 漂移 `(8/ℓ)(T/R) ≤ 1`。 -/
theorem large_numerics_P6DL2 {C2 Q R T L : ℝ} (Ctime : ℝ≥0) (hC2 : 1 ≤ C2) (hQ : 1 ≤ Q)
    (hR : 1 ≤ R) (hT : 0 < T)
    (hE1 : 8 * T * Real.sqrt (cDist_P6DL2 C2 Q) ≤ Real.sqrt R)
    (hE2 : 16 * Real.sqrt (cDist_P6DL2 C2 Q) + 2 ≤ L) :
    ∃ ℓ K h : ℝ, 0 < ℓ ∧ ℓ ^ 2 * (2 * C2 * (2 * (Q * R))) ≤ 1 ∧ ℓ ≤ 1 / 50 ∧
      K * ℓ ^ 2 ≤ 1 ∧ 1 / 1 ^ 2 ≤ K ∧
      2 * Real.sqrt 3 * (2 * C2 / 2 + max (2 * C2) (2 * Real.exp 4)) * (2 * (Q * R)) ≤ K ∧
      0 < h ∧ (Ctime : ℝ) * (Q * R) * h ≤ 1 / 2 ∧
      3 * L / 4 / Real.sqrt R + ℓ ≤ L / Real.sqrt R ∧
      L / 2 / Real.sqrt R + 8 / ℓ * h < 3 * L / 4 / Real.sqrt R ∧
      8 / ℓ * (T / R) ≤ 1 := by
  set A := 2 * Real.sqrt 3 * (2 * C2 / 2 + max (2 * C2) (2 * Real.exp 4)) with hA
  have hA0 : 0 ≤ A := by
    have h1 : 0 ≤ max (2 * C2) (2 * Real.exp 4) := (by linarith : (0 : ℝ) ≤ 2 * C2).trans
      (le_max_left _ _)
    have h2 : 0 ≤ 2 * C2 / 2 + max (2 * C2) (2 * Real.exp 4) := by linarith
    positivity
  set cD := cDist_P6DL2 C2 Q with hcD
  have hcDdef : cD = A * (2 * Q) + 4 * C2 * Q + 2500 := rfl
  have hcD25 : 2500 ≤ cD := by
    have : 0 ≤ A * (2 * Q) := mul_nonneg hA0 (by linarith)
    nlinarith
  set w := Real.sqrt cD with hw
  set sR := Real.sqrt R with hsR
  have hR0 : 0 < R := by linarith
  have hsR0 : 0 < sR := Real.sqrt_pos.2 hR0
  have hsR1 : 1 ≤ sR := by rw [hsR]; exact Real.one_le_sqrt.2 hR
  have hw2 : w ^ 2 = cD := Real.sq_sqrt (by linarith)
  have hsR2 : sR ^ 2 = R := Real.sq_sqrt hR0.le
  have hw50 : 50 ≤ w := by
    rw [hw]
    have h50 : Real.sqrt 2500 = 50 := by
      rw [show (2500 : ℝ) = 50 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [← h50]
    exact Real.sqrt_le_sqrt hcD25
  have hw0 : 0 < w := by linarith
  have hwsR : 0 < w * sR := mul_pos hw0 hsR0
  have hL2 : 2 ≤ L := by linarith
  have hM : 0 < Q * R := by positivity
  refine ⟨1 / (w * sR), cD * R, 1 / (2 * max (Ctime : ℝ) 1 * (Q * R)), by positivity,
    ?_, ?_, ?_, ?_, ?_, by positivity, ?_, ?_, ?_, ?_⟩
  · -- ℓ²·(2C2·2QR) ≤ 1
    rw [div_pow, one_pow, mul_pow, hw2, hsR2, one_div_mul_eq_div, div_le_one (by positivity),
      hcDdef]
    have h1 : 0 ≤ A * (2 * Q) * R := by positivity
    nlinarith
  · -- ℓ ≤ 1/50
    rw [div_le_div_iff₀ hwsR (by norm_num)]
    nlinarith [mul_nonneg (sub_nonneg.2 hw50) (sub_nonneg.2 hsR1)]
  · -- K·ℓ² ≤ 1
    rw [div_pow, one_pow, mul_pow, hw2, hsR2, mul_one_div_cancel (by positivity)]
  · -- 1 ≤ K
    norm_num
    nlinarith
  · -- A·(2QR) ≤ K
    rw [hcDdef]
    have h1 : 0 ≤ (4 * C2 * Q + 2500) * R := by positivity
    nlinarith
  · -- Ctime·M·h ≤ 1/2
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_right (le_max_left (Ctime : ℝ) 1) hM.le]
  · -- (3L/4)/√R + ℓ ≤ L/√R
    have h2 : 1 / w ≤ L / 4 := by
      rw [div_le_iff₀ hw0]
      nlinarith
    calc 3 * L / 4 / sR + 1 / (w * sR) = 3 * L / 4 / sR + 1 / w / sR := by rw [div_div (1 : ℝ) w sR]
      _ ≤ 3 * L / 4 / sR + L / 4 / sR :=
          add_le_add le_rfl (div_le_div_of_nonneg_right h2 hsR0.le)
      _ = L / sR := by ring
  · -- stay 余量
    have hh : 1 / (2 * max (Ctime : ℝ) 1 * (Q * R)) ≤ 1 / (2 * R) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hmax : 1 ≤ max (Ctime : ℝ) 1 := le_max_right _ _
      have h1 : 1 * R ≤ max (Ctime : ℝ) 1 * Q * R := by
        have := mul_le_mul hmax hQ zero_le_one (by positivity)
        nlinarith
      nlinarith
    have h8 : 8 / (1 / (w * sR)) * (1 / (2 * max (Ctime : ℝ) 1 * (Q * R))) ≤
        8 * (w * sR) * (1 / (2 * R)) := by
      rw [div_div_eq_mul_div, div_one]
      exact mul_le_mul_of_nonneg_left hh (by positivity)
    have h9 : 8 * (w * sR) * (1 / (2 * R)) = 4 * w / sR := by
      rw [← hsR2]
      field_simp
      ring
    rw [h9] at h8
    have h10 : L / 2 / sR + 4 * w / sR < 3 * L / 4 / sR := by
      rw [← add_div, div_lt_div_iff_of_pos_right hsR0]
      linarith
    linarith
  · -- 漂移
    rw [div_div_eq_mul_div, div_one]
    have h9 : 8 * (w * sR) * (T / R) = 8 * T * w / sR := by
      rw [← hsR2]
      field_simp
    rw [h9, div_le_one hsR0]
    linarith

end Numerics

section Single

/-- **单 history 大形（`_P6DL2`，PROVED）**：slab `j` 内 `[τ₀, t]`，U 端点 `x`：
**整窗逐点界** `∀ s ∈ [τ₀, t]，R_s(x) ≤ M`（大形里由 hTR 的 traced region 沿 worldline 给出，∀ 深度）、
**整窗 stay** `d_s(O, x) ≤ d_σ + Ls/√R`（大形里由 BCDBOOT `hstopE_deep_tower_P6BB` 给出）、段长 `h`
（`Ctime′·M·h ≤ 1/2`）、余量 `Ls/√R + (8/ℓ)h < Lc/√R`、`d_σ < ⊤`，以及 `hdistL_of_witness_P6DL` 的数值前提 ⇒
`∀ τ ∈ [τ₀, t]`，`d_τ(O, x) ≤ d_t(O, x) + (8/ℓ)(t − τ)`。
证明：局部步 = `hdistL_of_witness_P6DL` 作用在 `[s, v]`（`v − h ≤ s`，顶点值取逐点界、余量取 stay），
整窗 = `chain_backward_P6DL2`（不需要 ODE 跨段：每段顶点值都由逐点界独立付，常数不翻倍）。 -/
theorem ObservedHistory.hdistL_large_single_P6DL2 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (H : ObservedHistory.{u}) {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (H.stageAt Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature H Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) H.horizon) (x : (H.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage t) t) (a₀ + t) x)
    (y : (H.stageAt σ).Carrier) {R L Lc Ls : ℝ} (hR : 0 < R)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
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
    (j : Fin H.eventCount) (h1 : H.activeStage aSeed ≤ j.castSucc)
    (h2 : j.castSucc ≤ H.activeStage Tn) (x : (H.stage j.castSucc).Carrier)
    {τ₀ t M ℓ K h : ℝ} (hτ1 : H.time j.castSucc < τ₀) (ht2 : t < H.time j.succ)
    (haτ : (aSeed : ℝ) ≤ τ₀) (htσ : t ≤ σ) (hLτ : (σ : ℝ) - L ^ 2 / R ≤ τ₀)
    (hM : 0 < M) (hCgM : Cg * R ≤ M) (hC2 : 1 ≤ C2')
    (hxM : ∀ s ∈ Icc τ₀ t, (H.event j).incoming.flow.scalar s x ≤ M)
    (hh : 0 < h) (hbud : (Ctime' : ℝ) * M * h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓM : ℓ ^ 2 * (2 * C2' * (2 * M)) ≤ 1) (hℓr : ℓ ≤ r / 50)
    (hKℓ : K * ℓ ^ 2 ≤ 1) (hKr : 1 / r ^ 2 ≤ K)
    (hKC : 2 * Real.sqrt 3 * (2 * C2' / 2 + max (2 * C2') (2 * Real.exp 4)) * (2 * M) ≤ K)
    (hMτ : 1 ≤ 2 * M * τ₀)
    (hLc : Lc / Real.sqrt R + ℓ ≤ L / Real.sqrt R) (hLc0 : 0 ≤ Lc) (hLs0 : 0 ≤ Ls)
    (hLs : Ls / Real.sqrt R + 8 / ℓ * h < Lc / Real.sqrt R)
    (hfin : riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
        (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
          (H.activeStage_mono hsT)) y ≠ ⊤)
    (hstay : ∀ s ∈ Icc τ₀ t, riemannianEDistOf ((H.event j).incoming.flow.base.metric s)
        (seedTrace.point j.castSucc h1 h2) x ≤
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (Ls / Real.sqrt R)) :
    ∀ τ ∈ Icc τ₀ t, riemannianEDistOf ((H.event j).incoming.flow.base.metric τ)
        (seedTrace.point j.castSucc h1 h2) x ≤
      riemannianEDistOf ((H.event j).incoming.flow.base.metric t)
        (seedTrace.point j.castSucc h1 h2) x + ENNReal.ofReal (8 / ℓ * (t - τ)) := by
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hc8 : (0 : ℝ) ≤ 8 / ℓ := div_nonneg (by norm_num) hℓ.le
  refine chain_backward_P6DL2 (f := fun s => riemannianEDistOf
    ((H.event j).incoming.flow.base.metric s) (seedTrace.point j.castSucc h1 h2) x) hh hc8 ?_
  intro v hv s hs hvs
  have hs1 : H.time j.castSucc < s := hτ1.trans_le hs.1
  have hv2 : v < H.time j.succ := hv.2.trans_lt ht2
  have hbud' : (Ctime' : ℝ) * M * (v - s) ≤ 1 / 2 := by
    have hCM : (0 : ℝ) ≤ Ctime' * M := mul_nonneg Ctime'.coe_nonneg hM.le
    exact (mul_le_mul_of_nonneg_left (by linarith) hCM).trans hbud
  have hMs : 1 ≤ 2 * M * s := by
    have := mul_le_mul_of_nonneg_left hs.1 (by positivity : (0 : ℝ) ≤ 2 * M)
    linarith
  have hd8 : 8 / ℓ * (v - s) ≤ 8 / ℓ * h := mul_le_mul_of_nonneg_left (by linarith) hc8
  have hmargin : riemannianEDistOf ((H.event j).incoming.flow.base.metric v)
        (seedTrace.point j.castSucc h1 h2) x + ENNReal.ofReal (8 / ℓ * (v - s)) <
      riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (Lc / Real.sqrt R) := by
    have hLs8 : 0 ≤ 8 / ℓ * h := mul_nonneg hc8 hh.le
    calc _ ≤ (riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (Ls / Real.sqrt R)) +
          ENNReal.ofReal (8 / ℓ * h) :=
          add_le_add (hstay v ⟨hs.1.trans hs.2, hv.2⟩) (ENNReal.ofReal_le_ofReal hd8)
      _ = riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
          (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
            (H.activeStage_mono hsT)) y + ENNReal.ofReal (Ls / Real.sqrt R + 8 / ℓ * h) := by
          rw [add_assoc, ENNReal.ofReal_add (div_nonneg hLs0 hsR.le) hLs8]
      _ < _ := by
          refine ENNReal.add_lt_add_left hfin ?_
          refine (ENNReal.ofReal_lt_ofReal_iff ?_).2 hLs
          have : 0 ≤ Ls / Real.sqrt R + 8 / ℓ * h := by positivity
          linarith
  exact H.hdistL_of_witness_P6DL haT hsT has hsmall hclock seedTrace ha₀ hpin y hR hgood j h1 h2 x
    hs1 hs.2 hv2 (haτ.trans hs.1) (hv.2.trans htσ) (hLτ.trans hs.1) hM hCgM hC2 (hxM v hv) hbud'
    hℓ hℓM hℓr hKℓ hKr hKC hMs hLc hLc0 hmargin s ⟨le_rfl, hs.2⟩

end Single
section Tower

/-- **traced trace 端点（`_P6DL2`，PROVED）**：`activeStage s = activeStage t` ⇒ trace 在
`activeStage s` 处的点与端点 `p` HEq（`endpoint_eq` + 索引 `subst`）。 -/
theorem trace_point_heq_P6DL2 {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t}
    {p : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    {s : Icc (0 : ℝ) H.horizon} (has : a ≤ s) (hst : s ≤ t)
    (hk : H.activeStage s = H.activeStage t) :
    HEq (A.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hst)) p := by
  have key : ∀ (j : Fin (H.eventCount + 1)) (_ : j = H.activeStage t)
      (h1 : H.activeStage a ≤ j) (h2 : j ≤ H.activeStage t), HEq (A.point j h1 h2) p := by
    intro j hj h1 h2
    subst hj
    exact heq_of_eq A.endpoint_eq
  exact key _ hk _ _

/-- **G1 大球形 `hdistL_large_of_TR_P6DL2`（`_P6DL2`，PROVISIONAL[`hTR`, `hfamT`]）**：结论 = HP6B2 v2
`hdistLA` 槽的内层**逐字**（槽前缀里本证明不用的 `Aseed`/体积/`2 < Tn`/neckRadius/`d_σ + (L+1)/√R` 五条已删，
G2 补回）。binder：`hfamT`（J10WIRE2 族：HI `a₀`、records、`T₀ ≤ aSeed`、`d_σ < ⊤`、WindowNeckScaleBudget；
与 BCDBOOT `hderivL_of_hgood_firstExit_TRonly_P6BB` **逐字**）+ `hTR`（BCDBOOT traced-region 合同，**逐字**：
`∀ T r`，`∀ᶠ k`、`∀ᶠ t ↑ σ`，`isTracedRegion t (y′ ≍ p′) (r/√R_k) (T/R_k) (Ktr r T · R_k)`）+ cap 参数
`qp`（`transitionEnd + 10 < modelRadius`、`modelAccuracy ≤ ε₀`、`2 ≤ modelOrder`、`δ → 0`）+ `1 ≤ C2`。
**深度随 `n` 的处理**：窗深 `T/R_k` 的整窗逐点界**只**来自 `hTR` 在同一 `(T, r)` 处的 ∀ 深度形（traced region
沿 `z` 的 worldline 给 `R_s(z) ≤ 9·Ktr r T·R_k`，`s ∈ [t − T/R_k, t]`），**不**由固定深度的 eventual 界拼接、
也不由上一段 ODE ceiling 归纳（R-C11-19 Q3）。
**常数（显式）**：`Q := max (max (9·Ktr r T) 4) 1`、`M_k := Q·R_k`、`c_dist := cDist_P6DL2 C2 Q`、
`K_k := c_dist·R_k`、`ℓ_k := 1/√K_k`、段长 `h_k := 1/(2·max(Ctime,1)·M_k)`；**∀ᶠ k 条件（显式）**：
(E1) `8·T·√c_dist ≤ √R_k`（⇔ 漂移 `8T·√c_dist/√R_k ≤ 1`，由 `1/200·√R_k → ∞`）、
(E2) `16·√c_dist + 2 + 2T ≤ L_k`（由 `L_k → ∞`）、`aSeed ≤ σ − 2T/R_k`。
证明：stay `d_s(O, z) ≤ d_σ + (L_k/2)/√R_k` = BCDBOOT `hstopE_deep_tower_P6BB`（取 `L/2`；
其 `hballT` / `hgridT`
由 `hballT_of_tracedRegion_P6BB` / `hgridTr_of_tracedRegion_P6BB` 从 `hTR` 付）；逐点界 = `hTR` +
`hgrid_of_isTracedRegion_P6BB`；单 history 核 `hdistL_large_single_P6DL2`；数值 `large_numerics_P6DL2`。 -/
theorem hdistL_large_of_TR_P6DL2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
      {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {qp : CutoffParameters} {Ktr : ℝ → ℝ → ℝ},
    1 ≤ C2 → StandardCap.transitionEnd + 10 < qp.modelRadius → qp.modelAccuracy ≤ ε₀ →
    2 ≤ qp.modelOrder → Tendsto qp.delta atTop (𝓝 0) →
    (∀ r T, 0 ≤ Ktr r T) →
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
          (∀ k, riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) ≠ ⊤) ∧
          ∀ᶠ k in atTop, WindowNeckScaleBudget_P6HS (Kh k) (qp.rescale_P6N (c k) (hc k))
            (T₀ k) (aSeed k : ℝ) (R k)
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
            ∀ (tt : Icc (0 : ℝ) (Kh k).horizon), (tt : ℝ) = t →
            ∀ y' : ((Kh k).stageAt tt).Carrier, HEq y' p' →
              (Kh k).isTracedRegion tt y' (r / Real.sqrt (R k)) (T / R k) (Ktr r T * R k)
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
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ (h1 : (Kh k).activeStage (aSeed k) ≤ (i k).castSucc)
            (h2 : (i k).castSucc ≤ (Kh k).activeStage (Tn k)),
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ, ∀ τ : ℝ,
            t - T / R k ≤ τ → τ ≤ t → (Kh k).time (i k).castSucc < τ →
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
              riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric τ)
                  ((seedTrace k).point (i k).castSucc h1 h2) z ≤
                riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric t)
                  ((seedTrace k).point (i k).castSucc h1 h2) z + ENNReal.ofReal 1 := by
  obtain ⟨ε₀, hε₀, hST⟩ := hstopE_deep_tower_P6BB.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F ε C1 C2 Ctime qp Ktr hC2 hDm hacc hm hδlim hK hfamT hTR T r hT hr ind c hc Kh Tn pT
    hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL hsel hgood haS hTnS
    hroom hradii i hi
  obtain ⟨a₀, _T₀, _records, ha₀, hpin, -, -, -, hfin, -⟩ := hfamT ind c hc Tn pT hTc
    aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL hsel hgood haS hTnS
    hroom hradii
  -- stay 用 L/2（hgood 对 L 反单调）
  have hL2 : Tendsto (fun k => L k / 2) atTop atTop := hL.atTop_div_const two_pos
  have hgood2 : ∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
      (σ k : ℝ) - (L k / 2) ^ (2 : ℕ) / R k ≤ (v : ℝ) →
      ∀ z : ((Kh k).stageAt v).Carrier,
        riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
            ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
              ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
          riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
              ((seedTrace k).point ((Kh k).activeStage (σ k))
                ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
            ENNReal.ofReal (L k / 2 / Real.sqrt (R k)) →
        4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
        (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z := by
    intro k v hav hvs hvL z hz hRz
    refine hgood k v hav hvs ?_ z (hz.trans (add_le_add le_rfl ?_)) hRz
    · have h1 : (L k / 2) ^ (2 : ℕ) / R k ≤ L k ^ (2 : ℕ) / R k :=
        div_le_div_of_nonneg_right (by have := sq_nonneg (L k); linarith) (hRpos k).le
      linarith
    · rcases le_total 0 (L k) with h0 | h0
      · exact ENNReal.ofReal_le_ofReal
          (div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
      · rw [ENNReal.ofReal_of_nonpos
          (div_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _))]
        exact zero_le
  have hb := betaStar_P6BB (Ctime := Ctime) (Cball := fun r => 9 * Ktr r 1)
    (Cgrid := fun r T => 9 * Ktr r T)
  have hstay := hST (Cball := fun r => 9 * Ktr r 1) (Cgrid := fun r T => 9 * Ktr r T)
    (β := fun r T => gridStep_P6BB Ctime (fun r => 9 * Ktr r 1) (fun r T => 9 * Ktr r T) r T)
    (by linarith) hDm hacc hm hδlim hb.1 hb.2 hfamT (hballT_of_tracedRegion_P6BB hK hTR)
    (hgridTr_of_tracedRegion_P6BB hK hTR) T r hT hr ind c hc Tn pT hTc aSeed haT hclock hone hsm
    seedTrace σ y R hsT has (fun k => L k / 2) hRdef hRpos hRr hL2 hsel hgood2 haS hTnS hroom
    hradii i hi
  have htr := hTR T r hT hr ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has
    L hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  -- 显式常数 Q
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = max (max (9 * Ktr r T) 4) 1 := ⟨_, rfl⟩
  have hQ1 : (1 : ℝ) ≤ Q := hQ ▸ le_max_right _ _
  have hQ4 : (4 : ℝ) ≤ Q := hQ ▸ (le_max_right _ _).trans (le_max_left _ _)
  have hQ9 : 9 * Ktr r T ≤ Q := hQ ▸ (le_max_left _ _).trans (le_max_left _ _)
  filter_upwards [hstay, htr, haS (2 * T) (by linarith),
    hL.eventually_ge_atTop (16 * Real.sqrt (cDist_P6DL2 C2 Q) + 2 + 2 * T),
    hradii.eventually_ge_atTop (8 * T * Real.sqrt (cDist_P6DL2 C2 Q))]
    with k hstk htrk haSk hLk hRk
  intro p' q hq hcross h1 h2
  have hcs : (Kh k).time (i k).castSucc < (Kh k).time (i k).succ :=
    (Kh k).time_strictMono Fin.castSucc_lt_succ
  have hσ' : (σ k : ℝ) = (Kh k).time (i k).succ := hi k
  have hRk0 := hRpos k
  have hR1 : (1 : ℝ) ≤ R k := by
    have h0 := hRr k
    have h00 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hTR0 : 0 < T / R k := div_pos hT hRk0
  have e2 : 2 * T / R k = T / R k + T / R k := by ring
  have hsc0 := Real.sqrt_nonneg (cDist_P6DL2 C2 Q)
  filter_upwards [hstk p' q hq hcross, htrk p' q hq hcross,
    Ioo_mem_nhdsLT (show max ((Kh k).time (i k).castSucc) ((σ k : ℝ) - T / R k) <
      (Kh k).time (i k).succ from max_lt hcs (by linarith))] with t hst htr' hti
  intro τ hτ1 hτ2 hτ3 z hz
  have ht1 : (Kh k).time (i k).castSucc < t := lt_of_le_of_lt (le_max_left _ _) hti.1
  have htσ0 : (σ k : ℝ) - T / R k < t := lt_of_le_of_lt (le_max_right _ _) hti.1
  have ht0 : 0 ≤ t := ((Kh k).time_nonneg _).trans ht1.le
  have hth : t ≤ (Kh k).horizon := hti.2.le.trans ((hi k) ▸ (σ k).2.2)
  let tt : Icc (0 : ℝ) (Kh k).horizon := ⟨t, ht0, hth⟩
  have htt : (tt : ℝ) = t := rfl
  have he : (Kh k).activeStage tt = (i k).castSucc :=
    (Kh k).activeStage_eq_of_mem_slab_P6F3 (i k) tt ht1.le hti.2
  have htσ : tt ≤ σ k := by
    change t ≤ (σ k : ℝ)
    linarith [hti.2]
  obtain ⟨y', hy'⟩ := (Kh k).exists_heq_stageAt_P6JW he p'
  obtain ⟨z', hz'⟩ := (Kh k).exists_heq_stageAt_P6JW he z
  have hzy : z' ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage tt) tt) y'
      (r / Real.sqrt (R k)) := by
    rw [ObservedHistory.ball_transport_P6BB he htt z' y' z p' hz' hy',
      ObservedHistory.stageMetric_castSucc_apply]
    exact hz
  obtain ⟨-, -, a₁, ha₁t, ha₁eq, hreg⟩ := htr' tt htt y' hy'
  obtain ⟨A₁, -⟩ := hreg z' hzy
  have ha₁eq' : (a₁ : ℝ) = t - T / R k := ha₁eq
  have haSa₁ : aSeed k ≤ a₁ := by
    change (aSeed k : ℝ) ≤ a₁
    linarith
  have hP : ∀ zc : ((Kh k).stage (i k).castSucc).Carrier, HEq z' zc →
      zc ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
        (r / Real.sqrt (R k)) := by
    intro zc hzc
    have hzc' : zc = z := eq_of_heq (hzc.symm.trans hz')
    rw [hzc']
    exact hz
  have hstay' := hst tt htt htσ a₁ haSa₁ ha₁t (le_of_eq ha₁eq'.symm) z' hP A₁
  -- 整窗逐点界（hTR，∀ 深度）+ 整窗 stay，搬到 slab 形
  have hpt : ∀ s ∈ Icc τ t,
      ((Kh k).event (i k)).incoming.flow.scalar s z ≤ Q * R k ∧
      riemannianEDistOf (((Kh k).event (i k)).incoming.flow.base.metric s)
          ((seedTrace k).point (i k).castSucc h1 h2) z ≤
        riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) +
          ENNReal.ofReal (L k / 2 / Real.sqrt (R k)) := by
    intro s hs
    have hs0 : 0 ≤ s := ((Kh k).time_nonneg _).trans (hτ3.le.trans hs.1)
    have hsh : s ≤ (Kh k).horizon := hs.2.trans hth
    let sI : Icc (0 : ℝ) (Kh k).horizon := ⟨s, hs0, hsh⟩
    have hsI : (sI : ℝ) = s := rfl
    have hes : (Kh k).activeStage sI = (i k).castSucc :=
      (Kh k).activeStage_eq_of_mem_slab_P6F3 (i k) sI (hτ3.le.trans hs.1)
        (lt_of_le_of_lt hs.2 hti.2)
    have ha₁s : a₁ ≤ sI := by
      change (a₁ : ℝ) ≤ s
      linarith [hs.1]
    have hst' : sI ≤ tt := by
      change s ≤ t
      exact hs.2
    have hAz : HEq (A₁.point ((Kh k).activeStage sI) ((Kh k).activeStage_mono ha₁s)
        ((Kh k).activeStage_mono hst')) z :=
      (trace_point_heq_P6DL2 (a := a₁) (t := tt) (hat := ha₁t) A₁ ha₁s hst'
        (hes.trans he.symm)).trans hz'
    have haSs : aSeed k ≤ sI := haSa₁.trans ha₁s
    have hsTn : sI ≤ Tn k := (hst'.trans htσ).trans (hsT k)
    obtain ⟨hd, hsc, -⟩ := (Kh k).transport_at_stage_P6JW (haT k) (seedTrace k) haSs hsTn hes
      hsI _ z hAz h1 h2
    have hb9 := (Kh k).hgrid_of_isTracedRegion_P6BB hRk0 (hK r T) (htr' tt htt y' hy') hzy ha₁t
      (le_of_eq ha₁eq.symm) A₁ sI ha₁s hst'
    rw [hsc, ObservedHistory.stageMetric_castSucc_apply] at hb9
    refine ⟨hb9.trans (mul_le_mul_of_nonneg_right hQ9 hRk0.le), ?_⟩
    have h := hstay' sI ha₁s hst'
    rw [hd, ObservedHistory.stageMetric_castSucc_apply] at h
    exact h
  -- 数值（E1）（E2）
  have hE1 : 8 * T * Real.sqrt (cDist_P6DL2 C2 Q) ≤ Real.sqrt (R k) := by
    have := Real.sqrt_nonneg (R k)
    linarith
  have hE2 : 16 * Real.sqrt (cDist_P6DL2 C2 Q) + 2 ≤ L k := by linarith
  obtain ⟨ℓ, K, h, hℓ, hℓM, hℓr, hKℓ, hKr, hKC, hh, hbud, hLc, hLs, hdrift⟩ :=
    large_numerics_P6DL2 Ctime hC2 hQ1 hR1 hT hE1 hE2
  have hLk1 : 1 ≤ L k := by
    have := Real.sqrt_nonneg (cDist_P6DL2 C2 Q)
    linarith
  have haτ : (aSeed k : ℝ) ≤ τ := by linarith
  have hLτ : (σ k : ℝ) - L k ^ 2 / R k ≤ τ := by
    have h2T : 2 * T ≤ L k ^ 2 := by
      calc 2 * T ≤ L k := by linarith
        _ = 1 * L k := (one_mul _).symm
        _ ≤ L k * L k := mul_le_mul_of_nonneg_right hLk1 (by linarith)
        _ = L k ^ 2 := (sq _).symm
    have : 2 * T / R k ≤ L k ^ 2 / R k := div_le_div_of_nonneg_right h2T hRk0.le
    have e : 2 * T / R k = T / R k + T / R k := by ring
    linarith
  have hMτ : 1 ≤ 2 * (Q * R k) * τ := by
    have hQR : 1 ≤ Q * R k := one_le_mul_of_one_le_of_one_le hQ1 hR1
    have hτ1' : 1 ≤ τ := (hone k).trans haτ
    have := mul_le_mul hQR hτ1' zero_le_one (by linarith)
    linarith
  have hmain := (Kh k).hdistL_large_single_P6DL2 (haT k) (hsT k) (has k) (hsm k) (hclock k)
    (seedTrace k) (ha₀ k) (hpin k) (y k) hRk0 (hgood k) (i k) h1 h2 z (τ₀ := τ) (t := t) hτ3 hti.2
    haτ (by linarith [hti.2]) hLτ (by positivity) (mul_le_mul_of_nonneg_right hQ4 hRk0.le) hC2
    (fun s hs => (hpt s hs).1) hh hbud hℓ hℓM hℓr hKℓ hKr hKC hMτ hLc (by linarith)
    (by linarith) hLs (hfin k) (fun s hs => (hpt s hs).2) τ ⟨le_rfl, hτ2⟩
  refine hmain.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
  have hc8 : (0 : ℝ) ≤ 8 / ℓ := div_nonneg (by norm_num) hℓ.le
  calc 8 / ℓ * (t - τ) ≤ 8 / ℓ * (T / R k) := mul_le_mul_of_nonneg_left (by linarith) hc8
    _ ≤ 1 := hdrift

end Tower

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
