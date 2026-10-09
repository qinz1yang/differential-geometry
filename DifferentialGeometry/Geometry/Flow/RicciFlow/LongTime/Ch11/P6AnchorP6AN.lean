import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.CrossingDepthExtension2C_P6L2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.BallContainmentSameSlab_P6L2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistWFirstExitP6DW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistWFinalP6DW2

/-!
# Anchor₀：`hscalW` / `hscalW_final_P6M6` 的条件 producer（O-CH11-ANCHOR G1，后缀 `_P6AN`）

G0 判定 (b)（lead 18:3x 批准）：路线 (iii)（独立 κ / HI 紧性 = 深度驱动的 local flow limit）。
`hscalW`（`hdistW_of_firstExit_P6DW` 的残余前提）与其 final 版不再是独立分析叶子：
* **同 slab 换算**（树内已证，`scalar_le_on_ball_of_isTracedRegion_sameSlab_P6L2`）：traced region
  `(2D/√R, T/R, KR)` 于 `(σ, y)` ⇒ 同 slab 时刻 `s` 的 `B_s(x, ℓ)` 上 `R ≤ 9KR`（`ℓ e^{9KT} ≤ D/√R`）；
  **不用 ExitGuard**（Good 区只在 hwitC / hderivC 里出现）。
* `scalar_le_of_tracedRegion_P6AN`：逐 n 的常数形（`C ≥ 9K`、`C ≥ (e^{9KT}/D)²`、`C ≥ 1`）。
* `exists_const_eventually_of_subseq_P6AN`：子列 → `∀ᶠ n` 的反证 wrapper（`C_k = k + 1`，
  `Filter.extraction_forall_of_frequently`）。
* **`hscalW_of_depthExtendable_P6AN`**（PROVED）：遗传子列深度可延拓 `hdepth`
  （任意子列 `φ` 有再子列 `ψ`，`∀ T > 0, DepthExtendable Kh σ y R (φ ∘ ψ) T`）⇒ `hscalW`
  binder **逐字**。`_final_` 版 ⇒ `hscalW_final_P6M6`。
* `hdepth_of_driver_P6AN`（INTEGRATION-ONLY）：driver `exists_subseq_forall_depthExtendable_bcadC_P6L2`
  对 `Kh ∘ φ` 重标（全部前提对子列遗传）⇒ `hdepth`。
* **`hscalW_of_independent_P6AN`** / **`hscalW_final_of_independent_P6AN`**（PROVISIONAL）：
  driver 前提 ⇒ `hscalW` / `hscalW_final_P6M6`。具名分析 binder 只有两个：
  `hanchor0`（σ 切片 BCBD，owner = KSW 的 σ′ = 0 实例；**禁止**经
  `hanchor0_of_closure_data_window_q_P6M` ⇐ `hgrad_of_selection_sameSlab_Cg_P6CD`（hdistW ⇐ hscalW）
  生产——循环）与 `hbcadC`（= `ShallowBcadC_C11SH` T0，owner = SHALLOW / KSW；**禁止** P6S3 /
  hclosG / HU 路线）。其余为 supplies：`hsurvive / hextend`（extendAt 实例树内已证）、
  `hseed / hkappa / hpinch`、`hwitC / hderivC`（⇐ hgood + hdistC）。前提中无 HU、hgapJ、hclosG、
  CanonicalLateCore、hspine（D-20）。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn

namespace ObservedHistory

/-- **子列 → eventually 的反证 wrapper（`_P6AN`）**：若任意子列 `φ` 都有再子列 `ψ` 与门槛 `C₀`，使
`∀ᶠ i, ∀ C ≥ C₀, P (φ (ψ i)) C`，则 `∃ C ≥ 1, ∀ᶠ n, P n C`（反设取 `C_k = k + 1`）。 -/
theorem exists_const_eventually_of_subseq_P6AN {P : ℕ → ℝ → Prop}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ C₀ : ℝ,
      ∀ᶠ i in atTop, ∀ C : ℝ, C₀ ≤ C → P (φ (ψ i)) C) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop, P n C := by
  by_contra hcon
  have hfreq : ∀ k : ℕ, ∃ᶠ n in atTop, ¬ P n ((k : ℝ) + 1) := by
    intro k
    refine Filter.not_eventually.mp fun hev => hcon ⟨(k : ℝ) + 1, ?_, hev⟩
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  obtain ⟨φ, hφ, hbad⟩ := Filter.extraction_forall_of_frequently hfreq
  obtain ⟨ψ, hψ, C₀, hev⟩ := h φ hφ
  obtain ⟨N, hN⟩ := exists_nat_ge C₀
  obtain ⟨i, hi, hiN⟩ := (hev.and (eventually_ge_atTop N)).exists
  have hψi : (N : ℝ) ≤ (ψ i : ℝ) := by exact_mod_cast hiN.trans (hψ.id_le i)
  exact hbad (ψ i) (hi _ (by linarith))

/-- **逐 n 常数形（`_P6AN`）**：traced region `(2D/√R, T/R, KR)` 于 `(σ, y)`、`C ≥ max 1 (9K)`、
`C ≥ (e^{9KT}/D)²` ⇒ `x ∈ B_σ(y, D/√R)`、同 slab `s ∈ (σ − T/R, σ)`、`z ∈ B_s(x, 1/√(CR))` 上
`R(s, z) ≤ C R`（同 slab 换算 `scalar_le_on_ball_of_isTracedRegion_sameSlab_P6L2`，`ℓ = 1/√(CR)`）。 -/
theorem scalar_le_of_tracedRegion_P6AN (H : ObservedHistory.{u}) (σ : Icc (0 : ℝ) H.horizon)
    (y : (H.stageAt σ).Carrier) {R D T K C : ℝ} (hR : 0 < R) (hD : 0 < D) (hK : 0 ≤ K)
    (hC1 : 1 ≤ C) (hC9 : 9 * K ≤ C) (hCe : (Real.exp (9 * K * T) / D) ^ 2 ≤ C)
    (htr : H.isTracedRegion σ y (2 * D / Real.sqrt R) (T / R) (K * R))
    (x : (H.stageAt σ).Carrier)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage σ) σ) y (D / Real.sqrt R))
    (s : ℝ) (hs1 : (σ : ℝ) - T / R < s) (hs2 : s < σ) (hs3 : H.time (H.activeStage σ) < s)
    (z : (H.stageAt σ).Carrier)
    (hz : riemannianEDistOf (H.stageMetric (H.activeStage σ) s) x z <
      ENNReal.ofReal (1 / Real.sqrt (C * R))) :
    metricScalarAt (H.stageMetric (H.activeStage σ) s) z ≤ C * R := by
  have hC : 0 < C := lt_of_lt_of_le one_pos hC1
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hsC : 0 < Real.sqrt C := Real.sqrt_pos.mpr hC
  have hE0 : 0 < Real.exp (9 * K * T) := Real.exp_pos _
  have hexp : 9 * (K * R) * (T / R) = 9 * K * T := by
    field_simp
  have hsCR : Real.sqrt (C * R) = Real.sqrt C * Real.sqrt R := Real.sqrt_mul hC.le R
  have hED : Real.exp (9 * K * T) / D ≤ Real.sqrt C := by
    rw [← Real.sqrt_sq (div_nonneg hE0.le hD.le)]
    exact Real.sqrt_le_sqrt hCe
  have hE : Real.exp (9 * K * T) ≤ D * Real.sqrt C := by
    rw [mul_comm D]
    exact (div_le_iff₀ hD).mp hED
  have hrad : D / Real.sqrt R + Real.exp (9 * (K * R) * (T / R)) * (1 / Real.sqrt (C * R)) ≤
      2 * D / Real.sqrt R := by
    rw [hexp, hsCR]
    have h1 : Real.exp (9 * K * T) * (1 / (Real.sqrt C * Real.sqrt R)) ≤ D / Real.sqrt R := by
      rw [mul_one_div, div_le_div_iff₀ (mul_pos hsC hsR) hsR]
      calc Real.exp (9 * K * T) * Real.sqrt R ≤ D * Real.sqrt C * Real.sqrt R :=
            mul_le_mul_of_nonneg_right hE hsR.le
        _ = D * (Real.sqrt C * Real.sqrt R) := by ring
    have h2 : 2 * D / Real.sqrt R = D / Real.sqrt R + D / Real.sqrt R := by ring
    linarith
  have hb := H.scalar_le_on_ball_of_isTracedRegion_sameSlab_P6L2 σ y htr
    (mul_nonneg hK hR.le) (one_div_pos.mpr (Real.sqrt_pos.mpr (mul_pos hC hR))) hrad x hx s hs1
    hs3 hs2 z hz
  calc metricScalarAt (H.stageMetric (H.activeStage σ) s) z ≤ 9 * (K * R) := hb
    _ = (9 * K) * R := by ring
    _ ≤ C * R := mul_le_mul_of_nonneg_right hC9 hR.le

/-- **`hscalW ⇐ 遗传子列深度可延拓`（`_P6AN`，PROVED）**：结论 = `hdistW_of_firstExit_P6DW` 的 `hscalW`
binder 逐字。`hdepth`：任意子列 `φ` 有再子列 `ψ`，`∀ T > 0, DepthExtendable Kh σ y R (φ ∘ ψ) T`
（driver `exists_subseq_forall_depthExtendable_bcadC_P6L2` 的遗传形，见 `hdepth_of_driver_P6AN`）。
ExitGuard 前件不被使用（traced region 覆盖整个 `B_σ(y, 2D/√R)`）。 -/
theorem hscalW_of_depthExtendable_P6AN (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hdepth : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) x ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        ∀ z : ((Kh n).stageAt (σ n)).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n := by
  intro D T hD hT
  refine exists_const_eventually_of_subseq_P6AN fun φ hφ => ?_
  obtain ⟨ψ, hψ, hdep⟩ := hdepth φ hφ
  obtain ⟨K, hK, hev⟩ := hdep T hT (2 * D) (by positivity)
  refine ⟨ψ, hψ, max (max 1 (9 * K)) ((Real.exp (9 * K * T) / D) ^ 2), ?_⟩
  filter_upwards [hev] with i hi C hC
  intro x hx s hs1 hs2 hs3 _hguard z hz
  exact (Kh (φ (ψ i))).scalar_le_of_tracedRegion_P6AN (σ (φ (ψ i))) (y (φ (ψ i)))
    (hR (φ (ψ i))) hD hK ((le_max_left _ _).trans ((le_max_left _ _).trans hC))
    ((le_max_right _ _).trans ((le_max_left _ _).trans hC)) ((le_max_right _ _).trans hC)
    hi x hx s hs1 hs2 hs3 z hz

/-- **final 孪生的展开（`_P6AN`）**：stage 泛型 `hscalW` ⇒ `hscalW_final_P6M6`（`activeStage σ = last` 时
`time (activeStage σ) = time last`）。 -/
theorem hscalW_final_of_hscalW_P6AN (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
    (hscalW : ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) x ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        ∀ z : ((Kh n).stageAt (σ n)).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n) :
    ObservedHistory.hscalW_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L := by
  intro D T hD hT
  obtain ⟨C, hC, hev⟩ := hscalW D T hD hT
  refine ⟨C, hC, hev.mono fun n hn hfin x hx s hs1 hs2 hs3 hg z hz => ?_⟩
  have hs3' : (Kh n).time ((Kh n).activeStage (σ n)) < s := by
    rw [hfin]
    exact hs3
  exact hn x hx s hs1 hs2 hs3' hg z hz

/-- **`hscalW_final_P6M6` ⇐ 遗传子列深度可延拓（`_P6AN`，PROVED）**。 -/
theorem hscalW_final_of_depthExtendable_P6AN (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hdepth : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T) :
    ObservedHistory.hscalW_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L :=
  hscalW_final_of_hscalW_P6AN Kh Tn aSeed σ haT hsT has pT seedTrace y R L
    (hscalW_of_depthExtendable_P6AN Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR hdepth)

/-- **driver 子列重标（`_P6AN`，INTEGRATION-ONLY）**：`exists_subseq_forall_depthExtendable_bcadC_P6L2`
的前提（对 `Kh σ y R` 陈述，逐字）对任意子列遗传，故对 `Kh ∘ φ` 应用 driver 得再子列 `ψ`，
`DepthExtendable (Kh ∘ φ) … ψ ≡ DepthExtendable Kh σ y R (φ ∘ ψ)`（定义等）。driver 里子列变量 `σ`
改名 `χ`（`σ` 已是基点时刻）。 -/
theorem hdepth_of_driver_P6AN (Kh : ℕ → ObservedHistory.{u})
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop)
    {Cst : ℝ≥0}
    (hsurvive : ∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (∀ z ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (A / Real.sqrt (R n)),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) z ≤ Q * R n) →
        (Kh n).isTracedRegion (σ n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) z ≤ Q * R n)
    (hextend : ∀ χ : ℕ → ℕ, StrictMono χ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Kh σ y R χ T) →
      (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((Kh (χ i)).stageMetric
          ((Kh (χ i)).activeStage (σ (χ i))) (σ (χ i))) (y (χ i))
          (A / Real.sqrt (R (χ i))),
      ∀ (w : Icc (0 : ℝ) (Kh (χ i)).horizon),
        (w : ℝ) = σ (χ i) - T' / R (χ i) →
      ∀ (hwt : w ≤ σ (χ i))
        (Bt : BackwardPointTrace (Kh (χ i)) ((Kh (χ i)).activeStage w)
          ((Kh (χ i)).activeStage (σ (χ i)))
          ((Kh (χ i)).activeStage_mono hwt) x),
        metricScalarAt ((Kh (χ i)).stageMetric ((Kh (χ i)).activeStage w) w)
          (Bt.point ((Kh (χ i)).activeStage w) le_rfl
            ((Kh (χ i)).activeStage_mono hwt)) ≤
          M * R (χ i)) →
      DepthExtendable Kh σ y R χ (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1))))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'')
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))))
    {ε : ℝ} (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u}) {C1s C2s Cs : ℝ}
    {qs : ℕ → ℝ} (hqs : ∀ n, qs n ≤ Cs * R n)
    (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε)
    {Ctime : ℝ≥0} {Cq : ℝ} {qcan : ℕ → ℝ} (hqcan : ∀ n, qcan n ≤ Cq * R n)
    (hderivC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qcan n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctime * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2)
    (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (K * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) :
    ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T := by
  intro φ hφ
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  obtain ⟨ψ, hψ, hdep⟩ := ObservedHistory.exists_subseq_forall_depthExtendable_bcadC_P6L2
    (fun n => Kh (φ n)) (fun n => σ (φ n)) (fun n => y (φ n)) (fun n => R (φ n))
    (fun n => hR (φ n)) (hRlim.comp hφt)
    (fun A T Q hA hT hQ hQT => by
      obtain ⟨K, hK, hev⟩ := hsurvive A T Q hA hT hQ hQT
      exact ⟨K, hK, hφt.eventually hev⟩)
    (fun A hA => by
      obtain ⟨Q, hQ, hev⟩ := hanchor0 A hA
      exact ⟨Q, hQ, hφt.eventually hev⟩)
    (fun χ hχ Tstar M hT hM hdep hanc => hextend (φ ∘ χ) (hφ.comp hχ) Tstar M hT hM hdep hanc)
    hr₀ hw (hφt.eventually hseed) hκ (fun n => ρnc (φ n)) (hradii.comp hφt)
    (fun D T hD hT => hφt.eventually (hkappa D T hD hT)) hPhi
    (fun D T hD hT => hφt.eventually (hpinch D T hD hT)) hε hεX hεN (qs := fun n => qs (φ n))
    (fun n => hqs (φ n)) (fun φ' hφ' => hwitC (φ ∘ φ') (hφ.comp hφ'))
    (qcan := fun n => qcan (φ n)) (fun n => hqcan (φ n))
    (fun φ' hφ' => hderivC (φ ∘ φ') (hφ.comp hφ'))
    (fun A Dd hA hDd => by
      obtain ⟨C, hC⟩ := hbcadC A Dd hA hDd
      exact ⟨C, fun φ' hφ' => hC (φ ∘ φ') (hφ.comp hφ')⟩)
  exact ⟨ψ, hψ, fun T hT => hdep T hT⟩

/-- **`hscalW_of_independent_P6AN`（Anchor₀ event 版，`_P6AN`，PROVISIONAL）**：结论 = `hscalW` binder 逐字。
前提 = driver `exists_subseq_forall_depthExtendable_bcadC_P6L2` 的前提（对 `Kh σ y R`）。具名分析 binder：
`hanchor0`（σ 切片 BCBD，owner KSW σ′ = 0；禁 hgrad / hdistW 循环路线）、`hbcadC`（= ShallowBcadC T0，
owner SHALLOW / KSW；禁 P6S3 / HU 路线）；其余 supplies。 -/
theorem hscalW_of_independent_P6AN (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop)
    {Cst : ℝ≥0}
    (hsurvive : ∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (∀ z ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (A / Real.sqrt (R n)),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) z ≤ Q * R n) →
        (Kh n).isTracedRegion (σ n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) z ≤ Q * R n)
    (hextend : ∀ χ : ℕ → ℕ, StrictMono χ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Kh σ y R χ T) →
      (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((Kh (χ i)).stageMetric
          ((Kh (χ i)).activeStage (σ (χ i))) (σ (χ i))) (y (χ i))
          (A / Real.sqrt (R (χ i))),
      ∀ (w : Icc (0 : ℝ) (Kh (χ i)).horizon),
        (w : ℝ) = σ (χ i) - T' / R (χ i) →
      ∀ (hwt : w ≤ σ (χ i))
        (Bt : BackwardPointTrace (Kh (χ i)) ((Kh (χ i)).activeStage w)
          ((Kh (χ i)).activeStage (σ (χ i)))
          ((Kh (χ i)).activeStage_mono hwt) x),
        metricScalarAt ((Kh (χ i)).stageMetric ((Kh (χ i)).activeStage w) w)
          (Bt.point ((Kh (χ i)).activeStage w) le_rfl
            ((Kh (χ i)).activeStage_mono hwt)) ≤
          M * R (χ i)) →
      DepthExtendable Kh σ y R χ (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1))))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'')
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))))
    {ε : ℝ} (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u}) {C1s C2s Cs : ℝ}
    {qs : ℕ → ℝ} (hqs : ∀ n, qs n ≤ Cs * R n)
    (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε)
    {Ctime : ℝ≥0} {Cq : ℝ} {qcan : ℕ → ℝ} (hqcan : ∀ n, qcan n ≤ Cq * R n)
    (hderivC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qcan n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctime * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2)
    (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (K * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) x ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        ∀ z : ((Kh n).stageAt (σ n)).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n :=
  hscalW_of_depthExtendable_P6AN Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR
    (hdepth_of_driver_P6AN Kh σ y R hR hRlim hsurvive hanchor0 hextend hr₀ hw hseed hκ ρnc hradii
      hkappa hPhi hpinch hε hεX hεN hqs hwitC hqcan hderivC hbcadC)

/-- **`hscalW_final_of_independent_P6AN`（Anchor₀ final 孪生，`_P6AN`，PROVISIONAL）**：结论 =
`hscalW_final_P6M6`；前提同 `hscalW_of_independent_P6AN`（driver 与同 slab 换算都是 stage 泛型）。 -/
theorem hscalW_final_of_independent_P6AN (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRlim : Tendsto R atTop atTop)
    {Cst : ℝ≥0}
    (hsurvive : ∀ A T Q : ℝ, 0 < A → 0 < T → 2 ≤ Q → 4 * (Cst : ℝ) * Q * T ≤ 1 →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ n in atTop,
        (∀ z ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (A / Real.sqrt (R n)),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) z ≤ Q * R n) →
        (Kh n).isTracedRegion (σ n) (y n) (A / Real.sqrt (R n)) (T / R n) (K * R n))
    (hanchor0 : ∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) z ≤ Q * R n)
    (hextend : ∀ χ : ℕ → ℕ, StrictMono χ → ∀ Tstar M : ℝ, 0 < Tstar → 0 ≤ M →
      (∀ T : ℝ, 0 < T → T < Tstar → DepthExtendable Kh σ y R χ T) →
      (∀ T' : ℝ, 0 < T' → T' < Tstar → ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ x ∈ riemannianBallOf ((Kh (χ i)).stageMetric
          ((Kh (χ i)).activeStage (σ (χ i))) (σ (χ i))) (y (χ i))
          (A / Real.sqrt (R (χ i))),
      ∀ (w : Icc (0 : ℝ) (Kh (χ i)).horizon),
        (w : ℝ) = σ (χ i) - T' / R (χ i) →
      ∀ (hwt : w ≤ σ (χ i))
        (Bt : BackwardPointTrace (Kh (χ i)) ((Kh (χ i)).activeStage w)
          ((Kh (χ i)).activeStage (σ (χ i)))
          ((Kh (χ i)).activeStage_mono hwt) x),
        metricScalarAt ((Kh (χ i)).stageMetric ((Kh (χ i)).activeStage w) w)
          (Bt.point ((Kh (χ i)).activeStage w) le_rfl
            ((Kh (χ i)).activeStage_mono hwt)) ≤
          M * R (χ i)) →
      DepthExtendable Kh σ y R χ (Tstar + 1 / (32 * ((Cst : ℝ) + 1) * (M + 1))))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
        ENNReal.ofReal (w * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((Kh n).stageAt (σ n)).Carrier
            ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
              (r₀ / Real.sqrt (R n))))
    {κ : ℝ} (hκ : 0 < κ) (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'')
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          curvatureOperatorLowerBoundAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
            (metricAlgebraicCurvatureTensorAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Phi (metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))))
    {ε : ℝ} (hε : 0 < ε) (hεX : ε ≤ crossingWindowNeckAccuracy.{u})
    (hεN : ε ≤ crossingNeckAccuracy.{u}) {C1s C2s Cs : ℝ}
    {qs : ℕ → ℝ} (hqs : ∀ n, qs n ≤ Cs * R n)
    (hwitC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qs n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) ε C1s C2s
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
            Wt.capTubeHasNeckChart ε)
    {Ctime : ℝ≥0} {Cq : ℝ} {qcan : ℕ → ℝ} (hqcan : ∀ n, qcan n ≤ Cq * R n)
    (hderivC : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T K : ℝ, 0 < D → 0 < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
          (T / R n) (K * R n)) → ∀ᶠ n in map φ atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
          qcan n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
          |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
            (Iic (v : ℝ)) v| ≤
            Ctime * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2)
    (hbcadC : ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, ∀ φ : ℕ → ℕ, StrictMono φ →
        ∀ σ' : ℝ, σ' < 0 → ∀ Dw : ℝ, 0 < Dw → ∀ T K : ℝ, -σ' < T → 0 ≤ K →
        (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * Dw / Real.sqrt (R n))
          (T / R n) (K * R n)) →
        ∀ᶠ n in map φ atTop,
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ x₂ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (v : ℝ) = σ n + σ' / R n →
        ∀ (tr₁ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₁)
          (tr₂ : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
            ((Kh n).activeStage_mono hvt) x₂),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ A * R n →
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₁.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt))
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) <
            ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr₂.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ≤ C * R n) :
    ObservedHistory.hscalW_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L :=
  hscalW_final_of_depthExtendable_P6AN Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR
    (hdepth_of_driver_P6AN Kh σ y R hR hRlim hsurvive hanchor0 hextend hr₀ hw hseed hκ ρnc hradii
      hkappa hPhi hpinch hε hεX hεN hqs hwitC hqcan hderivC hbcadC)

/-- **consumer（event，`_P6AN`）**：`hdepth` 经 `hscalW_of_depthExtendable_P6AN` 喂
`hdistW_of_firstExit_P6DW` 的 `hscalW` 槽（类型由 elaboration 核对）。 -/
example (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (r : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (hσev : ∀ n, ∃ e : Fin (Kh n).eventCount, (Kh n).activeStage (σ n) = e.castSucc)
    (hdepth : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T) :=
  ObservedHistory.hdistW_of_firstExit_P6DW Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR r hL
    hsmall hclock hRr hwin ha₀ hpin hσev
    (hscalW_of_depthExtendable_P6AN Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR hdepth)

/-- **consumer（final，`_P6AN`）**：`hdepth` 经 `hscalW_final_of_depthExtendable_P6AN` 喂
`hdistW_of_firstExit_final_P6DW2` 的 `hscalW` 槽。 -/
example (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (r : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (hσfin : ∀ n, (Kh n).activeStage (σ n) = Fin.last (Kh n).eventCount)
    (hσlt : ∀ n, (σ n : ℝ) < (Kh n).horizon)
    (hdepth : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ T : ℝ, 0 < T → DepthExtendable Kh σ y R (φ ∘ ψ) T) :=
  ObservedHistory.hdistW_of_firstExit_final_P6DW2 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR r
    hL hsmall hclock hRr hwin ha₀ hpin hσfin hσlt
    (hscalW_final_of_depthExtendable_P6AN Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR hdepth)

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
