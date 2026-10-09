import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceAfterEventC11X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialCurvatureLifespan
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionOrCapWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionDepthInduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionTimeZeroScalarBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionMaximalDepth

/-!
# O-CH11-FIX3 port of astra `BirthTimeZeroBound`（`PortC11P`）

来源：donor `DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Topology/BirthTimeZeroBound.lean`
（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。donor 文本在本树 elaboration 失败（EXT1 / EXT2 记为
REF）：`IsOrderedRing ?m` stuck ×3、`generalize` result not type correct ×2，修掉后暴露 1 处
implicit 参数无法推断。

本 port 的修补（全部 elaboration 层面；no statement / definition / proof idea altered）：
* import：`BoundedCurvatureAtDistanceAfterEvent` → `BoundedCurvatureAtDistanceAfterEventC11X`
  （EXT2 extension，donor 新增的 `…_of_birth_metric_comparison` 等在那里；同 EXT1 的 port）；
* 三处 `linarith` / `nlinarith` 的 hint `Nat.cast_nonneg n` → `Nat.cast_nonneg (α := ℝ) n`
  （无 expected type 时目标类型是 metavariable，`IsOrderedRing ?m` 卡住）；
* 两处 `revert …` 之后、`generalize H.toHistory.activeStage v = k` 之前加
  `dsimp only [ObservedHistory.stageAt]`（`z : (stageAt v).Carrier` 里的 `activeStage v`
  藏在 abbrev 里，`generalize` 的 kabstract 看不到，抽象后不 type correct）；
* `exists_birth_persistence_inputs_eventually` 的调用补 `(ρb := ρb)`（该 private 定理的
  implicit `ρb` 不出现在陈述里，调用处无法推断；传入 section 自己的 `ρb`）。

遗留 donor warning（SOFT）：l.57 binder `ρb` 未被引用（改名或删除会改陈述，保留）。
原路径 `BirthTimeZeroBound` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

private theorem eventually_nat_add_one_ge (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) + 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge c
  filter_upwards [eventually_ge_atTop N] with n hn
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

private theorem eventually_one_div_nat_add_one_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ c := by
  filter_upwards [eventually_nat_add_one_ge (1 / c)] with n hn
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hc] at hn
  linarith

/-- At a stage birth there is no outgoing open time interval on which a
derivative hypothesis has to be supplied. Incoming intervals are unaffected. -/
theorem derivativeBound_inputs_at_birth (H : RetainedCoreHistory.{u})
    {t : Icc (0 : ℝ) H.toHistory.horizon}
    (hbirth : H.time (H.toHistory.activeStage t) = (t : ℝ)) (Ctime : ℝ≥0) (q : ℝ) :
    (∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime q t) ∧
    (∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime q t) := by
  constructor
  · intro j hj x v hv _
    have he : H.time j.castSucc = (t : ℝ) := by rw [hj, hbirth]
    exact False.elim (by have := hv.1; have := hv.2; linarith)
  · intro h hk x v hv _
    have he : H.time (Fin.last H.eventCount) = (t : ℝ) := by rw [← hk, hbirth]
    exact False.elim (by have := hv.1; have := hv.2; linarith)

private theorem exists_birth_persistence_inputs_eventually
    {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
    {D q : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
    {H : ℕ → RetainedCoreHistory.{u}}
    {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
    (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀ (H n).toHistory))
    (hq : ∀ n : ℕ, (n : ℝ) + 1 ≤ q n)
    (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
      D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
    (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * q n ≤ ((records n i).static b).neck.scale) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
      (∀ n x, InFixedHamiltonIveyRegion ((H n).initialMetric 0) a₀ x ∧
        -3 / a₀ ≤ metricScalarAt ((H n).initialMetric 0) x) ∧
      ∀ (Rw ζ₀ δ₀ Cbirth : ℝ) (m₀ : ℕ), 0 < ζ₀ → 0 < δ₀ → 0 < Cbirth → ∀ᶠ n in atTop,
        δb n ≤ δ₀ ∧ Rw ≤ (p₀ n).modelRadius ∧ m₀ ≤ (p₀ n).modelOrder ∧
        (p₀ n).modelAccuracy ≤ ζ₀ ∧
        (∀ i b, q n ≤ Cbirth * ((records n i).static b).neck.scale ∧
          1 ≤ a₀ * ((records n i).static b).neck.scale) := by
  obtain ⟨a₀, ha₀, hHI⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀
  refine ⟨a₀, ha₀, fun n x => ?_, ?_⟩
  · obtain ⟨I⟩ := hinit n
    exact ⟨(hHI _ I).1 x, (hHI _ I).2 x⟩
  intro Rw ζ₀ δ₀ Cbirth m₀ hζ₀ hδ₀ hC
  filter_upwards [eventually_one_div_nat_add_one_le hδ₀,
    eventually_one_div_nat_add_one_le hζ₀, eventually_nat_add_one_ge Rw,
    eventually_ge_atTop m₀, eventually_nat_add_one_ge (1 / Cbirth),
    eventually_nat_add_one_ge (1 / a₀)] with n hδ hζ hR hm hCb ha
  obtain ⟨hacc, hD, hrad, hord, hdel⟩ := hpar n
  have hq0 : 0 < q n := lt_of_lt_of_le (by positivity) (hq n)
  refine ⟨hdel.trans hδ, hR.trans (hD.trans hrad), le_trans hm (by omega), hacc.trans hζ,
    fun i b => ?_⟩
  have hs := hscale n i b
  have hCb' : 1 ≤ Cbirth * ((n : ℝ) + 1) := by
    rw [div_le_iff₀ hC] at hCb
    linarith
  have ha' : 1 ≤ a₀ * ((n : ℝ) + 1) := by
    rw [div_le_iff₀ ha₀] at ha
    linarith
  constructor
  · calc q n ≤ Cbirth * ((n : ℝ) + 1) * q n := le_mul_of_one_le_left hq0.le hCb'
      _ = Cbirth * (((n : ℝ) + 1) * q n) := by ring
      _ ≤ Cbirth * ((records n i).static b).neck.scale := mul_le_mul_of_nonneg_left hs hC.le
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hsq : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) * q n := by nlinarith [hq n]
    calc (1 : ℝ) ≤ a₀ * ((n : ℝ) + 1) := ha'
      _ ≤ a₀ * (((n : ℝ) + 1) * q n) := mul_le_mul_of_nonneg_left hsq ha₀.le
      _ ≤ a₀ * ((records n i).static b).neck.scale := mul_le_mul_of_nonneg_left hs ha₀.le

variable {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
  {ε C1 C2 κ ρ : ℝ} {Ctime Cgrad : ℝ≥0} {phi : ℝ → ℝ}
  {D θcap q R : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
  {H : ℕ → RetainedCoreHistory.{u}}
  {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
  {t : ∀ n, Icc (0 : ℝ) (H n).toHistory.horizon}
  {y : ∀ n, ((H n).toHistory.stageAt (t n)).Carrier}
  (hεcone : ε ≤ coneAccuracy) (hκ : 0 < κ) (hρ : 0 < ρ)
  (hphi : Perelman.AdmissiblePinchingFunction phi)
  (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀ (H n).toHistory))
  (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
  (hq : ∀ n : ℕ, (n : ℝ) + 1 ≤ q n ∧ q n < R n)
  (hRscalar : ∀ n, R n = metricScalarAt
    ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) (y n))
  (hbirth : ∀ n, (H n).time ((H n).toHistory.activeStage (t n)) = (t n : ℝ))
  (hne : ∀ n, (H n).toHistory.activeStage (t n) ≠ 0)
  (hRt : Tendsto (fun n => R n * (t n : ℝ)) atTop atTop)
  (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
    D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
  (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * q n ≤ ((records n i).static b).neck.scale)
  (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n)
  (hpinch : ∀ n, (H n).EventSlabsPinched phi)
  (hlast : ∀ n, (H n).toHistory.activeStage (t n) = Fin.last (H n).eventCount →
    ∃ h : (H n).time (Fin.last (H n).eventCount) < (H n).horizon,
      Perelman.PhiAlmostNonnegative ((H n).finalSlab h).flow
        (Icc ((H n).time (Fin.last (H n).eventCount)) (H n).horizon) phi)
  (hslabs : ∀ n,
    (H n).EventSlabsSpatiallyCanonical ε C1 C2 (q n) ((H n).toHistory.activeStage (t n)) ∧
    (H n).EventSlabsDerivative Ctime (q n) ((H n).toHistory.activeStage (t n)) ∧
    (H n).EventSlabsGradient Cgrad (q n) ((H n).toHistory.activeStage (t n)))
  (hnc : ∀ n, (H n).NoncollapsedBefore κ ρ (t n))
  (hnot : ∀ n, ¬ (H n).CapWindowPoint (records n) ((H n).toHistory.activeStage (t n))
    (y n) (t n) (D n) (θcap n))

private theorem birth_scalar_pos (n : ℕ) (hq : (n : ℝ) + 1 ≤ q n ∧ q n < R n) :
    0 < R n := (lt_of_lt_of_le (by positivity) hq.1).trans hq.2

include hεcone hκ hρ hphi hrec hq hRscalar hbirth hne hRt hpar hθcap hpinch hslabs hnc hnot in
/-- The actual post-event metric supplies the starting ball estimate. This
uses incoming estimates and noncollapse on this history, with its original
cutoff records; it does not replace the history or the postmetric. -/
theorem eventually_scalar_le_on_normalized_ball_at_birth (A : ℝ) (hA : 0 < A) :
    ∃ Q : ℝ, 1 ≤ Q ∧ ∀ᶠ n in atTop,
      ∀ z ∈ riemannianBallOf
          ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) (y n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) z ≤
          Q * R n := by
  obtain ⟨Q, Λ, Dcap, Rrad, ζ₀, hQ, hΛ, -, -, hζ₀, hmain⟩ :=
    exists_scalar_bound_at_distance_of_not_capWindowPoint_at_birth.{u}
      hεcone κ C1 C2 hκ Ctime Cgrad hphi A hA 1 (1 / 2) (by norm_num)
  have hRlim : Tendsto R atTop atTop := tendsto_atTop_mono
    (fun n => ((hq n).1.trans_lt (hq n).2).le)
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hRsq : Tendsto (fun n => ρ * Real.sqrt (R n)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp hRlim).const_mul_atTop hρ
  refine ⟨Q, hQ, ?_⟩
  filter_upwards [hRlim.eventually_ge_atTop Λ, hRt.eventually_ge_atTop Λ,
    hRsq.eventually_ge_atTop Λ, eventually_nat_add_one_ge Rrad,
    eventually_nat_add_one_ge Dcap, eventually_one_div_nat_add_one_le hζ₀]
    with n hRn hRtn hρn hRrad hDcap hacc
  have hmetric : (H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n) =
      (H n).initialMetric ((H n).toHistory.activeStage (t n)) := by
    rw [← hbirth n]
    exact (H n).toHistory.stageMetric_initial _
  have hscalar : R n = metricScalarAt
      ((H n).initialMetric ((H n).toHistory.activeStage (t n))) (y n) :=
    (hRscalar n).trans (congrArg (fun g => metricScalarAt g (y n)) hmetric)
  have hθn : (1 / 2 : ℝ) ≤ θcap n := by
    have : 1 / ((n : ℝ) + 2) ≤ (1 / 2 : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    linarith [hθcap n]
  have hbound : ∀ k : Fin ((H n).eventCount + 1), k ≠ 0 →
      ∀ z : ((H n).stage k).Carrier,
      0 < q n → q n ≤ metricScalarAt ((H n).initialMetric k) z →
      Λ ≤ metricScalarAt ((H n).initialMetric k) z →
      Λ ≤ metricScalarAt ((H n).initialMetric k) z * (H n).time k →
      (H n).EventSlabsSpatiallyCanonical ε C1 C2 (q n) k →
      (H n).EventSlabsDerivative Ctime (q n) k →
      (H n).EventSlabsGradient Cgrad (q n) k →
      (H n).NoncollapsedBefore κ ρ ((H n).time k) →
      Λ ≤ ρ * Real.sqrt (metricScalarAt ((H n).initialMetric k) z) →
      ¬ (H n).CapWindowPoint (records n) k z ((H n).time k) Dcap (1 / 2) →
      ∀ w ∈ riemannianBallOf ((H n).initialMetric k) z
          (A / Real.sqrt (metricScalarAt ((H n).initialMetric k) z)),
        metricScalarAt ((H n).initialMetric k) w ≤
          Q * metricScalarAt ((H n).initialMetric k) z := by
    intro k hk z hq0 hqz hΛz hΛt hsp hder hgrad hnc' hρ' hnot'
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hk
    simpa only [one_mul] using hmain (H n) (p₀ n) (δb n) (ρb n) (records n) (hrec n)
      (hRrad.trans ((hpar n).2.1.trans (hpar n).2.2.1))
      (by have := (hpar n).2.2.2.1; omega)
      ((hpar n).1.trans hacc) j z (q n) ρ hq0 (by simpa only [one_mul] using hqz)
      hΛz hΛt hsp hder hgrad (hpinch n) hnc' hρ' hnot'
  rw [hmetric, hscalar]
  apply hbound _ (hne n) (y n) (lt_of_lt_of_le (by positivity) (hq n).1)
    (hscalar ▸ (hq n).2.le) (hscalar ▸ hRn)
  · simpa only [hbirth n, ← hscalar] using hRtn
  · exact (hslabs n).1
  · exact (hslabs n).2.1
  · exact (hslabs n).2.2
  · simpa only [hbirth n] using hnc n
  · simpa only [← hscalar] using hρn
  · intro hc
    apply hnot n
    rw [hbirth n] at hc
    exact hc.mono (hDcap.trans (hpar n).2.1) hθn

include hphi hinit hrec hq hbirth hRt hpar hscale hθcap hpinch hlast hnot in
/-- A scalar bound on the birth ball gives a traced region for a short
backward depth. The required last-slab hypothesis refers to an actual later
observation of this same history; it is not automatic at a terminal birth. -/
theorem exists_eventually_isTracedRegion_at_birth_of_scalar_le_on_ball
    (hder : ∀ n, (H n).EventSlabsDerivative Ctime (q n) ((H n).toHistory.activeStage (t n)))
    {A T Q : ℝ}
    (hA : 0 < A) (hT : 0 < T) (hQ : 2 ≤ Q) (hstep : 2 * (Ctime : ℝ) * Q * T ≤ 1) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ᶠ n in atTop,
      (∀ z ∈ riemannianBallOf
          ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) (y n)
          (A / Real.sqrt (R n)),
        metricScalarAt ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) z ≤
          Q * R n) →
      (H n).toHistory.isTracedRegion (t n) (y n) (A / Real.sqrt (R n)) (T / R n) (K₀ * R n) := by
  obtain ⟨c, hc, hB⟩ := exists_isTracedRegion_or_capWindowPoint_at_scale.{u}
  have hφ0 := hphi.pos 0
  have hφ1 := hphi.pos 1
  have hTQ : 0 < 8 * T * Q := by positivity
  let θ₁ : ℝ := max (1 / 4) (1 - c / (8 * T * Q))
  have hθ₁ : θ₁ < 1 := max_lt (by norm_num) (by have := div_pos hc hTQ; linarith)
  have hΘ0 : 0 < (θ₁ + 1) / 2 := by
    have := le_max_left (1 / 4 : ℝ) (1 - c / (8 * T * Q))
    dsimp [θ₁]
    linarith
  obtain ⟨Cbirth, hCb, hB⟩ := hB ((θ₁ + 1) / 2) hΘ0 (by linarith) Ctime
  let Dcap : ℝ := 2 * StandardCap.transitionEnd + Real.sqrt (8 * Q) *
    Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0)) * Q * T) * A + 1
  have hDs : StandardCap.transitionEnd < Dcap := by
    have := StandardCap.transitionEnd_pos
    have : 0 ≤ Real.sqrt (8 * Q) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0)) * Q * T) * A := by positivity
    dsimp [Dcap]
    linarith
  obtain ⟨Rrad, -, m₀, -, ζ₀, δ₀, hζ₀, -, hδ₀, hB⟩ := hB Dcap hDs
  obtain ⟨a₀, -, hHI, hev⟩ := exists_birth_persistence_inputs_eventually (ρb := ρb)
    hinit (fun n => (hq n).1) hpar hscale
  have hθev : ∀ᶠ n : ℕ in atTop, θ₁ ≤ θcap n := by
    filter_upwards [eventually_one_div_nat_add_one_le (show 0 < 1 - θ₁ by linarith)] with n hn
    have hn' : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith [hθcap n]
  refine ⟨8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * Q, by positivity, ?_⟩
  filter_upwards [hev Rrad ζ₀ δ₀ Cbirth m₀ hζ₀ hδ₀ hCb,
    eventually_nat_add_one_ge Dcap, hθev, hRt.eventually_ge_atTop T]
    with n hn hDn hθn hRtn hball
  obtain ⟨hδn, hRn, hmn, hζn, hbirthscale⟩ := hn
  have hR0 : 0 < R n := birth_scalar_pos n (hq n)
  have hut0 : 0 ≤ (t n : ℝ) - T / R n := by
    rw [sub_nonneg, div_le_iff₀ hR0]
    linarith
  let uu : Icc (0 : ℝ) (H n).toHistory.horizon :=
    ⟨t n - T / R n, hut0, (sub_le_self _ (div_pos hT hR0).le).trans (t n).2.2⟩
  have hut : uu ≤ t n := sub_le_self _ (div_pos hT hR0).le
  have hd := (H n).derivativeBound_inputs_at_birth (hbirth n) Ctime (q n)
  have hscal := (H n).scalar_le_two_mul_along_backward_traces_of_scalar_le_on_ball
    hR0 (by linarith : 0 < Q) hstep (show (uu : ℝ) = t n - T / R n from rfl) hut
    (hder n) hd.1 hd.2 (by nlinarith [(hq n).2]) (y n) hball
  rcases hB (H n) (p₀ n) (δb n) (ρb n) (records n) (hrec n) hδn hRn hmn hζn
      (q n) a₀ (lt_of_lt_of_le (by positivity) (hq n).1)
      (fun x => (hHI n x).1) (fun x => (hHI n x).2)
      (fun i b => (hbirthscale i b).1) (fun i b => (hbirthscale i b).2)
      phi hphi (hpinch n) uu (t n) hut (hlast n) (hder n) hd.1 hd.2
      (y n) (R n) A T Q Dcap θ₁ hR0 hA hT
      (by nlinarith [(hq n).1, (hq n).2, Nat.cast_nonneg (α := ℝ) n]) rfl
      (le_max_left _ _) (le_max_right _ _) (by linarith) le_rfl hscal
      (by dsimp [Dcap]; linarith) with htr | hcw
  · simpa only [mul_assoc] using htr
  · exact False.elim ((hnot n) (hcw.mono (hDn.trans (hpar n).2.1) hθn))

include hεcone hκ hρ hphi hinit hrec hq hRscalar hbirth hne hRt hpar hscale hθcap hpinch
  hlast hslabs hnc hnot in
/-- Each radius has its own positive normalized backward depth. No common
depth is inferred from the radius-dependent initial scalar bounds. -/
theorem exists_depth_schedule_isTracedRegion_at_birth :
    ∃ τs : ℕ → ℝ, (∀ k, 0 < τs k) ∧ (∀ k, τs k ≤ 1 / 8) ∧
      ∀ k : ℕ, ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ᶠ n in atTop,
        (H n).toHistory.isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (R n))
          (τs k / R n) (K₀ * R n) := by
  choose Q hQ1 hQev using fun k : ℕ => eventually_scalar_le_on_normalized_ball_at_birth
    hεcone hκ hρ hphi hrec hq hRscalar hbirth hne hRt hpar hθcap hpinch hslabs hnc hnot
    ((k + 3 : ℕ) : ℝ) (by positivity)
  have hC0 : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
  refine ⟨fun k => 1 / (4 * ((Ctime : ℝ) + 1) * max (Q k) 2), fun k => by positivity,
    fun k => ?_, fun k => ?_⟩
  · have h2 := le_max_right (Q k) 2
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hQ2 := le_max_right (Q k) 2
  have hstep4 : 4 * (Ctime : ℝ) * max (Q k) 2 *
      (1 / (4 * ((Ctime : ℝ) + 1) * max (Q k) 2)) ≤ 1 := by
    rw [show 4 * (Ctime : ℝ) * max (Q k) 2 * (1 / (4 * ((Ctime : ℝ) + 1) * max (Q k) 2)) =
      (Ctime : ℝ) / ((Ctime : ℝ) + 1) by field_simp]
    rw [div_le_one (by positivity)]
    linarith
  have hstep : 2 * (Ctime : ℝ) * max (Q k) 2 *
      (1 / (4 * ((Ctime : ℝ) + 1) * max (Q k) 2)) ≤ 1 := by
    have : 0 ≤ (Ctime : ℝ) * max (Q k) 2 *
        (1 / (4 * ((Ctime : ℝ) + 1) * max (Q k) 2)) := by positivity
    nlinarith
  obtain ⟨K₀, hK₀, hev⟩ := exists_eventually_isTracedRegion_at_birth_of_scalar_le_on_ball
    hphi hinit hrec hq hbirth hRt hpar hscale hθcap hpinch hlast hnot
    (fun n => (hslabs n).2.1)
    (A := ((k + 3 : ℕ) : ℝ)) (by positivity) (by positivity) hQ2 hstep
  refine ⟨K₀, hK₀, ?_⟩
  filter_upwards [hev, hQev k] with n hn hQn
  exact hn fun z hz => (hQn z hz).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (birth_scalar_pos n (hq n)).le)

private theorem exists_spatialCanonicalWitness_before_birth
    (H : RetainedCoreHistory.{u}) {t : Icc (0 : ℝ) H.toHistory.horizon}
    (hbirth : H.time (H.toHistory.activeStage t) = (t : ℝ))
    {ε C1 C2 q : ℝ}
    (hslab : H.EventSlabsSpatiallyCanonical ε C1 C2 q (H.toHistory.activeStage t))
    (v : Icc (0 : ℝ) H.toHistory.horizon) (hv : (v : ℝ) < t)
    (hvk : H.time (H.toHistory.activeStage v) < v)
    (z : (H.toHistory.stageAt v).Carrier)
    (hq : q < metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) z) :
    ∃ W : Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalWitness
        (H.toHistory.stageMetric (H.toHistory.activeStage v) v) ε C1 C2 z,
      W.capTubeHasNeckChart ε := by
  have hk : H.toHistory.activeStage v < H.toHistory.activeStage t :=
    H.time_strictMono.lt_iff_lt.mp
      ((H.toHistory.activeStage_time_le v).trans_lt (by simpa only [hbirth] using hv))
  have hmem := H.toHistory.activeStage_mem v
  revert z hq
  dsimp only [ObservedHistory.stageAt]
  generalize H.toHistory.activeStage v = k at hk hvk hmem ⊢
  intro z hq
  cases k using Fin.lastCases with
  | last => exact False.elim ((not_lt_of_ge (Fin.le_last _)) hk)
  | cast j =>
    rw [ObservedHistory.stageMetric_castSucc_apply] at hq ⊢
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, mem_Ico] at hmem
    exact hslab j hk z v ⟨hvk, hmem.2⟩ hq

private theorem curvatureOperatorLowerBoundAt_before_of_eventSlabsPinched
    (H : RetainedCoreHistory.{u}) {t : Icc (0 : ℝ) H.toHistory.horizon}
    {phi : ℝ → ℝ} (hpinch : H.EventSlabsPinched phi)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (v : Icc (0 : ℝ) H.toHistory.horizon) (hv : v ≤ t)
    (z : (H.toHistory.stageAt v).Carrier) :
    curvatureOperatorLowerBoundAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) z
      (metricAlgebraicCurvatureTensorAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) z)
      (phi (metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v) z)) := by
  have hk := H.toHistory.activeStage_mono hv
  have hmem := H.toHistory.activeStage_mem v
  revert z
  dsimp only [ObservedHistory.stageAt]
  generalize H.toHistory.activeStage v = k at hk hmem ⊢
  intro z
  cases k using Fin.lastCases with
  | last =>
    obtain ⟨h, hp⟩ := hlast (le_antisymm (Fin.le_last _) hk)
    rw [ObservedHistory.stageMetric_last_of_lt (h := h)]
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last] at hmem
    exact hp v hmem z
  | cast j =>
    rw [ObservedHistory.stageMetric_castSucc_apply]
    simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] at hmem
    exact hpinch j v hmem z

include hεcone hκ hρ hphi hinit hrec hq hRscalar hbirth hne hRt hpar hscale hθcap hpinch
  hlast hslabs hnc hnot in
/-- The existing depth-schedule compactness theorem upgrades the actual birth
ball bounds to a single scalar constant on every normalized radius along a
subsequence. Prior canonical witnesses are used only at strictly earlier
regular times. The rescaled time gap is exactly zero. -/
theorem exists_subseq_scalar_le_on_normalized_balls_at_birth
    (hε : 0 < ε) (hεX : ε ≤ crossingNeckAccuracy.{u}) (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      ∀ z ∈ riemannianBallOf
          ((H (σ (ψ i))).toHistory.stageMetric
            ((H (σ (ψ i))).toHistory.activeStage (t (σ (ψ i)))) (t (σ (ψ i))))
          (y (σ (ψ i))) (A / Real.sqrt (R (σ (ψ i)))),
        metricScalarAt ((H (σ (ψ i))).toHistory.stageMetric
          ((H (σ (ψ i))).toHistory.activeStage (t (σ (ψ i)))) (t (σ (ψ i)))) z ≤
          C₀ * R (σ (ψ i)) := by
  obtain ⟨τs, hτs, hτs8, htr⟩ := exists_depth_schedule_isTracedRegion_at_birth
    hεcone hκ hρ hphi hinit hrec hq hRscalar hbirth hne hRt hpar hscale hθcap hpinch
    hlast hslabs hnc hnot
  have hRlim : Tendsto R atTop atTop := tendsto_atTop_mono
    (fun n => ((hq n).1.trans_lt (hq n).2).le)
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hgap : Tendsto (fun n => R (σ n) * ((t (σ n) : ℝ) - (t (σ n) : ℝ)))
      atTop (𝓝 0) := by simpa only [sub_self, mul_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact ObservedHistory.exists_subseq_scalar_le_on_normalized_balls_of_depth_schedule
    (fun n => (H (σ n)).toHistory) (fun n => t (σ n)) (fun n => y (σ n)) (fun n => R (σ n))
    (fun n => birth_scalar_pos (σ n) (hq (σ n))) (hRlim.comp hσ.tendsto_atTop)
    τs hτs (fun k => (hτs8 k).trans (by norm_num))
    (fun k => (htr k).imp fun _ hK => ⟨hK.1, hσ.tendsto_atTop.eventually hK.2⟩)
    hκ hρ (t₀ := fun n => (t (σ n) : ℝ)) hgap
    (fun n v z r hv hr hb => hnc (σ n) v z r hv.le hr hb) hphi
    (fun n v hv z => curvatureOperatorLowerBoundAt_before_of_eventSlabsPinched
      (H (σ n)) (hpinch (σ n)) (hlast (σ n)) v hv z)
    hε hεX (Cq := 1) (qs := fun n => q (σ n))
    (fun n => by simpa only [mul_one] using (hq (σ n)).2.le)
    (fun n v hv hvk z hz => exists_spatialCanonicalWitness_before_birth
      (H (σ n)) (hbirth (σ n)) (hslabs (σ n)).1 v hv hvk z hz)

include hεcone hκ hρ hphi hinit hrec hq hRscalar hbirth hne hRt hpar hscale hθcap hpinch
  hlast hslabs hnc hnot in
/-- A uniform positive depth follows only after the depth-schedule compactness
upgrade. This is the birth analogue of the initial positive-depth input to
the maximal-depth argument; it does not assert arbitrary backward depth. -/
theorem exists_subseq_depthExtendable_pos_at_birth
    (hε : 0 < ε) (hεX : ε ≤ crossingNeckAccuracy.{u}) (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ T₀ : ℝ, 0 < T₀ ∧
      ObservedHistory.DepthExtendable (fun n => (H n).toHistory) t y R (σ ∘ ψ) T₀ := by
  obtain ⟨ψ, hψ, C₀, -, hball⟩ := exists_subseq_scalar_le_on_normalized_balls_at_birth
    hεcone hκ hρ hphi hinit hrec hq hRscalar hbirth hne hRt hpar hscale hθcap hpinch
    hlast hslabs hnc hnot hε hεX σ hσ
  have hC0 : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
  refine ⟨ψ, hψ, 1 / (4 * ((Ctime : ℝ) + 1) * max C₀ 2), by positivity, fun A hA => ?_⟩
  have hQ2 := le_max_right C₀ 2
  have hstep4 : 4 * (Ctime : ℝ) * max C₀ 2 *
      (1 / (4 * ((Ctime : ℝ) + 1) * max C₀ 2)) ≤ 1 := by
    rw [show 4 * (Ctime : ℝ) * max C₀ 2 * (1 / (4 * ((Ctime : ℝ) + 1) * max C₀ 2)) =
      (Ctime : ℝ) / ((Ctime : ℝ) + 1) by field_simp]
    rw [div_le_one (by positivity)]
    linarith
  have hstep : 2 * (Ctime : ℝ) * max C₀ 2 *
      (1 / (4 * ((Ctime : ℝ) + 1) * max C₀ 2)) ≤ 1 := by
    have : 0 ≤ (Ctime : ℝ) * max C₀ 2 *
        (1 / (4 * ((Ctime : ℝ) + 1) * max C₀ 2)) := by positivity
    nlinarith
  obtain ⟨K₀, hK₀, hev⟩ := exists_eventually_isTracedRegion_at_birth_of_scalar_le_on_ball
    hphi hinit hrec hq hbirth hRt hpar hscale hθcap hpinch hlast hnot
    (fun n => (hslabs n).2.1)
    (A := A) hA (by positivity) hQ2 hstep
  refine ⟨K₀, hK₀, ?_⟩
  filter_upwards [hball A hA, (hσ.comp hψ).tendsto_atTop.eventually hev] with i hi hn
  have hR0 := birth_scalar_pos (σ (ψ i)) (hq (σ (ψ i)))
  exact hn fun z hz => (hi z hz).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hR0.le)

include hinit hq hbirth hne records in
/-- The common original metric supplies a positive lower bound on every
nonzero surgery birth, before any history or fine cutoff accuracy is chosen.
Hence diverging normalization scales also diverge after multiplication by the
actual birth times. Only the singular endpoints of the actual records are used. -/
theorem tendsto_scale_mul_birth_time_atTop_of_initialIdentification :
    Tendsto (fun n => R n * (t n : ℝ)) atTop atTop := by
  obtain ⟨a, ha, htime⟩ :=
    exists_pos_le_singular_incoming_time_of_initialIdentification P₀ g₀
  have hbirthfloor : ∀ n, a ≤ (t n : ℝ) := by
    intro n
    obtain ⟨I⟩ := hinit n
    obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr (hne n)
    have hf := htime (H n).toHistory I (fun j => (records n j).singular)
      i.castSucc ((H n).time i.succ) ((H n).toHistory.event i).incoming
      ((H n).toHistory.event_initial i) (records n i).singular
    exact hf.trans_eq ((congrArg (H n).time hi).trans (hbirth n))
  have hRlim : Tendsto R atTop atTop := tendsto_atTop_mono
    (fun n => ((hq n).1.trans_lt (hq n).2).le)
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  refine tendsto_atTop_mono (fun n => ?_) (hRlim.const_mul_atTop ha)
  calc a * R n ≤ (t n : ℝ) * R n :=
        mul_le_mul_of_nonneg_right (hbirthfloor n) (birth_scalar_pos n (hq n)).le
    _ = R n * (t n : ℝ) := mul_comm _ _

include hεcone hκ hρ hphi hinit hrec hq hRscalar hbirth hne hpar hscale hθcap hpinch
  hlast hslabs hnc hnot in
/-- Actual initial identification and singular cutoff records discharge the
birth-time divergence premise of the positive-depth construction. The other
physical history, cutoff-quality and later-observation hypotheses are retained. -/
theorem exists_subseq_depthExtendable_pos_at_birth_of_initialIdentification
    (hε : 0 < ε) (hεX : ε ≤ crossingNeckAccuracy.{u}) (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ T₀ : ℝ, 0 < T₀ ∧
      ObservedHistory.DepthExtendable (fun n => (H n).toHistory) t y R (σ ∘ ψ) T₀ := by
  exact exists_subseq_depthExtendable_pos_at_birth
    hεcone hκ hρ hphi hinit hrec hq hRscalar hbirth hne
    (tendsto_scale_mul_birth_time_atTop_of_initialIdentification (records := records)
      hinit hq hbirth hne)
    hpar hscale hθcap hpinch hlast hslabs hnc hnot hε hεX σ hσ

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
