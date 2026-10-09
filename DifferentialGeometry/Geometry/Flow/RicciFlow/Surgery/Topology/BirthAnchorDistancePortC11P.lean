import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceAnchor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthTimeZeroBound

/-!
# O-CH11-FIX3 port of astra `BirthAnchorDistance`（`PortC11P`）

来源：donor `DifferentialGeometry/Geometry/Flow/RicciFlow/Surgery/Topology/BirthAnchorDistance.lean`
（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。G5 落地 `BirthTimeZeroBound`（port + shim）后
overlay 试编的两处失败都来自 shim 结构与 Lean 4.35 的名字解析（elaboration only；
no statement / definition / proof idea altered）：
* `open private RetainedCoreHistory.exists_birth_persistence_inputs_eventually from …` 的模块名
  `BirthTimeZeroBound` → `BirthTimeZeroBoundPortC11P`（private 名字按声明所在模块 mangle，
  shim 模块里没有它）；
* 调用处写全名 `RetainedCoreHistory.exists_birth_persistence_inputs_eventually` 并补
  `(ρb := ρb)`（短名不再解析到 opened private 声明；implicit `ρb` 不出现在该定理陈述里，
  同 `BirthTimeZeroBoundPortC11P` 的修补）。

原路径 `BirthAnchorDistance` 是只 import 本文件的 re-export shim。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

open private scalar_le_of_rebase_capWindow_dichotomy scalar_le_of_right_shift from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceAnchor
open private RetainedCoreHistory.exists_birth_persistence_inputs_eventually from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthTimeZeroBoundPortC11P

universe u

namespace RetainedCoreHistory

variable {P₀ : OrientedThreeStage.{u}} {g₀ : P₀.Metric}
  {ε C1 C2 κ ρ : ℝ} {Ctime Cgrad : ℝ≥0} {phi : ℝ → ℝ}
  {D q R : ℕ → ℝ} {p₀ p : ℕ → CutoffParameters} {δb ρb : ℕ → ℝ}
  {H : ℕ → RetainedCoreHistory.{u}}
  {records : ∀ n i, GeometricCutoffRecord (H n).toHistory i (p n)}
  {t : ∀ n, Icc (0 : ℝ) (H n).toHistory.horizon}
  (hεcone : ε ≤ coneAccuracy) (hκ : 0 < κ) (hρ : 0 < ρ)
  (hphi : Perelman.AdmissiblePinchingFunction phi)
  (hinit : ∀ n, Nonempty (InitialIdentification P₀ g₀ (H n).toHistory))
  (hrec : ∀ n, (H n).IsCanonicalCutoffRecordFamily (p₀ n) (δb n) (ρb n) (records n))
  (hq : ∀ n : ℕ, (n : ℝ) + 1 ≤ q n ∧ q n < R n)
  (hbirth : ∀ n, (H n).time ((H n).toHistory.activeStage (t n)) = (t n : ℝ))
  (hne : ∀ n, (H n).toHistory.activeStage (t n) ≠ 0)
  (hpar : ∀ n : ℕ, (p₀ n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
    D n ≤ (p₀ n).modelRadius ∧ n + 2 ≤ (p₀ n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1))
  (hscale : ∀ (n : ℕ) i b, ((n : ℝ) + 1) * q n ≤ ((records n i).static b).neck.scale)
  (hpinch : ∀ n, (H n).EventSlabsPinched phi)
  (hslabs : ∀ n,
    (H n).EventSlabsSpatiallyCanonical ε C1 C2 (q n) ((H n).toHistory.activeStage (t n)) ∧
    (H n).EventSlabsDerivative Ctime (q n) ((H n).toHistory.activeStage (t n)) ∧
    (H n).EventSlabsGradient Cgrad (q n) ((H n).toHistory.activeStage (t n)))
  (hnc : ∀ n, (H n).NoncollapsedBefore κ ρ (t n))

include hεcone hκ hρ hphi hinit hrec hq hbirth hpar hscale hpinch hslabs hnc in
private theorem eventually_incoming_scalar_le_at_normalized_distance_before_birth
    (A Dd : ℝ) (hA : 1 ≤ A) (hD : 0 < Dd) :
    ∃ C Λ : ℝ, 0 < Λ ∧ ∀ᶠ n in atTop,
      ∀ j : Fin (H n).eventCount, j.castSucc < (H n).toHistory.activeStage (t n) →
      ∀ τ : ℝ, (H n).time j.castSucc < τ → τ < (H n).time j.succ → Λ ≤ R n * τ →
      ∀ z x : ((H n).stage j.castSucc).Carrier,
        ((H n).toHistory.event j).incoming.flow.scalar τ z ≤ A * R n →
        riemannianEDistOf (((H n).toHistory.event j).incoming.flow.base.metric τ) z x <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        ((H n).toHistory.event j).incoming.flow.scalar τ x ≤ C * R n := by
  let AB : ℝ := 2 * Dd * Real.sqrt A + 1
  have hAB : 0 < AB := by dsimp [AB]; positivity
  obtain ⟨QB, Λ, Dcap, Rrad, ζB, hQB, hΛ, hDcap, -, hζB, hB3e⟩ :=
    exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal.{u}
      hεcone κ C1 C2 hκ Ctime Cgrad hphi AB hAB 1 (1 / 2) (by norm_num)
  obtain ⟨η₃, Cup, Lc, hη₃, hCup, hLc, hP3⟩ :=
    exists_scalar_metric_comparison_of_standard_close (1 / 2) (by norm_num) (by norm_num)
  let r : ℝ := 2 * Dd * Lc * Real.sqrt (2 * A) + 1
  have hr0 : 0 < r := by dsimp [r]; positivity
  let D₂ : ℝ := Dcap + 1 + r
  have hDcap0 : 0 < Dcap := StandardCap.transitionEnd_pos.trans hDcap
  obtain ⟨Cbirth, hCbirth, hP1⟩ := exists_capWindow_embedding_standard_close.{u} Ctime
  obtain ⟨RP, -, m₀, -, ζ₁, δ₀, hζ₁, hδ₀, hP1'⟩ :=
    hP1 Dcap D₂ η₃ hDcap0 (by dsimp [D₂]; linarith) hη₃
  obtain ⟨a₀, -, hHI, hev⟩ := RetainedCoreHistory.exists_birth_persistence_inputs_eventually
    (ρb := ρb) hinit (fun n => (hq n).1) hpar hscale
  have hRlim : Tendsto R atTop atTop := tendsto_atTop_mono
    (fun n => ((hq n).1.trans_lt (hq n).2).le)
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hRsq : Tendsto (fun n => ρ * Real.sqrt (R n)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp hRlim).const_mul_atTop hρ
  refine ⟨A * (QB + 2 * Cup + 1), Λ, zero_lt_one.trans_le hΛ, ?_⟩
  filter_upwards [hev (max RP Rrad) (min ζ₁ ζB) δ₀ Cbirth m₀ (lt_min hζ₁ hζB) hδ₀ hCbirth,
    hRlim.eventually_ge_atTop Λ, hRsq.eventually_ge_atTop Λ] with n hP1s hΛR hΛρ
  obtain ⟨hδn, hRn, hmn, hζn, hbirthscale⟩ := hP1s
  have hq0 : 0 < q n := lt_of_lt_of_le (by positivity) (hq n).1
  have hR0 : 0 < R n := hq0.trans (hq n).2
  have hgates : ∀ Rw τ : ℝ, R n ≤ Rw → Λ ≤ R n * τ →
      q n ≤ 1 * Rw ∧ Λ ≤ Rw ∧ Λ ≤ Rw * τ ∧ Λ ≤ ρ * Real.sqrt Rw := by
    intro Rw τ hRw hΛτ
    have hτ0 : 0 ≤ τ := by
      by_contra hneg
      have : R n * τ < 0 := mul_neg_of_pos_of_neg hR0 (lt_of_not_ge hneg)
      linarith [zero_lt_one.trans_le hΛ]
    refine ⟨by simpa only [one_mul] using (hq n).2.le.trans hRw,
      hΛR.trans hRw, hΛτ.trans (mul_le_mul_of_nonneg_right hRw hτ0), ?_⟩
    exact hΛρ.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hRw) hρ.le)
  have hrad : Rrad ≤ (p₀ n).modelRadius := (le_max_right _ _).trans hRn
  have hord : 2 ≤ (p₀ n).modelOrder := by have := (hpar n).2.2.2.1; omega
  have hacc : (p₀ n).modelAccuracy ≤ ζB := hζn.trans (min_le_right _ _)
  have hP1n := hP1' (H n) (p₀ n) (δb n) (ρb n) (records n) (hrec n) hδn
    ((le_max_left _ _).trans hRn) hmn (hζn.trans (min_le_left _ _)) (q n) a₀ hq0
    (fun x => (hHI n x).1) (fun x => (hHI n x).2) hbirthscale
  intro j hj τ hτ hτj hΛτ z x hz hzx
  have hjs : j.succ ≤ (H n).toHistory.activeStage (t n) := by
    have hj' : j.val < ((H n).toHistory.activeStage (t n)).val := hj
    exact Nat.succ_le_of_lt hj'
  have hjtime : (H n).time j.succ ≤ (t n : ℝ) :=
    ((H n).time_strictMono.monotone hjs).trans_eq (hbirth n)
  have hderprefix : (H n).EventSlabsDerivative Ctime (q n) j.castSucc :=
    fun i hi => (hslabs n).2.1 i (hi.trans hj)
  have hder : ((H n).toHistory.event j).incoming.DerivativeBoundBefore Ctime (q n) τ :=
    fun y v hv hR => (hslabs n).2.1 j hj y v ⟨hv.1, hv.2.trans hτj⟩ hR
  have hgrad : ((H n).toHistory.event j).incoming.GradientBoundBefore Cgrad (q n) τ :=
    fun y v hv hR => (hslabs n).2.2 j hj y v ⟨hv.1, hv.2.trans hτj⟩ hR
  refine scalar_le_of_rebase_capWindow_dichotomy
    (((H n).toHistory.event j).incoming.flow.base.metric τ)
    (fun w => (H n).CapWindowPoint (records n) j.castSucc w τ Dcap (1 / 2))
    (Rn := R n) (A := A) (D := Dd) (QB := QB) (AB := AB) (D₁ := Dcap) (D₂ := D₂) (r := r)
    (η₃ := η₃) (Cup := Cup) (Lc := Lc) hR0 hA hD (by linarith) hCup hLc
    (by dsimp [AB]; linarith) (by dsimp [r]; linarith) le_rfl
    ?_ ?_ hP3 z x hz hzx
  · intro w hnot hRw x' hx'
    obtain ⟨g1, g2, g3, g4⟩ := hgates _ τ hRw hΛτ
    exact hB3e ((H n).prefixAt j.castSucc) rfl ((H n).toHistory.event j).incoming
      ((H n).event_initial j) (p₀ n) (δb n) (ρb n) ((H n).prefixRecords j.castSucc (records n))
      ((H n).isCanonicalCutoffRecordFamily_prefixAt _ (hrec n)) hrad hord hacc hτ hτj w
      (q n) ρ hq0 g1 g2 g3
      (fun x'' hx'' => (hslabs n).1 j hj x'' τ ⟨hτ, hτj⟩ hx'')
      ((H n).eventSlabsDerivative_prefixAt _ hderprefix) hder hgrad
      ((H n).eventSlabsPinched_prefixAt _ (hpinch n)) (hpinch n j)
      ((H n).terminalNoncollapsedBefore_prefixAt j
        ((H n).noncollapsedBefore_mono (hτj.le.trans hjtime) (hnc n))) g4
      (fun h => hnot ((H n).capWindowPoint_of_prefixAt j (records n) h)) x' hx'
  · intro w hcw
    obtain ⟨Ξ, hΞ, z₀, hinj, hz₀, hn, i, b, Q, τw, hτw, hcl⟩ :=
      hP1n j.castSucc ((H n).time j.succ) ((H n).toHistory.event j).incoming
        ((H n).event_initial j) hderprefix τ hτ hτj hder w hcw
    exact ⟨Ξ, hΞ, z₀, hinj, hz₀, hn, _, _, Q, τw, hτw, hcl⟩

include hεcone hκ hρ hphi hinit hrec hq hbirth hne hpar hscale hpinch hslabs hnc in
/-- Uniform scalar control at normalized distance on actual slices strictly
before a nonzero birth. The constant is chosen before the negative time shift;
the eventual index may depend on that shift. Earlier surgery births are
included through right-time continuity of their actual outgoing metrics. -/
theorem eventually_scalar_le_at_normalized_distance_before_birth :
    ∀ A Dd : ℝ, 0 < A → 0 < Dd → ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, s < 0 → ∀ᶠ n in atTop,
      ∀ v : Icc (0 : ℝ) (H n).toHistory.horizon, (v : ℝ) = (t n : ℝ) + s / R n →
      ∀ z x : ((H n).toHistory.stageAt v).Carrier,
        metricScalarAt ((H n).toHistory.stageMetric ((H n).toHistory.activeStage v) v) z ≤
          A * R n →
        riemannianEDistOf ((H n).toHistory.stageMetric ((H n).toHistory.activeStage v) v) z x <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        metricScalarAt ((H n).toHistory.stageMetric ((H n).toHistory.activeStage v) v) x ≤
          C * R n := by
  intro A Dd hA hD
  obtain ⟨C₁, Λ, -, hslab⟩ := eventually_incoming_scalar_le_at_normalized_distance_before_birth
    hεcone hκ hρ hphi hinit hrec hq hbirth hpar hscale hpinch hslabs hnc
    (A + 1) (Dd + 1) (by linarith) (by linarith)
  have hRlim : Tendsto R atTop atTop := tendsto_atTop_mono
    (fun n => ((hq n).1.trans_lt (hq n).2).le)
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hRt := tendsto_scale_mul_birth_time_atTop_of_initialIdentification
    (records := records) hinit hq hbirth hne
  refine ⟨max 1 (C₁ + 1), le_max_left _ _, fun s hs => ?_⟩
  filter_upwards [hslab, hRt.eventually_ge_atTop (Λ - s), hRlim.eventually_ge_atTop 1]
    with n hsl hRtn hR1
  intro v hv
  have hR0 : 0 < R n := zero_lt_one.trans_le hR1
  have hRv : R n * (v : ℝ) = R n * (t n : ℝ) + s := by
    rw [hv, mul_add, mul_div_cancel₀ _ hR0.ne']
  have hΛv : Λ ≤ R n * (v : ℝ) := by linarith
  have hvt : (v : ℝ) < t n := by rw [hv]; linarith [div_neg_of_neg_of_pos hs hR0]
  have hk : (H n).toHistory.activeStage v < (H n).toHistory.activeStage (t n) :=
    (H n).time_strictMono.lt_iff_lt.mp (by
      rw [hbirth n]
      exact ((H n).toHistory.activeStage_time_le v).trans_lt hvt)
  have hC : C₁ + 1 ≤ max 1 (C₁ + 1) := le_max_right _ _
  have key : ∀ k : Fin ((H n).eventCount + 1), k < (H n).toHistory.activeStage (t n) →
      (v : ℝ) ∈ (H n).toHistory.stageDomain k → ∀ z x : ((H n).stage k).Carrier,
      metricScalarAt ((H n).toHistory.stageMetric k v) z ≤ A * R n →
      riemannianEDistOf ((H n).toHistory.stageMetric k v) z x <
        ENNReal.ofReal (Dd / Real.sqrt (R n)) →
      metricScalarAt ((H n).toHistory.stageMetric k v) x ≤ max 1 (C₁ + 1) * R n := by
    intro k hkb
    cases k using Fin.lastCases with
    | last => exact False.elim ((not_lt_of_ge (Fin.le_last _)) hkb)
    | cast j =>
      intro hmem z x hz hzx
      simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc, mem_Ico] at hmem
      rw [ObservedHistory.stageMetric_castSucc_apply] at hz hzx ⊢
      have h := scalar_le_of_right_shift ((H n).toHistory.event j).incoming
        (v := v) (Rn := R n) (A := A) (A' := A + 1)
        (Dd := Dd) (D' := Dd + 1) (C₁ := C₁) (e := 1)
        ⟨hmem.1, hmem.2⟩ hR1 le_rfl hD le_rfl one_pos
        (fun τ hvτ _ hτb z' x' hz' hzx' => hsl j hkb τ
          (lt_of_le_of_lt hmem.1 hvτ) hτb
          (hΛv.trans (mul_le_mul_of_nonneg_left hvτ.le hR0.le)) z' x' hz' hzx')
        z x hz hzx
      exact h.trans (mul_le_mul_of_nonneg_right hC hR0.le)
  exact key _ hk ((H n).toHistory.activeStage_mem v)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
