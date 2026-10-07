import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitTimeControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalPointedFlowLimitNoncollapsing
import DifferentialGeometry.Geometry.Collapse.CurvatureScale

/-!
# P6 / M8（L8b）：局部 κ ⇒ 局部流的 `hnc`（O-CH11-P6B G2，后缀 `_P6B`）

`LocalPointedFlowLimitNoncollapsing.lean:213`（极限 `κ/250`-noncollapsed）的输入 `hnc` 是局部流
`h k n` 在 `W k n` 上、所有 `0 < r ≤ radii n` 尺度的体积下界。树内的 history 级来源
`TracedRegionAncientLimitTimeControl` 要**全局** noncollapse（任意点、任意更早时刻）；P6 只有
**局部** κ（KL 84.1(a) 在种子附近，L5 的 window 形）。这里把它局部化：

* `volume_ball_ge_of_survivor_maps_of_traced_kappa_P6B`（单个 `(k, n)`）：survivor maps `f`
  （`A13b_fixed_scale_local_flow_limit` 输出 (i) 的形）+ **trace-local κ**（只要求 `W` 中点的
  backward trace 上的 controlled 球有 `κ r''³ ≤ vol`）⇒ 重标度局部流 `g σ` 在 `W` 上的体积下界。
  `f j z` 与 trace 点的等同由 trace 唯一性（`BackwardPointTrace` 是 `Subsingleton`）给出。
* `hnc_of_traced_kappa_P6B`（序列级）：输出**逐字是** `:213` 的 `hnc`，`radii n = ρnc n · √(lam n)`。

trace-local κ 的来源：L5 `localKappaWindow_of_late_P6B`（取 `nr := fun _ => 0`，即 KL 字面的全尺度
(a)）+ L7 survival 的"trace 留在种子 trace 的 `A r` 邻域"结论（P6A 的 L9 装配）。
证明照树内 private `volume_ball_ge_of_isScaledSurvivorData_of_admissible`（TimeControl:96），
只把全局 `hnc` 换成 trace-local 前提。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private ObservedHistory.isParabolicallyRmControlledBall_of_isScaledSurvivorData from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimitData

open private ObservedHistory.mem_Icc_of_mem_window
  ObservedHistory.riemannianBallOf_scaleMetric_eq
  ObservedHistory.riemannianClosedBallOf_scaleMetric_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

universe u

private local instance {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [SigmaCompactSpace M] (U : Opens M) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)

namespace ObservedHistory

/-- **M8 单步**：survivor maps（A13b 输出 (i) 的形）+ trace-local κ ⇒ 重标度局部流 `g σ` 在 `W` 上、
尺度 `r ≤ ρnc √R` 的 controlled 球体积下界 `κ r³`（`:213` 的 `hnc` 的被积式）。 -/
theorem volume_ball_ge_of_survivor_maps_of_traced_kappa_P6B (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) {R θ : ℝ} (hR : 0 < R) {W : Opens (H.stageAt t).Carrier}
    {g : ℝ → SmoothRiemannianMetric ThreeModel W}
    (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t) (ha : (a : ℝ) = t - θ / R)
    (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → W →
      (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j))
    (hc : ∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
        (hl : i.succ ≤ H.activeStage t), ∀ x : W,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    (hlast : ∀ x : W, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val)
    (hp : ∀ s ∈ Icc (-θ) 0, ∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
      (t : ℝ) + s / R ∈ H.stageDomain j.val →
        g s = scaleMetric R hR
          (localPullMetric (H.stageMetric j.val ((t : ℝ) + s / R)) (f j) (hf j)))
    {κ ρnc : ℝ} (hκ : 0 ≤ κ)
    (hkappa : ∀ x : W, ∀ (v : Icc (0 : ℝ) H.horizon) (hvt : v ≤ t), a ≤ v →
      ∀ tr : BackwardPointTrace H (H.activeStage v) (H.activeStage t)
        (H.activeStage_mono hvt) x.val,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc →
        H.isParabolicallyRmControlledBall v
          (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume (H.stageMetric (H.activeStage v) v)
            (tr.point (H.activeStage v) le_rfl (H.activeStage_mono hvt)) r'')
    {σ r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρnc * Real.sqrt R) (hwin : -θ ≤ σ - r ^ 2)
    (hσ : σ ≤ 0)
    (z : W) (hcpt : IsCompact (riemannianClosedBallOf (g σ) z r))
    (hcurv : ∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (g σ) z r,
      r ^ 4 * curvDerivNormSq 0 (g s) w ≤ 1) :
    ENNReal.ofReal (κ * r ^ 3) ≤
      Integral.Measure.riemannianVolumeMeasure ThreeModel W (g σ)
        (riemannianBallOf (g σ) z r) := by
  let _ : MeasurableSpace W := borel W
  have _ : BorelSpace W := ⟨rfl⟩
  have hsR := Real.sqrt_pos.mpr hR
  have hσθ : σ ∈ Icc (-θ) 0 := ⟨by nlinarith, hσ⟩
  have hvI := ObservedHistory.mem_Icc_of_mem_window hR ha hσθ
  let vI : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ) + σ / R, a.2.1.trans hvI.1, hvI.2.trans t.2.2⟩
  have hav : a ≤ vI := hvI.1
  have hvt : vI ≤ t := hvI.2
  let j : H.StageInterval (H.activeStage a) (H.activeStage t) :=
    ⟨H.activeStage vI, H.activeStage_mono hav, H.activeStage_mono hvt⟩
  have hgσ := hp σ hσθ j (H.activeStage_mem vI)
  set G := H.stageMetric j.val ((t : ℝ) + σ / R) with hG
  set r' := r / Real.sqrt R with hr'
  have hr'0 : 0 < r' := div_pos hr hsR
  have hsr : Real.sqrt R * r' = r := by rw [hr']; field_simp
  have hcpt' : IsCompact (riemannianClosedBallOf (localPullMetric G (f j) (hf j)) z r') := by
    rw [hgσ, ObservedHistory.riemannianClosedBallOf_scaleMetric_eq] at hcpt
    exact hcpt
  have hball' : riemannianBallOf (g σ) z r =
      riemannianBallOf (localPullMetric G (f j) (hf j)) z r' := by
    rw [hgσ, ObservedHistory.riemannianBallOf_scaleMetric_eq]
  -- the actual backward trace of `z` carried by the survivor maps
  let tr0 : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) z.val :=
    { point := fun k hk hl => f ⟨k, hk, hl⟩ z
      endpoint_eq := hlast z
      crossing := fun i hi hl => hc i hi hl z }
  let tr := tr0.restrictFirst (H.activeStage_mono hav) (H.activeStage_mono hvt)
  have htrpt : tr.point (H.activeStage vI) le_rfl (H.activeStage_mono hvt) = f j z := rfl
  have hsmall : ∀ r'' ∈ Ioo 0 r', ENNReal.ofReal (κ * r'' ^ 3) ≤
      Integral.Measure.riemannianVolumeMeasure ThreeModel W (localPullMetric G (f j) (hf j))
        (riemannianBallOf (localPullMetric G (f j) (hf j)) z r') := by
    intro r'' hr''
    have himg := Geometry.Metric.image_riemannianBallOf_localPullMetric G (f j) (hf j) (hinj j) z
      hr''.1 hr''.2 hcpt'
    have hmeas : MeasurableSet (riemannianBallOf (localPullMetric G (f j) (hf j)) z r'') :=
      (isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ z)
        continuous_const).measurableSet
    have hveq := Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
      (localPullMetric G (f j) (hf j)) G (f j) (hf j) (hinj j)
      (fun x v w => localPullMetric_inner G (f j) (hf j) x v w) hmeas
    rw [himg] at hveq
    have hpc : H.isParabolicallyRmControlledBall vI (f j z) r'' := by
      have hb0 : (a : ℝ) ≤ vI - r'' ^ 2 := by
        have h2 : r'' ^ 2 ≤ r ^ 2 / R := by
          have := pow_le_pow_left₀ hr''.1.le hr''.2.le 2
          rwa [hr', div_pow, Real.sq_sqrt hR.le] at this
        change (a : ℝ) ≤ (t : ℝ) + σ / R - r'' ^ 2
        rw [ha]
        have h1 : -θ / R ≤ (σ - r ^ 2) / R := div_le_div_of_nonneg_right hwin hR.le
        rw [neg_div, sub_div] at h1
        linarith
      let b : Icc (0 : ℝ) H.horizon :=
        ⟨vI - r'' ^ 2, a.2.1.trans hb0, by linarith [vI.2.2, sq_nonneg r'']⟩
      have hbv : b ≤ vI := show (vI : ℝ) - r'' ^ 2 ≤ vI by linarith [sq_nonneg r'']
      refine ⟨hr''.1, b, hbv, rfl, fun x hx => ?_⟩
      have hx' : x ∈ f j '' riemannianBallOf (localPullMetric G (f j) (hf j)) z r'' := by
        rw [himg]
        exact hx
      obtain ⟨w, hw, rfl⟩ := hx'
      exact ObservedHistory.isParabolicallyRmControlledBall_of_isScaledSurvivorData H t hR a ha
        f hf hc hp hr''.1
        hr''.2.le hwin hσ vI rfl hav hvt b hbv rfl w (fun s hs => hcurv s hs w (by
          rw [hball']
          exact riemannianBallOf_mono _ _ hr''.2.le hw))
    have hρ'' : r'' ≤ ρnc := hr''.2.le.trans (by
      rw [hr', div_le_iff₀ hsR]
      exact hrρ)
    have hv := hkappa z vI hvt hav tr r'' hr''.1 hρ'' (by rw [htrpt]; exact hpc)
    rw [htrpt] at hv
    refine hv.trans ?_
    change Integral.Measure.riemannianVolumeMeasure ThreeModel _ _
      (riemannianBallOf (H.stageMetric (H.activeStage vI) vI) (f j z) r'') ≤ _
    rw [← hveq]
    exact MeasureTheory.measure_mono (riemannianBallOf_mono _ _ hr''.2.le)
  have hlim : ENNReal.ofReal (κ * r' ^ 3) ≤
      Integral.Measure.riemannianVolumeMeasure ThreeModel W (localPullMetric G (f j) (hf j))
        (riemannianBallOf (localPullMetric G (f j) (hf j)) z r') := by
    have htend : Tendsto (fun x : ℝ => ENNReal.ofReal (κ * x ^ 3)) (𝓝[<] r')
        (𝓝 (ENNReal.ofReal (κ * r' ^ 3))) :=
      ((ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_pow 3))).tendsto
        r').mono_left nhdsWithin_le_nhds
    exact le_of_tendsto htend (Filter.mem_of_superset (Ioo_mem_nhdsLT hr'0) hsmall)
  have hfin : Module.finrank ℝ ThreeSpace = 3 := by simp
  have hiff := (Geometry.Measure.riemannianVolumeMeasure_ball_ge_scaleMetric_iff
    (localPullMetric G (f j) (hf j)) R hR z r' (ENNReal.ofReal κ)).2 (by
      rw [hfin, ← ENNReal.ofReal_pow hr'0.le, ← ENNReal.ofReal_mul hκ]
      exact hlim)
  rw [hsr, hfin, ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul hκ] at hiff
  rw [hgσ]
  exact hiff

end ObservedHistory

/-- **M8 序列级**：A13b 输出 (i) 的 survivor data（深度 `τ k`）+ 序列 trace-local κ ⇒ **`:213` 的
`hnc` 逐字**（`radii n = ρnc n · √(lam n)`）。 -/
theorem hnc_of_traced_kappa_P6B (H : ℕ → ObservedHistory.{u})
    (t : ∀ n, Icc (0 : ℝ) (H n).horizon) (lam : ℕ → ℝ) (hlam : ∀ n, 0 < lam n)
    (τ c : ℕ → ℝ)
    (W : ∀ (_ : ℕ) (n : ℕ), Opens ((H n).stageAt (t n)).Carrier)
    (h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n))
    (hdata : ∀ k : ℕ, ∀ᶠ n in atTop,
      ∃ (a : Icc (0 : ℝ) (H n).horizon) (hat : a ≤ t n),
        (a : ℝ) = t n - τ k / lam n ∧
        ∃ f : (j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n))) →
            W k n → ((H n).stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i : Fin (H n).eventCount) (hi : (H n).activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ (H n).activeStage (t n)), ∀ x : W k n,
              ((H n).event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : W k n,
              f ⟨(H n).activeStage (t n), (H n).activeStage_mono hat, le_rfl⟩ x = x.val) ∧
            ∀ s ∈ Icc (-τ k) 0,
              ∀ j : (H n).StageInterval ((H n).activeStage a) ((H n).activeStage (t n)),
                (t n : ℝ) + s / lam n ∈ (H n).stageDomain j.val →
                  h k n s = scaleMetric (lam n) (hlam n)
                    (localPullMetric ((H n).stageMetric j.val ((t n : ℝ) + s / lam n)) (f j)
                      (hf j)))
    {κ : ℝ} (hκ : 0 ≤ κ) (ρnc : ℕ → ℝ)
    (hkappa : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ x : W k n,
      ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - τ k / lam n ≤ v →
      ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
        ((H n).activeStage_mono hvt) x.val,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
        (H n).isParabolicallyRmControlledBall v
          (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume ((H n).stageMetric ((H n).activeStage v) v)
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'') :
    ∀ k : ℕ, ∀ σ ∈ Icc (-c k) 0, σ < 0 → ∀ᶠ n in atTop, ∀ z : W k n,
      ∀ r : ℝ, 0 < r → r ≤ ρnc n * Real.sqrt (lam n) → Icc (σ - r ^ 2) σ ⊆ Icc (-τ k) 0 →
      IsCompact (riemannianClosedBallOf (h k n σ) z r) →
      (∀ s ∈ Icc (σ - r ^ 2) σ, ∀ w ∈ riemannianBallOf (h k n σ) z r,
        r ^ 4 * curvDerivNormSq 0 (h k n s) w ≤ 1) →
      ENNReal.ofReal (κ * r ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel (W k n) (h k n σ)
          (riemannianBallOf (h k n σ) z r) := by
  intro k σ hσ _hσneg
  filter_upwards [hdata k, hkappa k] with n hd hk
  intro z r hr hrρ hwinI hcpt hcurv
  obtain ⟨a, hat, ha, f, hf, hinj, hcross, hlast, hp⟩ := hd
  have hwin : -τ k ≤ σ - r ^ 2 := (hwinI ⟨le_rfl, by nlinarith⟩).1
  have hσ0 : σ ≤ 0 := hσ.2
  refine ObservedHistory.volume_ball_ge_of_survivor_maps_of_traced_kappa_P6B (H n) (t n)
    (hlam n) a hat ha f hf hinj hcross hlast hp hκ ?_ hr hrρ hwin hσ0 z hcpt hcurv
  intro x v hvt hav tr r'' hr'' hρ hpc
  have hav' : (t n : ℝ) - τ k / lam n ≤ v := by rw [← ha]; exact hav
  exact hk x v hvt hav' tr r'' hr'' hρ hpc

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
