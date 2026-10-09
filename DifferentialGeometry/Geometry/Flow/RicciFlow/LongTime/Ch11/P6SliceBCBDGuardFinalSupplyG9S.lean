import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDGuardAlignedA2B
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6AnchorFinalSlabP6M
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KernelsNoJ10P6JG3

/-!
# guarded `hder / hgrad` 槽的 final-slab 孪生（O-CH11-G9SHIFT G5，后缀 `_G9S`）

BCBD-A2 G5（`P6SliceBCBDGuardSupplyA2B`）的 `hderSelG / hgradG` 在 σ 落 final slab
（`time (Fin.last _) < t n < horizon`）时的换帧：中心 slab `(event (j n)).incoming` ↦ `G n`
（`hG : G n = finalSlab.restrictIncoming …`，P6M 同款写法），`(j n).castSucc` ↦ `Fin.last _`，
stage 识别用 `activeStage_eq_last_of_time_last_le` 与 `stageMetric_last_of_lt`
（四个桥引理 `mem_ball_final / scalar_final / witness_final / deriv_final` 为 P6M private 版的公开副本）。
`hdistWG` 陈述帧通用（只含 `activeStage v = activeStage σ`），原样作 binder，
由 final 同 slab c⋆ stay（`stay_cstar_final_P6HK`）付。生成器 `gen/genF1.py`。无新分析、无新 binder。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

/-- 球成员：final slab incoming 度量 → `stageMetric m`（`_G9S`，P6M private 版的公开副本）。 -/
theorem mem_ball_final_G9S (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    (G : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount)) K.horizon)
    (hG : G = (K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
    {m : Fin (K.eventCount + 1)} (hm : Fin.last K.eventCount = m) (v r : ℝ)
    (z yG : (K.stage (Fin.last K.eventCount)).Carrier) (x y : (K.stage m).Carrier) (hx : HEq x z)
    (hy : HEq y yG) (h : z ∈ riemannianBallOf (G.flow.base.metric v) yG r) :
    x ∈ riemannianBallOf (K.toHistory.stageMetric m v) y r := by
  subst hG
  subst hm
  obtain rfl := eq_of_heq hx
  obtain rfl := eq_of_heq hy
  rw [ObservedHistory.stageMetric_last_of_lt (H := K.toHistory) (h := hfin)]
  exact h

/-- 标量 `stageMetric m` ↔ final slab incoming（`_G9S`）。 -/
theorem scalar_final_G9S (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    (G : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount)) K.horizon)
    (hG : G = (K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
    {m : Fin (K.eventCount + 1)} (hm : Fin.last K.eventCount = m) (v : ℝ)
    (z : (K.stage (Fin.last K.eventCount)).Carrier) (x : (K.stage m).Carrier) (hx : HEq x z) :
    metricScalarAt (K.toHistory.stageMetric m v) x = G.flow.scalar v z := by
  subst hG
  subst hm
  obtain rfl := eq_of_heq hx
  rw [ObservedHistory.stageMetric_last_of_lt (H := K.toHistory) (h := hfin)]
  rfl

/-- witness `stageMetric m` → final slab incoming（`_G9S`）。 -/
theorem witness_final_G9S (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    (G : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount)) K.horizon)
    (hG : G = (K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
    {m : Fin (K.eventCount + 1)} (hm : Fin.last K.eventCount = m) (v : ℝ) {ε C1 C2 : ℝ}
    (z : (K.stage (Fin.last K.eventCount)).Carrier) (x : (K.stage m).Carrier) (hx : HEq x z)
    (h : ∃ W : SpatialCanonicalWitness (K.toHistory.stageMetric m v) ε C1 C2 x,
      W.capTubeHasNeckChart ε) :
    ∃ W : SpatialCanonicalWitness (G.flow.base.metric v) ε C1 C2 z, W.capTubeHasNeckChart ε := by
  subst hG
  subst hm
  obtain rfl := eq_of_heq hx
  rw [ObservedHistory.stageMetric_last_of_lt (H := K.toHistory) (h := hfin)] at h
  exact h

/-- 时间导数 `stageMetric m` → final slab incoming（`_G9S`）。 -/
theorem deriv_final_G9S (K : RetainedCoreHistory.{u})
    (hfin : K.time (Fin.last K.eventCount) < K.horizon)
    (G : (K.stage (Fin.last K.eventCount)).IncomingSlab (K.time (Fin.last K.eventCount)) K.horizon)
    (hG : G = (K.finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
    {m : Fin (K.eventCount + 1)} (hm : Fin.last K.eventCount = m) (v : ℝ) {C : ℝ}
    (z : (K.stage (Fin.last K.eventCount)).Carrier) (x : (K.stage m).Carrier) (hx : HEq x z)
    (h : |derivWithin (fun s => metricScalarAt (K.toHistory.stageMetric m s) x) (Iic v) v| ≤
      C * metricScalarAt (K.toHistory.stageMetric m v) x ^ 2) :
    |derivWithin (fun s => G.flow.scalar s z) (Iic v) v| ≤ C * G.flow.scalar v z ^ 2 := by
  subst hG
  subst hm
  obtain rfl := eq_of_heq hx
  simp only [ObservedHistory.stageMetric_last_of_lt (H := K.toHistory) (h := hfin)] at h
  exact h

end RetainedCoreHistory

/-- **guarded `hder` 槽（`_A2B`，PROVED ⇐ hgood + `hdistWG`）**：
`hderSel_of_selection_sameSlab_Cg_P6JG3` 逐字，`hdistW` 与结论都加 c⋆ guard。 -/
theorem ObservedHistory.hderSelGF_of_selection_sameSlab_Cg_G9S
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    {K : ℕ → RetainedCoreHistory.{u}}
    {t : ℕ → ℝ} (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n)
    (htK : ∀ n, t n < (K n).horizon)
    (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon)
    (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistWG : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (K n).toHistory.activeStage v = (K n).toHistory.activeStage (σ n) →
        ((σ n : ℝ) - v) * max (Cg * R n) (metricScalarAt ((K n).toHistory.stageMetric
          ((K n).toHistory.activeStage (σ n)) (σ n)) x) ≤ 1 / (2 * max (Ctime' : ℝ) 1) →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ Rad B : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
      ∀ v ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) (t n),
      t n - B / (G n).flow.scalar (t n) (yG n) ≤ v →
      Cg * R n < (G n).flow.scalar v x →
      (t n - v) * max (Cg * R n) ((G n).flow.scalar (t n) x) ≤
        1 / (2 * max (Ctime' : ℝ) 1) →
      |derivWithin (fun w => (G n).flow.scalar w x) (Iic v) v| ≤
        (Ctime' : ℝ) * (G n).flow.scalar v x ^ 2 := by
  intro Rad B
  filter_upwards [eventually_window_scale_le_P6N hL (max B 1) (max Rad 1),
    hwin (max B 1) (by positivity), hdistWG (max Rad 1) (max B 1) (by positivity) (by positivity)]
    with n hsc hw hd
  intro x hx v hv hBv hq hg
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon := (htl n).trans (htK n)
  have hσact : (K n).toHistory.activeStage (σ n) = Fin.last (K n).eventCount :=
    (K n).toHistory.activeStage_eq_last_of_time_last_le (σ n) (by rw [hσ n]; exact (htl n).le)
  have hv0 : 0 ≤ v := ((K n).toHistory.time_nonneg _).trans hv.1.le
  have hvH : v ≤ (K n).horizon := (hv.2.trans (htK n)).le
  let v' : Icc (0 : ℝ) (K n).toHistory.horizon := ⟨v, hv0, hvH⟩
  have hvact : (K n).toHistory.activeStage v' = Fin.last (K n).eventCount :=
    (K n).toHistory.activeStage_eq_last_of_time_last_le v' hv.1.le
  have hvt : v' ≤ σ n := show v ≤ (σ n : ℝ) by rw [hσ n]; exact hv.2.le
  let x' : ((K n).toHistory.stageAt (σ n)).Carrier :=
    cast (congrArg (fun m => ((K n).stage m).Carrier) hσact.symm) x
  have hxx : HEq x' x := cast_heq _ _
  have hx' : x' ∈ riemannianBallOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) (max Rad 1 / Real.sqrt (R n)) := by
    refine (K n).mem_ball_final_G9S hfin (G n) (hG n) hσact.symm (σ n) _ x (yG n) x' (y n) hxx
      (hyG n) ?_
    rw [hσ n]
    rw [← hRn n] at hx
    exact riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le) hx
  obtain ⟨tr, htr⟩ := RetainedCoreHistory.exists_trace_of_stage_eq_P6JG3H (K n).toHistory
    (hvact.trans hσact.symm) ((K n).toHistory.activeStage_mono hvt) x'
  have hBv' : (σ n : ℝ) - max B 1 / R n ≤ v' := by
    change (σ n : ℝ) - max B 1 / R n ≤ v
    rw [hσ n]
    rw [← hRn n] at hBv
    have : B / R n ≤ max B 1 / R n := div_le_div_of_nonneg_right (le_max_left _ _) (hR n).le
    linarith
  have hav : aSeed n ≤ v' := hw.trans hBv'
  have hLθ : (σ n : ℝ) - L n ^ 2 / R n ≤ (σ n : ℝ) - max B 1 / R n :=
    sub_le_sub_left (div_le_div_of_nonneg_right hsc.1 (hR n).le) _
  have hptx : HEq (tr.point ((K n).toHistory.activeStage v') le_rfl
      ((K n).toHistory.activeStage_mono hvt)) x := htr.trans hxx
  have hsc' := (K n).scalar_final_G9S hfin (G n) (hG n) hvact.symm v x _ hptx
  have hg' : ((σ n : ℝ) - v') * max (Cg * R n) (metricScalarAt ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) x') ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by
    rw [(K n).scalar_final_G9S hfin (G n) (hG n) hσact.symm (σ n) x x' hxx, hσ n]
    exact hg
  have hgoodv := hgood n v' hav hvt (hLθ.trans hBv') _
    (hd x' hx' v' hav hvt hBv' (hvact.trans hσact.symm) hg' tr) (by rw [hsc']; exact hq.le)
  have hvh : v < (K n).toHistory.horizon := hv.2.trans (htK n)
  have htv : (K n).toHistory.time ((K n).toHistory.activeStage v') < (v' : ℝ) := by
    rw [hvact]
    exact hv.1
  exact (K n).deriv_final_G9S hfin (G n) (hG n) hvact.symm v x _ hptx (hgoodv.2 htv hvh)

/-- **guarded `hgrad` 槽（`_A2B`，PROVED ⇐ hgood + `hdistWG`）**：
`hgrad_of_selection_sameSlab_Cg_P6CD` 逐字，`hdistW` 与结论都加 c⋆ guard。 -/
theorem ObservedHistory.hgradGF_of_selection_sameSlab_Cg_G9S
    {eps C1' C2' : ℝ} {Ctime' : ℝ≥0} {Cg : ℝ}
    (hC2 : 0 ≤ C2')
    {K : ℕ → RetainedCoreHistory.{u}}
    {t : ℕ → ℝ} (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n)
    (htK : ∀ n, t n < (K n).horizon)
    (G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
      ((K n).time (Fin.last (K n).eventCount)) (K n).horizon)
    (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
      ((htl n).trans (htK n)) le_rfl) (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n) (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier)
    (yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier) (hyG : ∀ n, HEq (y n) (yG n))
    (R : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n))
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((K n).toHistory.stageAt v).Carrier,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        Cg * R n ≤ metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
          z →
        (K n).toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdistWG : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (K n).toHistory.activeStage v = (K n).toHistory.activeStage (σ n) →
        ((σ n : ℝ) - v) * max (Cg * R n) (metricScalarAt ((K n).toHistory.stageMetric
          ((K n).toHistory.activeStage (σ n)) (σ n)) x) ≤ 1 / (2 * max (Ctime' : ℝ) 1) →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    ∀ Rad B : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
          (Rad / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
      ∀ v ∈ Ioo ((K n).time (Fin.last (K n).eventCount)) (t n),
      t n - B / (G n).flow.scalar (t n) (yG n) ≤ v →
      Cg * R n < (G n).flow.scalar v x →
      (t n - v) * max (Cg * R n) ((G n).flow.scalar (t n) x) ≤
        1 / (2 * max (Ctime' : ℝ) 1) →
      ∀ w : TangentSpace ThreeModel x,
        |scalarDifferential (G n).flow v x w| ≤
          (C2'.toNNReal : ℝ) * (G n).flow.scalar v x *
            Real.sqrt ((G n).flow.scalar v x) *
            Real.sqrt
              (((G n).flow.base.metric v).inner x w w) := by
  intro Rad B
  filter_upwards [eventually_window_scale_le_P6N hL (max B 1) (max Rad 1),
    hwin (max B 1) (by positivity), hdistWG (max Rad 1) (max B 1) (by positivity) (by positivity)]
    with n hsc hw hd
  intro x hx v hv hBv hq hg w
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon := (htl n).trans (htK n)
  have hσact : (K n).toHistory.activeStage (σ n) = Fin.last (K n).eventCount :=
    (K n).toHistory.activeStage_eq_last_of_time_last_le (σ n) (by rw [hσ n]; exact (htl n).le)
  have hv0 : 0 ≤ v := ((K n).toHistory.time_nonneg _).trans hv.1.le
  have hvH : v ≤ (K n).horizon := (hv.2.trans (htK n)).le
  let v' : Icc (0 : ℝ) (K n).toHistory.horizon := ⟨v, hv0, hvH⟩
  have hvact : (K n).toHistory.activeStage v' = Fin.last (K n).eventCount :=
    (K n).toHistory.activeStage_eq_last_of_time_last_le v' hv.1.le
  have hvt : v' ≤ σ n := show v ≤ (σ n : ℝ) by rw [hσ n]; exact hv.2.le
  let x' : ((K n).toHistory.stageAt (σ n)).Carrier :=
    cast (congrArg (fun m => ((K n).stage m).Carrier) hσact.symm) x
  have hxx : HEq x' x := cast_heq _ _
  have hx' : x' ∈ riemannianBallOf ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) (y n) (max Rad 1 / Real.sqrt (R n)) := by
    refine (K n).mem_ball_final_G9S hfin (G n) (hG n) hσact.symm (σ n) _ x (yG n) x' (y n) hxx
      (hyG n) ?_
    rw [hσ n]
    rw [← hRn n] at hx
    exact riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right (le_max_left _ _) hsR.le) hx
  obtain ⟨tr, htr⟩ := RetainedCoreHistory.exists_trace_of_stage_eq_P6JG3H (K n).toHistory
    (hvact.trans hσact.symm) ((K n).toHistory.activeStage_mono hvt) x'
  have hBv' : (σ n : ℝ) - max B 1 / R n ≤ v' := by
    change (σ n : ℝ) - max B 1 / R n ≤ v
    rw [hσ n]
    rw [← hRn n] at hBv
    have : B / R n ≤ max B 1 / R n := div_le_div_of_nonneg_right (le_max_left _ _) (hR n).le
    linarith
  have hav : aSeed n ≤ v' := hw.trans hBv'
  have hLθ : (σ n : ℝ) - L n ^ 2 / R n ≤ (σ n : ℝ) - max B 1 / R n :=
    sub_le_sub_left (div_le_div_of_nonneg_right hsc.1 (hR n).le) _
  have hptx : HEq (tr.point ((K n).toHistory.activeStage v') le_rfl
      ((K n).toHistory.activeStage_mono hvt)) x := htr.trans hxx
  have hsc' := (K n).scalar_final_G9S hfin (G n) (hG n) hvact.symm v x _ hptx
  have hg' : ((σ n : ℝ) - v') * max (Cg * R n) (metricScalarAt ((K n).toHistory.stageMetric
      ((K n).toHistory.activeStage (σ n)) (σ n)) x') ≤ 1 / (2 * max (Ctime' : ℝ) 1) := by
    rw [(K n).scalar_final_G9S hfin (G n) (hG n) hσact.symm (σ n) x x' hxx, hσ n]
    exact hg
  have hgoodv := hgood n v' hav hvt (hLθ.trans hBv') _
    (hd x' hx' v' hav hvt hBv' (hvact.trans hσact.symm) hg' tr) (by rw [hsc']; exact hq.le)
  have hW := (K n).witness_final_G9S hfin (G n) (hG n) hvact.symm v x _ hptx hgoodv.1
  obtain ⟨W, -⟩ := hW
  rw [Real.coe_toNNReal _ hC2]
  exact W.gradient w

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
