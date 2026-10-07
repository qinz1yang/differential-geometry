import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.CapWindowAgeBoundLate_P6LL
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosureAnchorP6M

/-!
# B5（traced region 或 cap window point）的 late-records + hybrid 形（O-CH11-P6LATE G1，`_P6LL`）

`TracedRegionOrCapWindow` 的 `:286`（cap capture）、`:546`（B5）、`:665`（B5 at scale）的局部化副本：
* records / `hcan` / `hscale` / birth 比较改 late 形（`∀ i hi …`），加 `hT₀u : T₀ ≤ u`（窗口起点）；
  cap capture 找到的 event `j` 满足 `u ≤ time j.succ`，故 `hj : T₀ ≤ time j.succ`；单 record 的窗口点
  引理用 `exists_window_point_of_edist_le_record_P6N`；
* `p₀` 去掉；底座 age bound 换成 `exists_capWindow_age_bound_of_scalar_le_along_trace_late_P6LL`
  （hybrid：WindowPersistence 吃 full family `recordsF` 的 late delta 界）；
* 结论第二支 = `CapWindowPoint` 的 late 展开形（`∃ j (hj : T₀ ≤ time j.succ) hl A b x, …`，与
  `_P6N` / SLT 窗口版同形），不新建 def。
private 小引理照抄（后缀 `_P6LL`）。证明其余逐字。`P6ClosureAnchorP6M` 只为传递引入
`Local/BackwardTraceChainCaptureLateRecords_P6N`（其模块名过长，不直接 import）。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private ObservedHistory.activeStage_eq_of_time_mem
  ObservedHistory.time_lt_succ_of_activeStage_eq_castSucc
  ObservedHistory.backwardSurvivorInitialMetric_inner_le_exp
  BackwardPointTrace.apply_point_eq_of_stage_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortion

namespace RetainedCoreHistory

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

variable (H : RetainedCoreHistory.{u})

private theorem initialMetric_inner_le_exp_of_normSq_le_at_P6LL (K : ObservedHistory.{u})
    (t : Icc (0 : ℝ) K.horizon) (x : (K.stage (K.activeStage t)).Carrier) {C : ℝ}
    (hbound : ∀ r ∈ Icc (K.time (K.activeStage t)) (t : ℝ),
      normSq0S (K.stageMetric (K.activeStage t) r) x 4
        (metricRm04At (K.stageMetric (K.activeStage t) r) x) ≤ C)
    (w : TangentSpace ThreeModel x) :
    (K.initialMetric (K.activeStage t)).inner x w w ≤
      Real.exp (18 * Real.sqrt C * ((t : ℝ) - K.time (K.activeStage t))) *
        (K.stageMetric (K.activeStage t) t).inner x w w := by
  have hta := K.activeStage_time_le t
  have h := K.stageMetric_inner_le_exp_of_normSq_le (K.activeStage t) x le_rfl
    (fun i hi => ObservedHistory.time_lt_succ_of_activeStage_eq_castSucc K t i hi) t.2.2 hbound
    ⟨le_rfl, hta⟩ ⟨hta, le_rfl⟩ w
  rwa [K.stageMetric_initial, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hta)] at h

/-- **`_P6LL`**：`TracedRegionOrCapWindow:286`（cap capture）的 late-records 副本：records / `hcan` /
`hscale` late 形，加 `hT₀u : T₀ ≤ u`；找到的 event `j` 满足 `u ≤ time j.succ` ⇒ late。 -/
theorem exists_cap_capture_of_ball_point_without_trace_of_scalar_le_late_P6LL
    {p : CutoffParameters} {T₀ : ℝ}
    (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ → GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i hi b, ((records i hi).static b).hasCanonicalWindow)
    (hscale : ∀ i hi b z, ((records i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records i hi).static b).witness.metric
        (((records i hi).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {M r Dcap Dstar : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t) (hT₀u : T₀ ≤ (u : ℝ))
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (y z : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hz : z ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r)
    (hzt : IsEmpty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) z))
    (hM : 1 ≤ M)
    (hscal : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r,
      ∀ (w : Icc (0 : ℝ) H.toHistory.horizon) (_ : u ≤ w) (hwt : w ≤ t)
        (B : BackwardPointTrace H.toHistory (H.toHistory.activeStage w)
          (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hwt) x)
        (v : Icc (0 : ℝ) H.toHistory.horizon) (hwv : w ≤ v) (hvt : v ≤ t),
        metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (B.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hwv)
            (H.toHistory.activeStage_mono hvt)) ≤ 2 * M)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) * r < Dcap) :
    ∃ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ H.toHistory.activeStage t)
      (A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex)
      (zs : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
      (Az : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl zs)
      (x xc : standardCapWindow p.modelRadius),
      zs ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r ∧
      (∀ p' : (H.toHistory.stage j.castSucc).Carrier,
        ¬ (H.toHistory.event j).RegularCrossing p' (Az.point j.succ le_rfl hl)) ∧
      Az.point j.succ le_rfl hl = ((records j hj).static b).window xc ∧
      ‖xc.val‖ ≤ StandardCap.transitionEnd ∧
      A.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap ∧
      riemannianEDistOf (H.toHistory.initialMetric j.succ) (((records j hj).static b).window xc)
          (A.point j.succ le_rfl hl) ≤
        ENNReal.ofReal
          (Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) * r) ∧
      ((records j hj).static b).neck.scale ≤ 4 * M ∧ (u : ℝ) ≤ H.time j.succ := by
  classical
  let good : Fin H.eventCount → Prop := fun j =>
    H.toHistory.activeStage u ≤ j.castSucc ∧ ∃ (hl : j.succ ≤ H.toHistory.activeStage t)
      (w : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier),
      w ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r ∧
      ∃ A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl w,
        ∀ p' : (H.toHistory.stage j.castSucc).Carrier,
          ¬ (H.toHistory.event j).RegularCrossing p' (A.point j.succ le_rfl hl)
  obtain ⟨j₀, hf₀, hl₀, A₀, hno₀⟩ :=
    H.toHistory.exists_latest_event_without_regularCrossing _ z hzt
  let S := Finset.univ.filter good
  have hSne : S.Nonempty :=
    ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf₀, hl₀, z, hz, A₀, hno₀⟩⟩
  obtain ⟨j, hjS, hjmax⟩ : ∃ j ∈ S, ∀ j' ∈ S, j' ≤ j :=
    ⟨S.max' hSne, S.max'_mem hSne, fun j' h => S.le_max' j' h⟩
  obtain ⟨-, hfj, hlj, zs, hzs, As, hnos⟩ := Finset.mem_filter.mp hjS
  have htr : ∀ w ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r,
      Nonempty (BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hlj w) := by
    intro w hw
    by_contra hn
    obtain ⟨j', hf', hl', A', hno'⟩ :=
      H.toHistory.exists_latest_event_without_regularCrossing hlj w (not_nonempty_iff.mp hn)
    have hmem : j' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hfj.trans ((Fin.castSucc_lt_succ (i := j)).le.trans hf'), hl', w, hw, A', hno'⟩
    have h1 : j'.val ≤ j.val := hjmax j' hmem
    have h2 : j.val + 1 ≤ j'.val := hf'
    omega
  have hr : 0 < r := by
    have h : riemannianEDistOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y z <
        ENNReal.ofReal r := hz
    exact ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le h)
  have hyB :
      y ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r := by
    change riemannianEDistOf _ y y < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  let u' : Icc (0 : ℝ) H.toHistory.horizon :=
    ⟨H.toHistory.time j.succ, H.toHistory.time_nonneg _, H.toHistory.time_le_horizon_at _⟩
  have hau' : H.toHistory.activeStage u' = j.succ := H.toHistory.activeStage_at_time j.succ
  have hu'u : u ≤ u' := by
    change (u : ℝ) ≤ H.toHistory.time j.succ
    by_contra hle
    have h := H.toHistory.le_activeStage u j.succ (not_le.mp hle).le
    exact absurd (h.trans hfj) (not_le_of_gt (Fin.castSucc_lt_succ (i := j)))
  have hj : T₀ ≤ H.time j.succ := hT₀u.trans (show (u : ℝ) ≤ H.time j.succ from hu'u)
  have hu't : u' ≤ t := by
    change H.toHistory.time j.succ ≤ (t : ℝ)
    exact (H.toHistory.time_strictMono.monotone hlj).trans (H.toHistory.activeStage_time_le t)
  have hRm : ∀ q ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r,
      ∀ Aq : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hlj q,
      ∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u' ≤ v) (hvt : v ≤ t),
        normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            ((Aq.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)).point
              (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
              (H.toHistory.activeStage_mono hvt)) 4
          (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            ((Aq.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)).point
              (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
              (H.toHistory.activeStage_mono hvt))) ≤
          (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := fun q hq Aq v huv hvt =>
    (H.normSq_rm_le_of_backwardPointTrace_of_scalar_le_two_mul hphi hpinch hu't hlast
      (Aq.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)) hM
      (hscal q hq u' hu'u hu't _)).1 v huv hvt
  obtain ⟨b, zc, hzc⟩ := (records j hj).exists_cap_of_not_regularCrossing_target hnos
  obtain ⟨-, -, -, -, -, -, -, hcap⟩ := hcan j hj b
  obtain ⟨xz, hxzn, hxz⟩ := hcap zc
  have hspos : 0 < ((records j hj).static b).neck.scale := ((records j hj).static b).neck.scale_pos
  have hsM : ((records j hj).static b).neck.scale ≤ 4 * M := by
    have hb := hscal zs hzs u' hu'u hu't
      (As.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)) u' le_rfl hu't
    have heq := BackwardPointTrace.apply_point_eq_of_stage_eq As
      (fun m q => metricScalarAt (H.toHistory.stageMetric m (H.toHistory.time j.succ)) q)
      hau' ((le_of_eq hau'.symm).trans (H.toHistory.activeStage_mono (le_refl u')))
      (H.toHistory.activeStage_mono hu't) le_rfl hlj
    have h2 : metricScalarAt ((records j hj).static b).witness.metric
        (((records j hj).static b).witness.cap zc) ≤ 2 * M := by
      rw [((records j hj).static b).scalar_eq, ← hzc, H.toHistory.event_output j,
        ← H.toHistory.stageMetric_initial]
      exact heq.symm.le.trans hb
    linarith [hscale j hj b zc]
  have hΛ0 : 0 ≤ 8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M := by
    have := hphi.pos 0
    have := hphi.pos 1
    have : 0 ≤ M := by linarith
    positivity
  have hlocal : ∀ q : H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj,
      q.val ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r →
      ∀ v : TangentSpace ThreeModel q,
        (H.toHistory.backwardSurvivorInitialMetric j.succ (H.toHistory.activeStage t) hlj j.succ
          le_rfl hlj).inner q v v ≤
        Real.exp (18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
          ((t : ℝ) - H.toHistory.time j.succ)) *
          ((H.toHistory.stageMetric (H.toHistory.activeStage t) t).restrictOpen
            (H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj)).inner
            q v v := by
    intro q hq v
    have hb1 : ∀ v : Icc (0 : ℝ) H.toHistory.horizon, H.toHistory.time j.succ ≤ v →
        (v : ℝ) ≤ H.toHistory.time (H.toHistory.activeStage t) →
        ∀ (hf : j.succ ≤ H.toHistory.activeStage v)
          (hl : H.toHistory.activeStage v ≤ H.toHistory.activeStage t),
          normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
              ((Classical.choice q.property).point (H.toHistory.activeStage v) hf hl) 4
            (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
              ((Classical.choice q.property).point (H.toHistory.activeStage v) hf hl)) ≤
            (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := fun v hv1 hv2 _ _ =>
      hRm q.val hq (Classical.choice q.property) v hv1
        (hv2.trans (H.toHistory.activeStage_time_le t))
    have hb2 : ∀ s ∈ Icc (H.toHistory.time (H.toHistory.activeStage t)) (t : ℝ),
        normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage t) s) q.val 4
          (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage t) s) q.val) ≤
          (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by
      intro s hs
      let v : Icc (0 : ℝ) H.toHistory.horizon :=
        ⟨s, (H.toHistory.time_nonneg _).trans hs.1, hs.2.trans t.2.2⟩
      have hav : H.toHistory.activeStage v = H.toHistory.activeStage t :=
        ObservedHistory.activeStage_eq_of_time_mem H.toHistory v _ hs.1 (fun i' h =>
          hs.2.trans_lt
            (ObservedHistory.time_lt_succ_of_activeStage_eq_castSucc H.toHistory t i' h))
      have huv : u' ≤ v := by
        change H.toHistory.time j.succ ≤ s
        exact (H.toHistory.time_strictMono.monotone hlj).trans hs.1
      have hb := hRm q.val hq (Classical.choice q.property) v huv hs.2
      have heq := BackwardPointTrace.apply_point_eq_of_stage_eq
        ((Classical.choice q.property).restrictFirst (le_of_eq hau'.symm)
          (H.toHistory.activeStage_mono hu't))
        (fun m x => normSq0S (H.toHistory.stageMetric m s) x 4
          (metricRm04At (H.toHistory.stageMetric m s) x))
        hav (H.toHistory.activeStage_mono huv) (H.toHistory.activeStage_mono hs.2)
        (H.toHistory.activeStage_mono hu't) le_rfl
      rw [BackwardPointTrace.endpoint_eq] at heq
      exact heq.symm.le.trans hb
    have h1 := ObservedHistory.backwardSurvivorInitialMetric_inner_le_exp H.toHistory hlj q hb1 v
    have h2 := initialMetric_inner_le_exp_of_normSq_le_at_P6LL H.toHistory t q.val hb2 v
    rw [Real.sqrt_sq hΛ0] at h1 h2
    rw [SmoothRiemannianMetric.restrictOpen_inner]
    calc _ ≤ _ := h1
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = _ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hyz : riemannianEDistOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y zs <
      ENNReal.ofReal r := hzs
  let y' : H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj :=
    ⟨y, htr y hyB⟩
  let z' : H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj :=
    ⟨zs, htr zs hzs⟩
  have hyzU := Geometry.Metric.riemannianEDistOf_restrictOpen_lt_of_riemannianBallOf_subset
    (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
    (H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj) y' z'
    (fun w hw => htr w hw) hyz
  have hsub := riemannianBallOf_subset_of_inner_le_mul
    ((H.toHistory.stageMetric (H.toHistory.activeStage t) t).restrictOpen
      (H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj))
    (H.toHistory.backwardSurvivorInitialMetric j.succ (H.toHistory.activeStage t) hlj j.succ
      le_rfl hlj) y' (r := r) (Real.exp_pos _) (fun q hq v => hlocal q (by
        have h1 : riemannianEDistOf
            ((H.toHistory.stageMetric (H.toHistory.activeStage t) t).restrictOpen
              (H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj)) y' q <
            ENNReal.ofReal r := hq
        exact lt_of_le_of_lt (riemannianEDistOf_le_restrictOpen _ _ y' q) h1) v)
  have hz'' := hsub hyzU
  have hmap := Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph
    (H.toHistory.backwardSurvivorInitialMetric j.succ (H.toHistory.activeStage t) hlj j.succ
      le_rfl hlj)
    (H.toHistory.initialMetric j.succ)
    (H.toHistory.backwardSurvivorMap j.succ (H.toHistory.activeStage t) hlj j.succ le_rfl hlj)
    (H.toHistory.backwardSurvivorMap_isLocalDiffeomorph _ _ hlj j.succ le_rfl hlj) one_pos
    (fun x v => by
      rw [one_mul, ObservedHistory.backwardSurvivorInitialMetric, localPullMetric_inner])
    y' z'
  have hΦz : H.toHistory.backwardSurvivorMap j.succ (H.toHistory.activeStage t) hlj j.succ le_rfl
      hlj z' = As.point j.succ le_rfl hlj :=
    H.toHistory.backwardSurvivorMap_eq_point _ _ hlj j.succ le_rfl hlj z' As
  have hexp : Real.sqrt (Real.exp (18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
      ((t : ℝ) - H.toHistory.time j.succ))) =
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
        ((t : ℝ) - H.toHistory.time j.succ)) := by
    rw [show 18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
        ((t : ℝ) - H.toHistory.time j.succ) =
        9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - H.toHistory.time j.succ) +
        9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - H.toHistory.time j.succ)
        by ring, Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  set dd := Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
      ((t : ℝ) - H.toHistory.time j.succ)) * r with hdd
  have hnear : riemannianEDistOf (H.toHistory.initialMetric j.succ)
      (((records j hj).static b).window xz)
      ((Classical.choice (htr y hyB)).point j.succ le_rfl hlj) ≤ ENNReal.ofReal dd := by
    rw [hxz, ← hzc, ← hΦz, riemannianEDistOf_comm]
    have h3 : riemannianEDistOf (H.toHistory.backwardSurvivorInitialMetric j.succ
        (H.toHistory.activeStage t) hlj j.succ le_rfl hlj) y' z' <
        ENNReal.ofReal (Real.sqrt (Real.exp (18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
          ((t : ℝ) - H.toHistory.time j.succ))) * r) := hz''
    rw [hexp] at h3
    refine hmap.trans ?_
    rw [Real.sqrt_one, ENNReal.ofReal_one, one_mul]
    exact h3.le
  have hwin' : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      (Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) * r) <
        Dcap := by
    rw [← mul_assoc]
    exact hwin
  have hdd' : dd ≤ Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
      ((t : ℝ) - u)) * r := by
    have hu : (u : ℝ) ≤ H.toHistory.time j.succ := hu'u
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hr.le
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  obtain ⟨x, hxn', hxeq⟩ :=
    RetainedCoreHistory.exists_window_point_of_edist_le_record_P6N H (records j hj) (hcan j hj)
      hacc b hsM hDstar hDmodel xz hxzn _ (hnear.trans (ENNReal.ofReal_le_ofReal hdd'))
      (mul_nonneg (Real.exp_pos _).le hr.le) hwin'
  have hzxc : As.point j.succ le_rfl hlj = ((records j hj).static b).window xz := hzc.trans hxz.symm
  exact ⟨j, hj, hlj, Classical.choice (htr y hyB), b, zs, As, x, xz, hzs, hnos, hzxc, hxzn,
    hxeq.symm, hxn', hnear.trans (ENNReal.ofReal_le_ofReal hdd'), hsM, hu'u⟩

/-- **`_P6LL`（B5，late records + hybrid）**：`TracedRegionOrCapWindow:546` 的副本；结论第二支是
`CapWindowPoint` 的 late 展开形。 -/
theorem exists_isTracedRegion_or_capWindowPoint_of_scalar_le_along_traces_late_P6LL :
    ∃ c : ℝ, 0 < c ∧ ∀ Θ : ℝ, 0 < Θ → Θ < 1 → ∀ C : ℝ≥0, ∃ Cbirth : ℝ, 0 < Cbirth ∧
    ∀ Dstar : ℝ, StandardCap.transitionEnd < Dstar →
    ∃ Rrad : ℝ, Dstar + 1 < Rrad ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
    ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters} {T₀ : ℝ}
      (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        GeometricCutoffRecord H.toHistory i p),
      (∀ i hi b, ((records i hi).static b).hasCanonicalWindow) →
      Rrad ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
    ∀ {pF : CutoffParameters}, (∀ i, GeometricCutoffRecord H.toHistory i pF) →
    ∀ δbound : ℝ, (∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        pF.delta (H.time i.succ) ≤ δbound) →
      δbound ≤ δ₀ →
    ∀ (qcan a₀ : ℝ), 0 < qcan →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ i hi b, qcan ≤ Cbirth * ((records i hi).static b).neck.scale) →
      (∀ i hi b, 1 ≤ a₀ * ((records i hi).static b).neck.scale) →
    ∀ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi → H.EventSlabsPinched phi →
    ∀ u t : Icc (0 : ℝ) H.toHistory.horizon, u ≤ t → T₀ ≤ (u : ℝ) →
      (H.toHistory.activeStage t = Fin.last H.eventCount →
        ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
          Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
            (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi) →
      H.EventSlabsDerivative C qcan (H.toHistory.activeStage t) →
      (∀ i : Fin H.eventCount, i.castSucc = H.toHistory.activeStage t →
        (H.toHistory.event i).incoming.DerivativeBoundBefore C qcan t) →
      (∀ h : H.time (Fin.last H.eventCount) < H.horizon,
        H.toHistory.activeStage t = Fin.last H.eventCount →
        ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore C qcan t) →
    ∀ (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (M ρ Dcap θcap : ℝ),
      0 < ρ → (u : ℝ) < t → 1 ≤ M → 0 < θcap → θcap < Θ → Dcap ≤ Dstar →
      (∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ρ,
        ∀ (w : Icc (0 : ℝ) H.toHistory.horizon) (_ : u ≤ w) (hwt : w ≤ t)
          (B : BackwardPointTrace H.toHistory (H.toHistory.activeStage w)
            (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hwt) x)
          (v : Icc (0 : ℝ) H.toHistory.horizon) (hwv : w ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            (B.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hwv)
              (H.toHistory.activeStage_mono hvt)) ≤ 2 * M) →
      2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) * ρ < Dcap →
      2 * M * ((t : ℝ) - u) * (1 - θcap) ≤ c * θcap →
      H.toHistory.isTracedRegion t y ρ ((t : ℝ) - u) (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ∨
        ∃ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ)
          (hl : j.succ ≤ H.toHistory.activeStage t)
          (A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl y)
          (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
          A.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
            (t : ℝ) - H.time j.succ ≤ θcap * (((records j hj).static b).neck.scale)⁻¹ := by
  obtain ⟨c, hc, hC⟩ := exists_capWindow_age_bound_of_scalar_le_along_trace_late_P6LL.{u}
  refine ⟨c, hc, fun Θ hΘ hΘ1 C => ?_⟩
  obtain ⟨Cbirth, hCb, hC⟩ := hC Θ hΘ hΘ1 C
  refine ⟨Cbirth, hCb, fun Dstar hDs => ?_⟩
  obtain ⟨ε₀, hε₀, hsc⟩ := exists_presented_cap_scalar_lower_bound_of_canonical_window_core.{u}
    Dstar hDs
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζh, hδ₀, hC⟩ :=
    hC Dstar (StandardCap.transitionEnd_pos.trans hDs)
  refine ⟨R, hDR, m₀, hm₀, min ζ₀ ε₀, δ₀, lt_min hζ₀ hε₀, (min_le_left _ _).trans hζh, hδ₀, ?_⟩
  intro H p T₀ records hcan hRp hmp hζp pF recordsF δbound hdelta hδb qcan a₀ hqcan hHI hlow
    hbirth haq phi hphi hpinch u t hut hT₀u hlast hslabs hcurrent hfinal y M ρ Dcap θcap hρ hut' hM
    hθ0 hθΘ hDc hscal hwin hθM
  have hradius : Dstar ≤ p.modelRadius := by linarith
  have hacc : p.modelAccuracy ≤ 1 / 2 := hζp.trans ((min_le_left _ _).trans hζh)
  have hscale : ∀ i hi b z, ((records i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records i hi).static b).witness.metric
        (((records i hi).static b).witness.cap z) := fun i hi b z =>
    hsc (H.toHistory.event i) hradius (hζp.trans (min_le_right _ _)) (by omega)
      ((records i hi).static b) (hcan i hi b) z
  by_cases htr : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
      y ρ, Nonempty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
        (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) x)
  · refine Or.inl ⟨hρ, by linarith, u, hut, by ring, fun x hx => ?_⟩
    obtain ⟨A⟩ := htr x hx
    exact ⟨A, H.normSq_rm_le_of_backwardPointTrace_of_scalar_le_two_mul hphi hpinch hut hlast A
      hM (hscal x hx u le_rfl hut A)⟩
  · refine Or.inr ?_
    push Not at htr
    obtain ⟨z, hz, hzt⟩ := htr
    obtain ⟨j, hj, hl, A, b, -, -, x, -, -, -, -, -, hx, hxn, -, -, huj⟩ :=
      H.exists_cap_capture_of_ball_point_without_trace_of_scalar_le_late_P6LL records hcan hscale
        hacc hphi hpinch hut hT₀u hlast y z hz hzt hM hscal hDc hradius hwin
    refine ⟨j, hj, hl, A, b, x, hx, by linarith, ?_⟩
    have hyB :
        y ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ρ := by
      change riemannianEDistOf _ y y < ENNReal.ofReal ρ
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hρ
    let u' : Icc (0 : ℝ) H.toHistory.horizon :=
      ⟨H.toHistory.time j.succ, H.toHistory.time_nonneg _, H.toHistory.time_le_horizon_at _⟩
    have hau' : H.toHistory.activeStage u' = j.succ := H.toHistory.activeStage_at_time j.succ
    have hu't : u' ≤ t :=
      (H.toHistory.time_strictMono.monotone hl).trans (H.toHistory.activeStage_time_le t)
    refine hC H records hcan hRp hmp (hζp.trans (min_le_left _ _)) recordsF δbound hdelta hδb qcan
      a₀ hqcan hHI hlow u t hut hslabs hcurrent hfinal j hj hl y A b x hx (by linarith)
      (hbirth j hj b) (haq j hj b) huj (2 * M) θcap hθ0 hθΘ (fun v hjv hvt => ?_) hθM
    have hu'v : u' ≤ v :=
      (H.toHistory.time_strictMono.monotone hjv).trans (H.toHistory.activeStage_time_le v)
    exact hscal y hyB u' huj hu't (A.restrictFirst (le_of_eq hau'.symm)
      (H.toHistory.activeStage_mono hu't)) v hu'v hvt

private theorem sqrt_mul_exp_mul_div_sqrt_eq_P6LL {K Q R T A : ℝ} (hQ : 0 ≤ Q) (hR : 0 < R) :
    Real.sqrt (8 * (Q * R)) * Real.exp (9 * (K * (Q * R)) * (T / R)) * (A / Real.sqrt R) =
      Real.sqrt (8 * Q) * Real.exp (9 * K * Q * T) * A := by
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have h1 : Real.sqrt (8 * (Q * R)) = Real.sqrt (8 * Q) * Real.sqrt R := by
    rw [← mul_assoc, Real.sqrt_mul (by positivity)]
  have h2 : 9 * (K * (Q * R)) * (T / R) = 9 * K * Q * T := by field_simp
  rw [h1, h2]
  field_simp

private theorem two_mul_mul_one_sub_le_of_le_P6LL {c T Q R θcap : ℝ} (hc : 0 < c) (hT : 0 < T)
    (hQ : 0 < Q) (hR : 0 < R) (hθ4 : 1 / 4 ≤ θcap) (hθ : 1 - c / (8 * T * Q) ≤ θcap) :
    2 * (Q * R) * (T / R) * (1 - θcap) ≤ c * θcap := by
  have h1 : 2 * (Q * R) * (T / R) = 2 * Q * T := by field_simp
  have h2 : 1 - θcap ≤ c / (8 * T * Q) := by linarith
  have h3 : 2 * Q * T * (c / (8 * T * Q)) = c / 4 := by field_simp; ring
  rw [h1]
  calc 2 * Q * T * (1 - θcap) ≤ 2 * Q * T * (c / (8 * T * Q)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = c / 4 := h3
    _ ≤ c * θcap := by nlinarith

/-- **`_P6LL`（B5 at scale，late records + hybrid）**：`TracedRegionOrCapWindow:665` 的副本。 -/
theorem exists_isTracedRegion_or_capWindowPoint_at_scale_late_P6LL :
    ∃ c : ℝ, 0 < c ∧ ∀ Θ : ℝ, 0 < Θ → Θ < 1 → ∀ C : ℝ≥0, ∃ Cbirth : ℝ, 0 < Cbirth ∧
    ∀ Dstar : ℝ, StandardCap.transitionEnd < Dstar →
    ∃ Rrad : ℝ, Dstar + 1 < Rrad ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
    ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters} {T₀ : ℝ}
      (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        GeometricCutoffRecord H.toHistory i p),
      (∀ i hi b, ((records i hi).static b).hasCanonicalWindow) →
      Rrad ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
    ∀ {pF : CutoffParameters}, (∀ i, GeometricCutoffRecord H.toHistory i pF) →
    ∀ δbound : ℝ, (∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        pF.delta (H.time i.succ) ≤ δbound) →
      δbound ≤ δ₀ →
    ∀ (qcan a₀ : ℝ), 0 < qcan →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
      (∀ i hi b, qcan ≤ Cbirth * ((records i hi).static b).neck.scale) →
      (∀ i hi b, 1 ≤ a₀ * ((records i hi).static b).neck.scale) →
    ∀ phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction phi → H.EventSlabsPinched phi →
    ∀ u t : Icc (0 : ℝ) H.toHistory.horizon, u ≤ t → T₀ ≤ (u : ℝ) →
      (H.toHistory.activeStage t = Fin.last H.eventCount →
        ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
          Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
            (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi) →
      H.EventSlabsDerivative C qcan (H.toHistory.activeStage t) →
      (∀ i : Fin H.eventCount, i.castSucc = H.toHistory.activeStage t →
        (H.toHistory.event i).incoming.DerivativeBoundBefore C qcan t) →
      (∀ h : H.time (Fin.last H.eventCount) < H.horizon,
        H.toHistory.activeStage t = Fin.last H.eventCount →
        ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore C qcan t) →
    ∀ (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (R A T Q Dcap θcap : ℝ),
      0 < R → 0 < A → 0 < T → 1 ≤ Q * R → (u : ℝ) = t - T / R →
      1 / 4 ≤ θcap → 1 - c / (8 * T * Q) ≤ θcap → θcap < Θ → Dcap ≤ Dstar →
      (∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y
          (A / Real.sqrt R),
        ∀ (w : Icc (0 : ℝ) H.toHistory.horizon) (_ : u ≤ w) (hwt : w ≤ t)
          (B : BackwardPointTrace H.toHistory (H.toHistory.activeStage w)
            (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hwt) x)
          (v : Icc (0 : ℝ) H.toHistory.horizon) (hwv : w ≤ v) (hvt : v ≤ t),
          metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            (B.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono hwv)
              (H.toHistory.activeStage_mono hvt)) ≤ 2 * (Q * R)) →
      2 * StandardCap.transitionEnd + Real.sqrt (8 * Q) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0)) * Q * T) * A < Dcap →
      H.toHistory.isTracedRegion t y (A / Real.sqrt R) (T / R)
          (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (Q * R)) ∨
        ∃ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ)
          (hl : j.succ ≤ H.toHistory.activeStage t)
          (A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl y)
          (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
          A.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
            (t : ℝ) - H.time j.succ ≤ θcap * (((records j hj).static b).neck.scale)⁻¹ := by
  obtain ⟨c, hc, hD⟩ :=
    exists_isTracedRegion_or_capWindowPoint_of_scalar_le_along_traces_late_P6LL.{u}
  refine ⟨c, hc, fun Θ hΘ hΘ1 C => ?_⟩
  obtain ⟨Cbirth, hCb, hD⟩ := hD Θ hΘ hΘ1 C
  refine ⟨Cbirth, hCb, fun Dstar hDs => ?_⟩
  obtain ⟨Rrad, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζh, hδ₀, hD⟩ := hD Dstar hDs
  refine ⟨Rrad, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζh, hδ₀, ?_⟩
  intro H p T₀ records hcan hRp hmp hζp pF recordsF δbound hdelta hδb qcan a₀ hqcan hHI hlow
    hbirth haq phi hphi hpinch u t hut hT₀u hlast hslabs hcurrent hfinal y R A T Q Dcap θcap hR hA
    hT hQR hu hθ4 hθ hθΘ hDc hscal hwin
  have hQ : 0 < Q := by
    by_contra h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hR.le]
  have htu : (t : ℝ) - u = T / R := by rw [hu]; ring
  have hTR : 0 < T / R := div_pos hT hR
  have hwin' : 2 * StandardCap.transitionEnd + Real.sqrt (8 * (Q * R)) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (Q * R)) * ((t : ℝ) - u)) *
        (A / Real.sqrt R) < Dcap := by
    rw [htu, sqrt_mul_exp_mul_div_sqrt_eq_P6LL hQ.le hR]
    exact hwin
  have h := hD H records hcan hRp hmp hζp recordsF δbound hdelta hδb qcan a₀ hqcan hHI hlow hbirth
    haq phi hphi hpinch u t hut hT₀u hlast hslabs hcurrent hfinal y (Q * R) (A / Real.sqrt R) Dcap
    θcap
    (div_pos hA (Real.sqrt_pos.mpr hR)) (by linarith) hQR (by linarith) hθΘ hDc hscal hwin'
    (by rw [htu]; exact two_mul_mul_one_sub_le_of_le_P6LL hc hT hQ hR hθ4 hθ)
  rwa [htu] at h

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
