import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingRoom
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFlow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowRadius
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ForwardTransfer
import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Metric.RestrictionDistance
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalNorm

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

namespace BackwardPointTrace

private theorem apply_point_eq_of_stage_eq {K : ObservedHistory.{u}}
    {first last : Fin (K.eventCount + 1)} {hle : first ≤ last} {x : (K.stage last).Carrier}
    (A : BackwardPointTrace K first last hle x) {α : Type*}
    (F : (j : Fin (K.eventCount + 1)) → (K.stage j).Carrier → α)
    {j k : Fin (K.eventCount + 1)} (hjk : j = k) (hj : first ≤ j) (hjl : j ≤ last)
    (hk : first ≤ k) (hkl : k ≤ last) :
    F j (A.point j hj hjl) = F k (A.point k hk hkl) := by
  subst hjk
  rfl

end BackwardPointTrace

namespace ObservedHistory

variable (K : ObservedHistory.{u})

private theorem activeStage_eq_of_time_mem (v : Icc (0 : ℝ) K.horizon)
    (j : Fin (K.eventCount + 1)) (hj : K.time j ≤ v)
    (hnext : ∀ i : Fin K.eventCount, j = i.castSucc → (v : ℝ) < K.time i.succ) :
    K.activeStage v = j := by
  apply le_antisymm _ (K.le_activeStage v j hj)
  by_contra h
  have hlt : j < K.activeStage v := lt_of_not_ge h
  have hne : j ≠ Fin.last K.eventCount := ne_of_lt (hlt.trans_le (Fin.le_last _))
  obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hne
  have hs : i.succ ≤ K.activeStage v := Fin.castSucc_lt_iff_succ_le.mp hlt
  have hle := (K.time_strictMono.monotone hs).trans (K.activeStage_time_le v)
  exact absurd (hnext i rfl) (not_lt.mpr hle)

private theorem time_lt_succ_of_activeStage_eq_castSucc (v : Icc (0 : ℝ) K.horizon)
    (i : Fin K.eventCount) (hi : K.activeStage v = i.castSucc) :
    (v : ℝ) < K.time i.succ := by
  have hval : (K.activeStage v).val < K.eventCount := by
    rw [hi]
    exact i.isLt
  have h := K.activeStage_before_next v hval
  have he : (⟨(K.activeStage v).val + 1, Nat.succ_lt_succ hval⟩ :
      Fin (K.eventCount + 1)) = i.succ := by
    ext
    simp [hi]
  rw [he] at h
  exact h

private theorem exists_slab_of_mem_Icc {first last : Fin (K.eventCount + 1)} (hlt : first < last)
    {r : ℝ} (hr : r ∈ Icc (K.time first) (K.time last)) :
    ∃ i : Fin K.eventCount, first ≤ i.castSucc ∧ i.succ ≤ last ∧
      r ∈ Icc (K.time i.castSucc) (K.time i.succ) := by
  let v : Icc (0 : ℝ) K.horizon :=
    ⟨r, (K.time_nonneg first).trans hr.1, hr.2.trans (K.time_le_horizon_at last)⟩
  have hfa : first ≤ K.activeStage v := K.le_activeStage v first hr.1
  have hta : K.time (K.activeStage v) ≤ r := K.activeStage_time_le v
  rcases lt_or_ge (K.activeStage v) last with hal | hla
  · have hne : K.activeStage v ≠ Fin.last K.eventCount :=
      ne_of_lt (hal.trans_le (Fin.le_last _))
    obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hne
    have hn := K.time_lt_succ_of_activeStage_eq_castSucc v i hi.symm
    refine ⟨i, hi ▸ hfa, Fin.castSucc_lt_iff_succ_le.mp (hi ▸ hal), hi ▸ hta, hn.le⟩
  · have hrl : r = K.time last :=
      le_antisymm hr.2 ((K.time_strictMono.monotone hla).trans hta)
    obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (ne_of_gt ((Fin.zero_le first).trans_lt hlt))
    refine ⟨i, Fin.le_castSucc_iff.mpr hlt, le_rfl, ?_, hrl.le⟩
    rw [hrl]
    exact (K.time_strictMono (Fin.castSucc_lt_succ (i := i))).le

private theorem backwardSurvivorInitialMetric_inner_le_exp
    {first last : Fin (K.eventCount + 1)} (hle : first ≤ last) {C : ℝ}
    (x : K.backwardSurvivorDomain first last hle)
    (hbound : ∀ v : Icc (0 : ℝ) K.horizon, K.time first ≤ v → (v : ℝ) ≤ K.time last →
      ∀ (hf : first ≤ K.activeStage v) (hl : K.activeStage v ≤ last),
        normSq0S (K.stageMetric (K.activeStage v) v)
            ((Classical.choice x.property).point (K.activeStage v) hf hl) 4
          (metricRm04At (K.stageMetric (K.activeStage v) v)
            ((Classical.choice x.property).point (K.activeStage v) hf hl)) ≤ C)
    (w : TangentSpace ThreeModel x) :
    (K.backwardSurvivorInitialMetric first last hle first le_rfl hle).inner x w w ≤
      Real.exp (18 * Real.sqrt C * (K.time last - K.time first)) *
        (K.initialMetric last).inner x.val w w := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · subst heq
    rw [K.backwardSurvivorInitialMetric_last, SmoothRiemannianMetric.restrictOpen_inner,
      sub_self, mul_zero, Real.exp_zero, one_mul]
  · obtain rfl : hle = hlt.le := rfl
    obtain ⟨F, hslabs, hstages, -, hsol⟩ :=
      K.exists_backwardSurvivor_isSolutionOn first last hlt
    have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    have hRm : ∀ r ∈ Icc (K.time first) (K.time last),
        normSq0S (F r) x 4 (metricRm04At (F r) x) ≤ C := by
      intro r hr
      obtain ⟨i, hfi, hil, hri⟩ := K.exists_slab_of_mem_Icc hlt hr
      let v : Icc (0 : ℝ) K.horizon :=
        ⟨r, (K.time_nonneg first).trans hr.1, hr.2.trans (K.time_le_horizon_at last)⟩
      have hfs : first ≤ i.succ := hfi.trans (Fin.castSucc_lt_succ (i := i)).le
      have hcl : i.castSucc ≤ last := (Fin.castSucc_lt_succ (i := i)).le.trans hil
      rcases eq_or_lt_of_le hri.2 with hre | hrlt
      · have hav : K.activeStage v = i.succ := by
          apply K.activeStage_eq_of_time_mem v i.succ (le_of_eq hre.symm)
          intro i' h
          change r < _
          rw [hre, h]
          exact K.time_strictMono (Fin.castSucc_lt_succ (i := i'))
        have hb := hbound v hr.1 hr.2 (hav ▸ hfs) (hav ▸ hil)
        have heq := (Classical.choice x.property).apply_point_eq_of_stage_eq
          (fun m q => normSq0S (K.stageMetric m r) q 4 (metricRm04At (K.stageMetric m r) q))
          hav (hav ▸ hfs) (hav ▸ hil) hfs hil
        subst hre
        rw [hstages i.succ hfs hil, backwardSurvivorInitialMetric,
          normSq0S_metricRm04At_localPullMetric, ← K.stageMetric_initial]
        exact heq.symm.le.trans hb
      · have hav : K.activeStage v = i.castSucc := by
          apply K.activeStage_eq_of_time_mem v i.castSucc hri.1
          intro i' h
          rw [← Fin.castSucc_injective _ h]
          exact hrlt
        have hb := hbound v hr.1 hr.2 (hav ▸ hfi) (hav ▸ hcl)
        have heq := (Classical.choice x.property).apply_point_eq_of_stage_eq
          (fun m q => normSq0S (K.stageMetric m r) q 4 (metricRm04At (K.stageMetric m r) q))
          hav (hav ▸ hfi) (hav ▸ hcl) hfi hcl
        rw [hslabs i hfi hil r hri, backwardSurvivorSlabMetric,
          normSq0S_metricRm04At_localPullMetric, (K.event i).terminal.extendedMetric_before hrlt,
          Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen, ← K.stageMetric_castSucc_apply]
        exact heq.symm.le.trans hb
    have hcomp := (metric_inner_exp_bounds_of_curvature_bound
      ({ base := { metric := F } } : SolutionOn (I := ThreeModel)
        (M := K.backwardSurvivorDomain first last hlt.le)
        (RealTimeInterval.closed (K.time first) (K.time last) (K.time_strictMono hlt).le))
      hsol (a := K.time first) (b := K.time last) (fun r hr => hr) (fun r hr => hr) x hRm
      (s := K.time first) (t := K.time last) ⟨le_rfl, (K.time_strictMono hlt).le⟩
      ⟨(K.time_strictMono hlt).le, le_rfl⟩ w).2
    change (F (K.time first)).inner x w w ≤ _ * (F (K.time last)).inner x w w at hcomp
    rw [hstages first le_rfl hlt.le, hstages last hlt.le le_rfl,
      K.backwardSurvivorInitialMetric_last, SmoothRiemannianMetric.restrictOpen_inner, hdim,
      abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (K.time_strictMono hlt).le)] at hcomp
    convert hcomp using 3
    push_cast
    ring

private theorem initialMetric_inner_le_exp_of_normSq_le {k : Fin (K.eventCount + 1)}
    {i : Fin K.eventCount} (hk : k = i.castSucc) (x : (K.stage k).Carrier) {t C : ℝ}
    (htk : K.time k ≤ t) (hti : t < K.time i.succ)
    (hbound : ∀ r ∈ Icc (K.time k) t,
      normSq0S (K.stageMetric k r) x 4 (metricRm04At (K.stageMetric k r) x) ≤ C)
    (w : TangentSpace ThreeModel x) :
    (K.initialMetric k).inner x w w ≤
      Real.exp (18 * Real.sqrt C * (t - K.time k)) * (K.stageMetric k t).inner x w w := by
  subst hk
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [← K.stageMetric_initial]
  simp only [ObservedHistory.stageMetric_castSucc_apply] at hbound ⊢
  have h := (metric_inner_exp_bounds_of_curvature_bound (K.event i).incoming.flow
    (K.event i).incoming.equation (a := K.time i.castSucc) (b := t)
    (fun r hr => ⟨hr.1, hr.2.trans_lt hti⟩) (fun r hr => ⟨hr.1, hr.2.trans hti⟩) x hbound
    (s := K.time i.castSucc) (t := t) ⟨le_rfl, htk⟩ ⟨htk, le_rfl⟩ w).2
  rw [hdim, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htk)] at h
  convert h using 3
  push_cast
  ring

end ObservedHistory

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

private theorem normSq_le_of_sqrt_le_two_mul {N C R M : ℝ} (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hsqrt : Real.sqrt N ≤ C * max R 1) (hR : R ≤ 2 * M) (hM : 1 ≤ M) :
    N ≤ (2 * C * M) ^ 2 := by
  have hmax : max R 1 ≤ 2 * M := max_le hR (by linarith)
  have h1 : Real.sqrt N ≤ 2 * C * M := hsqrt.trans (by nlinarith)
  calc N = Real.sqrt N ^ 2 := (Real.sq_sqrt hN).symm
    _ ≤ (2 * C * M) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2

private theorem normSq_stageMetric_le_of_backwardPointTrace
    {Ctime : ℝ≥0} {qcan M : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (hne : H.toHistory.activeStage t ≠ Fin.last H.eventCount)
    {p : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) p)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hscalar : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (v : Icc (0 : ℝ) H.toHistory.horizon) (huv : u ≤ v) (hvt : v ≤ t) :
    normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
          (H.toHistory.activeStage_mono hvt)) 4
        (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
            (H.toHistory.activeStage_mono hvt))) ≤
      (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by
  have hC : 0 ≤ 4 * Real.sqrt 3 * (1 + phi 1 + phi 0) := by
    have := hphi.pos 0
    have := hphi.pos 1
    positivity
  have hscal := H.scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds hut A hslabs
    hcurrent (fun _ h => absurd h hne) (by linarith) hqcan hscalar htime v huv hvt
  have hs := H.sqrt_rmNormSq_stageMetric_le_of_pinched hphi hpinch v
    (fun h => absurd (le_antisymm (Fin.le_last _) (h ▸ H.toHistory.activeStage_mono hvt)) hne)
    (A.point (H.toHistory.activeStage v) (H.toHistory.activeStage_mono huv)
      (H.toHistory.activeStage_mono hvt))
  have hN := normSq_le_of_sqrt_le_two_mul (normSq0S_nonneg _ _ _ _) hC hs hscal hM
  calc _ ≤ (2 * (4 * Real.sqrt 3 * (1 + phi 1 + phi 0)) * M) ^ 2 := hN
    _ = (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) ^ 2 := by ring

private theorem exists_window_point_of_edist_le {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hacc : p.modelAccuracy ≤ 1 / 2) (j : Fin H.eventCount)
    (b : (H.toHistory.event j).RetainedBoundaryIndex) {M dd Dcap Dstar : ℝ}
    (hsM : ((records j).static b).neck.scale ≤ 4 * M)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (xz : standardCapWindow p.modelRadius) (hxzn : ‖xz.val‖ ≤ StandardCap.transitionEnd)
    (q : (H.toHistory.stage j.succ).Carrier)
    (hnear : riemannianEDistOf (H.toHistory.initialMetric j.succ)
      (((records j).static b).window xz) q ≤ ENNReal.ofReal dd)
    (hdd0 : 0 ≤ dd) (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) * dd < Dcap) :
    ∃ x : standardCapWindow p.modelRadius,
      ‖x.val‖ < Dcap ∧ ((records j).static b).window x = q := by
  obtain ⟨x₀, δ, kk, d, w, -, hinner, -⟩ := hcan j b
  have hspos : 0 < ((records j).static b).neck.scale := ((records j).static b).neck.scale_pos
  have hlocW : IsLocalDiffeomorph ThreeModel ThreeModel ∞ ((records j).static b).window :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
      ((records j).static b).window_smooth.contMDiff
      (fun q => (((records j).static b).window_smooth.isImmersion.isImmersionAt
        q).mfderiv_injective (by simp)) rfl
  have hinjW := ((records j).static b).window_smooth.isEmbedding.injective
  have hsmall := w.properties.window_close
  change Geometry.Metric.metricDerivENormSupOn
    {y : standardCapWindow p.modelRadius |
      (riemannianEDistOf StandardCap.metric 0 y.val).toReal < p.modelRadius} p.modelOrder
    w.windowMetric (StandardCap.metric.restrictOpen (standardCapWindow p.modelRadius))
      (StandardCap.metric.restrictOpen (standardCapWindow p.modelRadius)) <
        ENNReal.ofReal p.modelAccuracy at hsmall
  simp only [StandardCap.distance_zero] at hsmall
  rw [H.toHistory.event_output j] at hinner
  have hTE := StandardCap.transitionEnd_pos
  set sc := ((records j).static b).neck.scale with hsc
  have hL : 0 < Real.sqrt (2 * sc) := Real.sqrt_pos.mpr (by positivity)
  have hU : 0 < Real.sqrt (2 / sc) := Real.sqrt_pos.mpr (by positivity)
  have hLU : Real.sqrt (2 * sc) * Real.sqrt (2 / sc) = 2 := by
    rw [← Real.sqrt_mul (by positivity), show 2 * sc * (2 / sc) = 2 * 2 by field_simp,
      Real.sqrt_mul_self (by norm_num)]
  have hL8 : Real.sqrt (2 * sc) ≤ Real.sqrt (8 * M) := Real.sqrt_le_sqrt (by linarith)
  have hsqrt8 : 0 ≤ Real.sqrt (8 * M) := Real.sqrt_nonneg _
  have hkey : Real.sqrt (2 * sc) * (Real.sqrt (2 / sc) * ‖xz.val‖ + dd) < Dcap := by
    have h1 : Real.sqrt (2 * sc) * dd ≤ Real.sqrt (8 * M) * dd :=
      mul_le_mul_of_nonneg_right hL8 hdd0
    have h2 : Real.sqrt (2 * sc) * (Real.sqrt (2 / sc) * ‖xz.val‖) ≤
        2 * StandardCap.transitionEnd := by
      rw [← mul_assoc, hLU]
      linarith
    nlinarith
  have hxzD : ‖xz.val‖ < Dcap := by
    have h0 : 0 ≤ Real.sqrt (8 * M) * dd := mul_nonneg (Real.sqrt_nonneg _) hdd0
    linarith
  have hgap : Real.sqrt (2 / sc) * ‖xz.val‖ + dd < Dcap / Real.sqrt (2 * sc) := by
    rw [lt_div_iff₀ hL]
    linarith
  set r' := (Dcap / Real.sqrt (2 * sc) - (Real.sqrt (2 / sc) * ‖xz.val‖ + dd)) / 2 with hr'
  have hmargin : Real.sqrt (2 / sc) * ‖xz.val‖ + dd + r' < Dcap / Real.sqrt (2 * sc) := by
    rw [hr']
    linarith
  have hr'pos : 0 < r' := by
    rw [hr']
    linarith
  have hbd : ∀ x : standardCapWindow p.modelRadius, ‖x.val‖ < p.modelRadius →
      ∀ v : TangentSpace ThreeModel x,
        (1 - p.modelAccuracy) * StandardCap.metric.inner x.val v v ≤
            w.windowMetric.inner x v v ∧
          w.windowMetric.inner x v v ≤
            (1 + p.modelAccuracy) * StandardCap.metric.inner x.val v v := by
    intro x hx v
    have hn := Geometry.Metric.metricDerivNorm_lt_of_sup_lt _ _ _ _ _ hsmall (Nat.zero_le _)
      (x := x) hx
    simpa only [SmoothRiemannianMetric.restrictOpen_inner] using
      Geometry.Metric.inner_bounds_of_metricDerivNorm_le
        (StandardCap.metric.restrictOpen (standardCapWindow p.modelRadius)) w.windowMetric x
        hn.le v
  have hacc0 := p.modelAccuracy_pos
  have hball := StandardCap.window_ball_subset_image_ball_of_metric_bounds
    (H.toHistory.initialMetric j.succ) (D := p.modelRadius) (R := Dcap) (r := r')
    (by linarith) hL hU hdd0 ((records j).static b).window hlocW hinjW
    (fun x hx v => by
      obtain ⟨hlo, -⟩ := hbd x (hx.trans_le (hDstar.trans hDmodel)) v
      have hi := hinner x v v
      have hn := metric_inner_self_nonneg StandardCap.metric x.val v
      rw [Real.sq_sqrt (by positivity)]
      nlinarith)
    (fun x hx v => by
      obtain ⟨-, hup⟩ := hbd x (hx.trans_le (hDstar.trans hDmodel)) v
      have hi := hinner x v v
      have hn := metric_inner_self_nonneg StandardCap.metric x.val v
      rw [Real.sq_sqrt (by positivity), div_mul_eq_mul_div, le_div_iff₀ hspos]
      nlinarith)
    xz hxzD (q) hnear hmargin
  have hcenter : q ∈
      riemannianBallOf (H.toHistory.initialMetric j.succ)
        (q) r' := by
    change riemannianEDistOf _ _ _ < ENNReal.ofReal r'
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr'pos
  obtain ⟨x, hxn, hxeq⟩ := hball hcenter
  exact ⟨x, hxn, hxeq⟩

theorem exists_cap_capture_of_ball_point_without_trace {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan M r Dcap Dstar : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t) (i : Fin H.eventCount)
    (hi : H.toHistory.activeStage t = i.castSucc)
    (y z : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hz : z ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r)
    (hzt : IsEmpty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) z))
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : (H.toHistory.event i).incoming.DerivativeBoundBefore Ctime qcan t)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
        y r,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) * r < Dcap) :
    ∃ (j : Fin H.eventCount) (hl : j.succ ≤ H.toHistory.activeStage t)
      (A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex)
      (zs : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
      (Az : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl zs)
      (x xc : standardCapWindow p.modelRadius),
      zs ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r ∧
      (∀ p' : (H.toHistory.stage j.castSucc).Carrier,
        ¬ (H.toHistory.event j).RegularCrossing p' (Az.point j.succ le_rfl hl)) ∧
      Az.point j.succ le_rfl hl = ((records j).static b).window xc ∧
      ‖xc.val‖ ≤ StandardCap.transitionEnd ∧
      A.point j.succ le_rfl hl = ((records j).static b).window x ∧ ‖x.val‖ < Dcap ∧
      riemannianEDistOf (H.toHistory.initialMetric j.succ) (((records j).static b).window xc)
          (A.point j.succ le_rfl hl) ≤
        ENNReal.ofReal
          (Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) * r) ∧
      ((records j).static b).neck.scale ≤ 4 * M ∧
      ((records j).static b).neck.scale * ((t : ℝ) - H.time j.succ) ≤
        4 * M * ((t : ℝ) - u) := by
  classical
  have hne : H.toHistory.activeStage t ≠ Fin.last H.eventCount := by
    rw [hi]
    exact Fin.castSucc_ne_last i
  have hcur : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t := fun j hj => by
    have : j = i := Fin.castSucc_injective _ (hj.trans hi)
    subst this
    exact hcurrent
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
  have hu't : u' ≤ t := by
    change H.toHistory.time j.succ ≤ (t : ℝ)
    exact (H.toHistory.time_strictMono.monotone hlj).trans (H.toHistory.activeStage_time_le t)
  have htime' : Ctime * M * ((t : ℝ) - u') ≤ 1 / 2 := by
    have hu : (u : ℝ) ≤ u' := hu'u
    have hC : 0 ≤ (Ctime : ℝ) * M := mul_nonneg Ctime.coe_nonneg (by linarith)
    nlinarith
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
    H.normSq_stageMetric_le_of_backwardPointTrace hphi hpinch hu't hne
      (Aq.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)) hslabs hcur
      hM hqcan (hspace q hq) htime' v huv hvt
  obtain ⟨b, zc, hzc⟩ := (records j).exists_cap_of_not_regularCrossing_target hnos
  obtain ⟨-, -, -, -, -, -, -, hcap⟩ := hcan j b
  obtain ⟨xz, hxzn, hxz⟩ := hcap zc
  have hspos : 0 < ((records j).static b).neck.scale := ((records j).static b).neck.scale_pos
  have hsM : ((records j).static b).neck.scale ≤ 4 * M := by
    have hb := H.scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds hu't
      (As.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)) hslabs hcur
      (fun _ h => absurd h hne) (by linarith) hqcan (hspace zs hzs) htime' u' le_rfl hu't
    have heq := As.apply_point_eq_of_stage_eq
      (fun m q => metricScalarAt (H.toHistory.stageMetric m (H.toHistory.time j.succ)) q)
      hau' ((le_of_eq hau'.symm).trans (H.toHistory.activeStage_mono (le_refl u')))
      (H.toHistory.activeStage_mono hu't) le_rfl hlj
    have h2 : metricScalarAt ((records j).static b).witness.metric
        (((records j).static b).witness.cap zc) ≤ 2 * M := by
      rw [((records j).static b).scalar_eq, ← hzc, H.toHistory.event_output j,
        ← H.toHistory.stageMetric_initial]
      exact heq.symm.le.trans hb
    linarith [hscale j b zc]
  have hage : ((records j).static b).neck.scale * ((t : ℝ) - H.time j.succ) ≤
      4 * M * ((t : ℝ) - u) := by
    have hu : (u : ℝ) ≤ H.time j.succ := hu'u
    have hT : H.time j.succ ≤ (t : ℝ) := hu't
    nlinarith [mul_le_mul_of_nonneg_left hsM (sub_nonneg.mpr hT)]
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
        H.toHistory.activeStage_eq_of_time_mem v _ hs.1 (fun i' h =>
          hs.2.trans_lt (H.toHistory.time_lt_succ_of_activeStage_eq_castSucc t i' h))
      have huv : u' ≤ v := by
        change H.toHistory.time j.succ ≤ s
        exact (H.toHistory.time_strictMono.monotone hlj).trans hs.1
      have hb := hRm q.val hq (Classical.choice q.property) v huv hs.2
      have heq := ((Classical.choice q.property).restrictFirst (le_of_eq hau'.symm)
        (H.toHistory.activeStage_mono hu't)).apply_point_eq_of_stage_eq
        (fun m x => normSq0S (H.toHistory.stageMetric m s) x 4
          (metricRm04At (H.toHistory.stageMetric m s) x))
        hav (H.toHistory.activeStage_mono huv) (H.toHistory.activeStage_mono hs.2)
        (H.toHistory.activeStage_mono hu't) le_rfl
      rw [BackwardPointTrace.endpoint_eq] at heq
      exact heq.symm.le.trans hb
    have h1 := H.toHistory.backwardSurvivorInitialMetric_inner_le_exp hlj q hb1 v
    have h2 := H.toHistory.initialMetric_inner_le_exp_of_normSq_le hi q.val
      (H.toHistory.activeStage_time_le t)
      (H.toHistory.time_lt_succ_of_activeStage_eq_castSucc t i hi) hb2 v
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
      (((records j).static b).window xz)
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
  obtain ⟨x, hxn', hxeq⟩ := H.exists_window_point_of_edist_le records hcan hacc j b hsM hDstar
    hDmodel xz hxzn _ (hnear.trans (ENNReal.ofReal_le_ofReal hdd'))
    (mul_nonneg (Real.exp_pos _).le hr.le) hwin'
  have hzxc : As.point j.succ le_rfl hlj = ((records j).static b).window xz := hzc.trans hxz.symm
  exact ⟨j, hlj, Classical.choice (htr y hyB), b, zs, As, x, xz, hzs, hnos, hzxc, hxzn,
    hxeq.symm, hxn', hnear.trans (ENNReal.ofReal_le_ofReal hdd'), hsM, hage⟩

theorem capWindowPoint_of_ball_point_without_trace {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan M r Dcap Dstar θcap : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t) (i : Fin H.eventCount)
    (hi : H.toHistory.activeStage t = i.castSucc)
    (y z : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hz : z ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y r)
    (hzt : IsEmpty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) z))
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : (H.toHistory.event i).incoming.DerivativeBoundBefore Ctime qcan t)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
        y r,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hθ : 4 * M * ((t : ℝ) - u) ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) * r < Dcap) :
    H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap := by
  obtain ⟨j, hl, A, b, -, -, x, -, -, -, -, -, hx, hxn, -, -, hage⟩ :=
    H.exists_cap_capture_of_ball_point_without_trace records hcan hscale hacc hphi hpinch hut i
      hi y z hz hzt hslabs hcurrent hM hqcan hspace htime hDstar hDmodel hwin
  refine ⟨j, hl, A, b, x, hx, by linarith, ?_⟩
  rw [← div_eq_mul_inv, le_div_iff₀ ((records j).static b).neck.scale_pos]
  linarith

theorem exists_parabolicallyRmControlledBall_or_capWindowPoint {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime Cgrad : ℝ≥0} {qcan c Dcap θcap : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    (t : Icc (0 : ℝ) H.toHistory.horizon) (i : Fin H.eventCount)
    (hi : H.toHistory.activeStage t = i.castSucc)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hqR : qcan ≤ metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)
    (hR : 1 ≤ 4 * metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)
    (hc : 0 < c) (hcgrad : (Cgrad : ℝ) * c ≤ 1 / 4) (hctime : 8 * Ctime * c ^ 2 ≤ 1)
    (hcpinch : 3072 * (1 + phi 1 + phi 0) ^ 2 * c ^ 4 ≤ 1)
    {u : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (hu : (u : ℝ) = t - c ^ 2 /
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : (H.toHistory.event i).incoming.DerivativeBoundBefore Ctime qcan t)
    (hgrad : ∀ w, qcan < (H.toHistory.event i).incoming.flow.scalar t w →
      ∀ v : TangentSpace I3 w,
        |Perelman.CanonicalNeighborhood.scalarDifferential (H.toHistory.event i).incoming.flow
          t w v| ≤
          Cgrad * (H.toHistory.event i).incoming.flow.scalar t w *
            Real.sqrt ((H.toHistory.event i).incoming.flow.scalar t w) *
            Real.sqrt (((H.toHistory.event i).incoming.flow.base.metric t).inner w v v))
    {Dstar : ℝ} (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hθ : 16 * c ^ 2 ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd +
      Real.sqrt 32 * c * Real.exp (288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2) < Dcap) :
    H.toHistory.isParabolicallyRmControlledBall t y
        (c / Real.sqrt
          (metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y)) ∨
      H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap := by
  by_cases hcw : H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap
  · exact Or.inr hcw
  refine Or.inl ?_
  set R := metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y with hRdef
  have hRpos : 0 < R := by linarith
  have hsq : 0 < Real.sqrt R := Real.sqrt_pos.mpr hRpos
  have hsqsq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hRpos.le
  have hmax : max R qcan = R := max_eq_left hqR
  have hC : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
  have htu : (t : ℝ) - u = c ^ 2 / R := by rw [hu]; ring
  apply H.isParabolicallyRmControlledBall_of_forall_nonempty_backwardPointTrace_of_gradient_bound
    hphi hpinch t i hi y hqR hR hc hcgrad hctime hcpinch hut hu hslabs hcurrent hgrad
  intro x hx
  by_contra hn
  apply hcw
  have hspace : ∀ w ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
      y (c / Real.sqrt R),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) w ≤ 4 * R := by
    intro w hw
    have h := H.scalar_le_four_mul_max_on_ball_of_gradient_bound t i hi hgrad y hRpos
      (by rw [← hRdef, hmax, mul_assoc, div_mul_cancel₀ c hsq.ne']; exact hcgrad) w hw
    rwa [← hRdef, hmax] at h
  apply H.capWindowPoint_of_ball_point_without_trace records hcan hscale hacc hphi hpinch hut i
    hi y x hx (not_nonempty_iff.mp hn) hslabs hcurrent hR (by linarith) hspace
    (hDstar := hDstar) (hDmodel := hDmodel)
  · rw [htu]
    field_simp
    nlinarith
  · rw [htu]
    field_simp
    nlinarith
  · have h32 : Real.sqrt (8 * (4 * R)) = Real.sqrt 32 * Real.sqrt R := by
      rw [show 8 * (4 * R) = 32 * R by ring, Real.sqrt_mul (by norm_num)]
    have harg : 9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * (4 * R)) * ((t : ℝ) - u) =
        288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2 := by
      rw [htu]
      field_simp
      ring
    rw [h32, harg]
    have he : Real.sqrt 32 * Real.sqrt R *
        Real.exp (288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2) * (c / Real.sqrt R) =
        Real.sqrt 32 * c * Real.exp (288 * Real.sqrt 3 * (1 + phi 1 + phi 0) * c ^ 2) := by
      field_simp
    rw [he]
    exact hwin

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
