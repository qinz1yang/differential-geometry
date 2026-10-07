import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueTerminalLocal

/-!
# CH12-O3 (late records): the local-κ surgery-tolerant KL70.2 kernel with late cutoff records

Same as `MicroGlueTerminalLocal.lean`, but cutoff records are only required for events `i` with
`T₀ ≤ H.time i.succ`, under the extra premise `T₀ + θ ≤ t`.  The backward-trace capture chain of
`ST/BackwardTraceChainCapture.lean` and `ST/BoundedCurvatureAtDistanceSlice.lean` is re-proved
for such partial record families; the cap-window alternative is written inline.
`..._closed_late_O3L` is the same kernel for a closed terminal slab `S` on `[time last, t]`
(pinching then has to be assumed on the closed interval `Icc (time last) t`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

open private ObservedHistory.activeStage_eq_of_time_mem
  ObservedHistory.time_lt_succ_of_activeStage_eq_castSucc
  ObservedHistory.backwardSurvivorInitialMetric_inner_le_exp
  BackwardPointTrace.apply_point_eq_of_stage_eq from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortion

open private ObservedHistory.initialMetric_inner_le_exp_of_normSq_le_of_eq_last
  RetainedCoreHistory.normSq_stageMetric_le_of_backwardPointTrace_of_final from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortionTerminal

private theorem exists_window_point_of_edist_le_O3L (H : RetainedCoreHistory.{u})
    {p : CutoffParameters} (hacc : p.modelAccuracy ≤ 1 / 2) (j : Fin H.eventCount)
    (R : GeometricCutoffRecord H.toHistory j p)
    (hcan : ∀ b, (R.static b).hasCanonicalWindow)
    (b : (H.toHistory.event j).RetainedBoundaryIndex) {M dd Dcap Dstar : ℝ}
    (hsM : (R.static b).neck.scale ≤ 4 * M)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (xz : standardCapWindow p.modelRadius) (hxzn : ‖xz.val‖ ≤ StandardCap.transitionEnd)
    (q : (H.toHistory.stage j.succ).Carrier)
    (hnear : riemannianEDistOf (H.toHistory.initialMetric j.succ)
      ((R.static b).window xz) q ≤ ENNReal.ofReal dd)
    (hdd0 : 0 ≤ dd) (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) * dd < Dcap) :
    ∃ x : standardCapWindow p.modelRadius,
      ‖x.val‖ < Dcap ∧ (R.static b).window x = q := by
  obtain ⟨x₀, δ, kk, d, w, -, hinner, -⟩ := hcan b
  have hspos : 0 < (R.static b).neck.scale := (R.static b).neck.scale_pos
  have hlocW : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (R.static b).window :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
      (R.static b).window_smooth.contMDiff
      (fun q => ((R.static b).window_smooth.isImmersion.isImmersionAt
        q).mfderiv_injective (by simp)) rfl
  have hinjW := (R.static b).window_smooth.isEmbedding.injective
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
  set sc := (R.static b).neck.scale with hsc
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
    (by linarith) hL hU hdd0 (R.static b).window hlocW hinjW
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

private theorem exists_cap_capture_of_chain_point_without_trace_of_comparison_O3L
    (H : RetainedCoreHistory.{u})
    {p : CutoffParameters}
    (T₀ : ℝ)
    (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ → GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i hi b, ((records i hi).static b).hasCanonicalWindow)
    (hscale : ∀ i hi b z, ((records i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records i hi).static b).witness.metric
        (((records i hi).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan M Dcap Dstar : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t) (hT₀u : T₀ ≤ (u : ℝ))
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (hcmp : ∀ (q : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (C : ℝ),
      (∀ s ∈ Icc (H.toHistory.time (H.toHistory.activeStage t)) (t : ℝ),
        normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage t) s) q 4
          (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage t) s) q) ≤ C) →
      ∀ w : TangentSpace ThreeModel q,
        (H.toHistory.initialMetric (H.toHistory.activeStage t)).inner q w w ≤
          Real.exp (18 * Real.sqrt C * ((t : ℝ) - H.toHistory.time (H.toHistory.activeStage t))) *
            (H.toHistory.stageMetric (H.toHistory.activeStage t) t).inner q w w)
    {N : ℕ} (pc : ℕ → (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (δ : ℕ → ℝ)
    (hδ : ∀ k ≤ N, 0 < δ k)
    (hchain : ∀ k < N, pc (k + 1) ∈
      riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k))
    (z : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hz : ∃ k ≤ N,
      z ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k))
    (hzt : IsEmpty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) z))
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcur : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ k ≤ N, ∀ x ∈ riemannianBallOf
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) *
        ∑ i ∈ Finset.range (N + 1), δ i < Dcap) :
    ∃ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ H.toHistory.activeStage t)
      (A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl (pc 0))
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap ∧
      ((records j hj).static b).neck.scale ≤ 4 * M ∧
      ((records j hj).static b).neck.scale * ((t : ℝ) - H.time j.succ) ≤
        4 * M * ((t : ℝ) - u) := by
  classical
  set S : Set (H.toHistory.stage (H.toHistory.activeStage t)).Carrier :=
    {w | ∃ k ≤ N, w ∈ riemannianBallOf
      (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k)} with hSdef
  let good : Fin H.eventCount → Prop := fun j =>
    H.toHistory.activeStage u ≤ j.castSucc ∧ ∃ (hl : j.succ ≤ H.toHistory.activeStage t)
      (w : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier), w ∈ S ∧
      ∃ A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl w,
        ∀ p' : (H.toHistory.stage j.castSucc).Carrier,
          ¬ (H.toHistory.event j).RegularCrossing p' (A.point j.succ le_rfl hl)
  obtain ⟨j₀, hf₀, hl₀, A₀, hno₀⟩ :=
    H.toHistory.exists_latest_event_without_regularCrossing _ z hzt
  let T := Finset.univ.filter good
  have hTne : T.Nonempty :=
    ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf₀, hl₀, z, hz, A₀, hno₀⟩⟩
  obtain ⟨j, hjT, hjmax⟩ : ∃ j ∈ T, ∀ j' ∈ T, j' ≤ j :=
    ⟨T.max' hTne, T.max'_mem hTne, fun j' h => T.le_max' j' h⟩
  obtain ⟨-, hfj, hlj, zs, hzs, As, hnos⟩ := Finset.mem_filter.mp hjT
  have htr : ∀ w ∈ S,
      Nonempty (BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hlj w) := by
    intro w hw
    by_contra hn
    obtain ⟨j', hf', hl', A', hno'⟩ :=
      H.toHistory.exists_latest_event_without_regularCrossing hlj w (not_nonempty_iff.mp hn)
    have hmem : j' ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hfj.trans ((Fin.castSucc_lt_succ (i := j)).le.trans hf'), hl', w, hw, A', hno'⟩
    have h1 : j'.val ≤ j.val := hjmax j' hmem
    have h2 : j.val + 1 ≤ j'.val := hf'
    omega
  have hyS : pc 0 ∈ S := by
    refine ⟨0, Nat.zero_le _, ?_⟩
    change riemannianEDistOf _ (pc 0) (pc 0) < ENNReal.ofReal (δ 0)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (hδ 0 (Nat.zero_le _))
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
  have hj : T₀ ≤ H.time j.succ := hT₀u.trans (show (u : ℝ) ≤ H.time j.succ from hu'u)
  have htime' : Ctime * M * ((t : ℝ) - u') ≤ 1 / 2 := by
    have hu : (u : ℝ) ≤ u' := hu'u
    have hC : 0 ≤ (Ctime : ℝ) * M := mul_nonneg Ctime.coe_nonneg (by linarith)
    nlinarith
  have hspaceS : ∀ q ∈ S,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) q ≤ M := by
    rintro q ⟨k, hk, hq⟩
    exact hspace k hk q hq
  have hRm : ∀ q ∈ S,
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
    RetainedCoreHistory.normSq_stageMetric_le_of_backwardPointTrace_of_final H hphi hpinch hu't
      hlast
      (Aq.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)) hslabs hcur
      hfinal hM hqcan (hspaceS q hq) htime' v huv hvt
  obtain ⟨b, zc, hzc⟩ := (records j hj).exists_cap_of_not_regularCrossing_target hnos
  obtain ⟨-, -, -, -, -, -, -, hcap⟩ := hcan j hj b
  obtain ⟨xz, hxzn, hxz⟩ := hcap zc
  have hsM : ((records j hj).static b).neck.scale ≤ 4 * M := by
    have hb := H.scalar_le_two_mul_of_backwardPointTrace_of_derivative_bounds hu't
      (As.restrictFirst (le_of_eq hau'.symm) (H.toHistory.activeStage_mono hu't)) hslabs hcur
      hfinal (by linarith) hqcan (hspaceS zs hzs) htime' u' le_rfl hu't
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
  have hage : ((records j hj).static b).neck.scale * ((t : ℝ) - H.time j.succ) ≤
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
      q.val ∈ S → ∀ v : TangentSpace ThreeModel q,
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
    have h2 := hcmp q.val _ hb2 v
    rw [Real.sqrt_sq hΛ0] at h1 h2
    rw [SmoothRiemannianMetric.restrictOpen_inner]
    calc _ ≤ _ := h1
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = _ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  set U := H.toHistory.backwardSurvivorDomain j.succ (H.toHistory.activeStage t) hlj with hUdef
  let y' : U := ⟨pc 0, htr (pc 0) hyS⟩
  let z' : U := ⟨zs, htr zs hzs⟩
  obtain ⟨kz, hkz, hzk⟩ := hzs
  have hz'' := riemannianEDistOf_lt_sqrt_mul_sum_of_ball_chain
    (H.toHistory.stageMetric (H.toHistory.activeStage t) t) U
    (H.toHistory.backwardSurvivorInitialMetric j.succ (H.toHistory.activeStage t) hlj j.succ
      le_rfl hlj) (Real.exp_pos (18 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
        ((t : ℝ) - H.toHistory.time j.succ))) hδ
    (fun k hk w hw => htr w ⟨k, hk, hw⟩) hchain (fun q hq v => hlocal q hq v) y' rfl kz hkz
    z' hzk
  have hmono : ∑ i ∈ Finset.range (kz + 1), δ i ≤ ∑ i ∈ Finset.range (N + 1), δ i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      (fun i hi _ => (hδ i (by have := Finset.mem_range.mp hi; omega)).le)
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
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range (N + 1), δ i :=
    Finset.sum_nonneg fun i hi => (hδ i (by have := Finset.mem_range.mp hi; omega)).le
  set dd := Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
      ((t : ℝ) - H.toHistory.time j.succ)) * ∑ i ∈ Finset.range (N + 1), δ i with hdd
  have hnear : riemannianEDistOf (H.toHistory.initialMetric j.succ)
      (((records j hj).static b).window xz)
      ((Classical.choice (htr (pc 0) hyS)).point j.succ le_rfl hlj) ≤ ENNReal.ofReal dd := by
    rw [hxz, ← hzc, ← hΦz, riemannianEDistOf_comm]
    rw [hexp] at hz''
    refine hmap.trans ?_
    rw [Real.sqrt_one, ENNReal.ofReal_one, one_mul]
    refine hz''.le.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
  have hwin' : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      (Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) *
        ∑ i ∈ Finset.range (N + 1), δ i) < Dcap := by
    rw [← mul_assoc]
    exact hwin
  have hdd' : dd ≤ Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) *
      ((t : ℝ) - u)) * ∑ i ∈ Finset.range (N + 1), δ i := by
    have hu : (u : ℝ) ≤ H.toHistory.time j.succ := hu'u
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hsum0
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  obtain ⟨x, hxn', hxeq⟩ := exists_window_point_of_edist_le_O3L H hacc j (records j hj) (hcan j hj) b hsM hDstar hDmodel xz hxzn _ (hnear.trans (ENNReal.ofReal_le_ofReal hdd'))
    (mul_nonneg (Real.exp_pos _).le hsum0) hwin'
  exact ⟨j, hj, hlj, Classical.choice (htr (pc 0) hyS), b, x, hxeq.symm, hxn', hsM, hage⟩

theorem capWindowPoint_of_chain_point_without_trace_of_activeStage_eq_last_O3L
    (H : RetainedCoreHistory.{u})
    {p : CutoffParameters}
    (T₀ : ℝ)
    (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ → GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i hi b, ((records i hi).static b).hasCanonicalWindow)
    (hscale : ∀ i hi b z, ((records i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records i hi).static b).witness.metric
        (((records i hi).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan M Dcap Dstar θcap : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t) (hT₀u : T₀ ≤ (u : ℝ))
    (h : H.time (Fin.last H.eventCount) < H.horizon)
    (hlastA : H.toHistory.activeStage t = Fin.last H.eventCount)
    (hfinalPinch : Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
      (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    {N : ℕ} (pc : ℕ → (H.toHistory.stage (H.toHistory.activeStage t)).Carrier) (δ : ℕ → ℝ)
    (hδ : ∀ k ≤ N, 0 < δ k)
    (hchain : ∀ k < N, pc (k + 1) ∈
      riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k))
    (z : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hz : ∃ k ≤ N,
      z ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k))
    (hzt : IsEmpty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) z))
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hfinal : ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime
      qcan t)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ k ≤ N, ∀ x ∈ riemannianBallOf
        (H.toHistory.stageMetric (H.toHistory.activeStage t) t) (pc k) (δ k),
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hθ : 4 * M * ((t : ℝ) - u) ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) *
        ∑ i ∈ Finset.range (N + 1), δ i < Dcap) :
    ∃ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ (H.toHistory.activeStage t))
      (A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl (pc 0))
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
        (t : ℝ) - H.time j.succ ≤ θcap * (((records j hj).static b).neck.scale)⁻¹ := by
  obtain ⟨j, hj, hl, A, b, x, hx, hxn, -, hage⟩ :=
    exists_cap_capture_of_chain_point_without_trace_of_comparison_O3L H T₀ records hcan hscale
      hacc hphi hpinch hut hT₀u (fun _ => ⟨h, hfinalPinch⟩)
      (fun q _ hb w => ObservedHistory.initialMetric_inner_le_exp_of_normSq_le_of_eq_last
        H.toHistory hlastA h q (H.toHistory.activeStage_time_le t) t.2.2 hb w)
      pc δ hδ hchain z hz hzt hslabs
      (fun j hj => absurd (hj.trans hlastA) (Fin.castSucc_ne_last j))
      (fun _ _ => hfinal) hM hqcan hspace htime hDstar hDmodel hwin
  refine ⟨j, hj, hl, A, b, x, hx, by linarith, ?_⟩
  rw [← div_eq_mul_inv, le_div_iff₀ ((records j hj).static b).neck.scale_pos]
  linarith

private theorem nonempty_backwardPointTrace_of_chain_of_not_capWindowPoint_aux_O3L
    (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
    (T₀ : ℝ)
    (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ → GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i hi b, ((records i hi).static b).hasCanonicalWindow)
    (hscale : ∀ i hi b z, ((records i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records i hi).static b).witness.metric
        (((records i hi).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan M Dcap Dstar θcap : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t) (hT₀u : T₀ ≤ (u : ℝ))
    (h : H.time (Fin.last H.eventCount) < H.horizon)
    (hlastA : H.toHistory.activeStage t = Fin.last H.eventCount)
    (hfinalPinch : Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
      (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (k : Fin (H.eventCount + 1)) (hk : H.toHistory.activeStage t = k)
    {N : ℕ} (pc : ℕ → (H.toHistory.stage k).Carrier) (δ : ℕ → ℝ)
    (hδ : ∀ j ≤ N, 0 < δ j)
    (hchain : ∀ j < N, pc (j + 1) ∈ riemannianBallOf (H.toHistory.stageMetric k t) (pc j) (δ j))
    (hslabs : H.EventSlabsDerivative Ctime qcan k)
    (hfinal : ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime
      qcan t)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ j ≤ N, ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric k t) (pc j) (δ j),
      metricScalarAt (H.toHistory.stageMetric k t) x ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (hθ : 4 * M * ((t : ℝ) - u) ≤ θcap)
    (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
      Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * ((t : ℝ) - u)) *
        ∑ i ∈ Finset.range (N + 1), δ i < Dcap)
    (hnot : ¬ ∃ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ k)
      (A : BackwardPointTrace H.toHistory j.succ k hl (pc 0))
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
        (t : ℝ) - H.time j.succ ≤ θcap * (((records j hj).static b).neck.scale)⁻¹) :
    ∀ j ≤ N, ∀ z ∈ riemannianBallOf (H.toHistory.stageMetric k t) (pc j) (δ j),
      Nonempty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u) k
        (hk ▸ H.toHistory.activeStage_mono hut) z) := by
  subst hk
  intro j hj z hz
  by_contra hne
  exact hnot (capWindowPoint_of_chain_point_without_trace_of_activeStage_eq_last_O3L H T₀ records
    hcan hscale hacc hphi hpinch hut hT₀u h hlastA hfinalPinch pc δ hδ hchain z ⟨j, hj, hz⟩
    (not_nonempty_iff.mp hne) hslabs hfinal hM hqcan hspace htime hDstar hDmodel hθ hwin)

private theorem sum_range_ite_add_O3L {Nc N : ℕ} (a b : ℕ → ℝ) :
    ∑ j ∈ Finset.range (Nc + N + 1), (if j < Nc then a j else b (j - Nc)) =
      ∑ j ∈ Finset.range Nc, a j + ∑ j ∈ Finset.range (N + 1), b j := by
  rw [show Nc + N + 1 = Nc + (N + 1) by ring, Finset.sum_range_add]
  congr 1
  · exact Finset.sum_congr rfl fun j hj => ite_eq_left (Finset.mem_range.mp hj)
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]

theorem chain_traces_of_not_capWindowPoint_of_incomingSlab_O3L
    (H : RetainedCoreHistory.{u}) (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {t : ℝ} (ht : H.time (Fin.last H.eventCount) < t) (hts : t < s) {θ : ℝ}
    {p : CutoffParameters} (T₀ : ℝ) (hT₀t : T₀ + θ ≤ t)
    (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ → GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i hi b, ((records i hi).static b).hasCanonicalWindow)
    (hscale : ∀ i hi b z, ((records i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records i hi).static b).witness.metric
        (((records i hi).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan Dcap Dstar : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    (hpinchG : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi)
    (hslabs : H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount))
    (hderG : G.DerivativeBoundBefore Ctime qcan t)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (y : (H.stage (Fin.last H.eventCount)).Carrier)
    (hnot : ¬ ∃ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ (Fin.last H.eventCount))
      (A : BackwardPointTrace H.toHistory j.succ (Fin.last H.eventCount) hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
        t - H.time j.succ ≤ θ * (((records j hj).static b).neck.scale)⁻¹)
    {Nc : ℕ} (pc : ℕ → (H.stage (Fin.last H.eventCount)).Carrier) (δc : ℕ → ℝ) (hpc0 : pc 0 = y)
    (hδc : ∀ k < Nc, 0 < δc k)
    (hchainc : ∀ k < Nc, pc (k + 1) ∈
      riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t) (pc k) (δc k))
    {Mc lamc : ℝ}
    (hMc : ∀ k < Nc, ∀ z ∈ riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t)
      (pc k) (δc k), (G.closedPrefix t ht hts).flow.scalar t z ≤ Mc)
    (hlamc : ∑ k ∈ Finset.range Nc, δc k ≤ lamc) :
    ∀ (N : ℕ) (pp : ℕ → (H.stage (Fin.last H.eventCount)).Carrier) (δ : ℕ → ℝ) (M τ : ℝ),
      pp 0 = pc Nc → (∀ k ≤ N, 0 < δ k) →
      (∀ k < N, pp (k + 1) ∈
        riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t) (pp k) (δ k)) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t)
        (pp k) (δ k), (G.closedPrefix t ht hts).flow.scalar t z ≤ M) →
      Mc ≤ M → qcan ≤ M → 1 ≤ M → 0 ≤ τ → τ ≤ t →
      (Ctime : ℝ) * M * τ ≤ 1 / 2 → 4 * M * τ ≤ θ →
      2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * τ) *
          (lamc + ∑ k ∈ Finset.range (N + 1), δ k) < Dcap →
      ∀ k ≤ N, ∀ z ∈ riemannianBallOf ((G.closedPrefix t ht hts).flow.base.metric t)
        (pp k) (δ k),
        ∃ first : Fin (H.eventCount + 1), H.time first ≤ t - τ ∧
          Nonempty (BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
            (Fin.le_last first) z) := by
  intro N pp δ M τ h0 hδ hch hb hMcM hq hM1 hτ0 hτt hC h4 hD k hk z hz
  have hHt : H.horizon ≤ t := hend ▸ ht.le
  set S := G.closedPrefix t ht hts with hSdef
  set H' := H.extendHorizon t hHt S hG with hH'def
  have hh : H'.time (Fin.last H'.eventCount) < H'.horizon := ht
  let t' : Icc (0 : ℝ) H'.toHistory.horizon := ⟨t, H'.horizon_nonneg, le_rfl⟩
  have hu0 : 0 ≤ t - τ := by linarith
  let u' : Icc (0 : ℝ) H'.toHistory.horizon := ⟨t - τ, hu0, by
    change t - τ ≤ t
    linarith⟩
  have hut : u' ≤ t' := by
    change t - τ ≤ t
    linarith
  have hlastA : H'.toHistory.activeStage t' = Fin.last H.eventCount :=
    H.activeStage_extendHorizon_eq_last hHt S hG t' ht.le
  obtain ⟨h, hfp⟩ := RetainedCoreHistory.extendHorizon_finalSlab_phiAlmostNonnegative
    (H := H) (G := G) (hG := hG) (T := t) (hHT := hHt) (hT := ht) (hTs := hts) hpinchG
  have hmet : H'.toHistory.stageMetric (Fin.last H.eventCount) t = S.flow.base.metric t :=
    H.stageMetric_extendHorizon_last hHt S hG ht t
  let records' : ∀ i : Fin H'.eventCount, T₀ ≤ H'.time i.succ →
      GeometricCutoffRecord H'.toHistory i p :=
    fun i hi => (records i hi).extendHorizon t hHt S hG
  let P : ℕ → (H.stage (Fin.last H.eventCount)).Carrier := fun j =>
    if j < Nc then pc j else pp (j - Nc)
  let Δ : ℕ → ℝ := fun j => if j < Nc then δc j else δ (j - Nc)
  have hP0 : P 0 = y := by
    by_cases hN : 0 < Nc
    · exact (ite_eq_left hN).trans hpc0
    · have : Nc = 0 := by omega
      change (if 0 < Nc then pc 0 else pp (0 - Nc)) = y
      rw [ite_eq_right hN, Nat.zero_sub, h0, this, hpc0]
  have hΔ : ∀ j ≤ Nc + N, 0 < Δ j := by
    intro j hj
    by_cases hjc : j < Nc
    · change 0 < (if j < Nc then δc j else δ (j - Nc))
      rw [ite_eq_left hjc]
      exact hδc j hjc
    · change 0 < (if j < Nc then δc j else δ (j - Nc))
      rw [ite_eq_right hjc]
      exact hδ _ (by omega)
  have hchainP : ∀ j < Nc + N, P (j + 1) ∈
      riemannianBallOf (H'.toHistory.stageMetric (Fin.last H.eventCount) t) (P j) (Δ j) := by
    intro j hj
    rw [hmet]
    by_cases hjc : j < Nc
    · change (if j + 1 < Nc then pc (j + 1) else pp (j + 1 - Nc)) ∈
        riemannianBallOf (S.flow.base.metric t)
        (if j < Nc then pc j else pp (j - Nc)) (if j < Nc then δc j else δ (j - Nc))
      rw [ite_eq_left hjc, ite_eq_left hjc]
      by_cases hjc' : j + 1 < Nc
      · rw [ite_eq_left hjc']
        exact hchainc j hjc
      · rw [ite_eq_right hjc', show j + 1 - Nc = 0 by omega, h0, show Nc = j + 1 by omega]
        exact hchainc j (by omega)
    · change (if j + 1 < Nc then pc (j + 1) else pp (j + 1 - Nc)) ∈
        riemannianBallOf (S.flow.base.metric t)
        (if j < Nc then pc j else pp (j - Nc)) (if j < Nc then δc j else δ (j - Nc))
      rw [ite_eq_right hjc, ite_eq_right hjc, ite_eq_right (show ¬ (j + 1 < Nc) by omega),
        show j + 1 - Nc = j - Nc + 1 by omega]
      exact hch (j - Nc) (by omega)
  have hspaceP : ∀ j ≤ Nc + N, ∀ w ∈ riemannianBallOf
      (H'.toHistory.stageMetric (Fin.last H.eventCount) t) (P j) (Δ j),
      metricScalarAt (H'.toHistory.stageMetric (Fin.last H.eventCount) t) w ≤ M := by
    intro j hj w hw
    rw [hmet] at hw ⊢
    by_cases hjc : j < Nc
    · change w ∈ riemannianBallOf (S.flow.base.metric t) (if j < Nc then pc j else pp (j - Nc))
        (if j < Nc then δc j else δ (j - Nc)) at hw
      rw [ite_eq_left hjc, ite_eq_left hjc] at hw
      exact (hMc j hjc w hw).trans hMcM
    · change w ∈ riemannianBallOf (S.flow.base.metric t) (if j < Nc then pc j else pp (j - Nc))
        (if j < Nc then δc j else δ (j - Nc)) at hw
      rw [ite_eq_right hjc, ite_eq_right hjc] at hw
      exact hb _ (by omega) w hw
  have hsum : ∑ j ∈ Finset.range (Nc + N + 1), Δ j ≤ lamc + ∑ j ∈ Finset.range (N + 1), δ j := by
    have := sum_range_ite_add_O3L (Nc := Nc) (N := N) δc δ
    change ∑ j ∈ Finset.range (Nc + N + 1), (if j < Nc then δc j else δ (j - Nc)) ≤ _
    rw [this]
    linarith
  have htu : (t' : ℝ) - u' = τ := by
    change t - (t - τ) = τ
    ring
  have hnot' : ¬ (∃ (j : Fin H'.eventCount) (hj : T₀ ≤ H'.time j.succ) (hl : j.succ ≤ (Fin.last H.eventCount))
      (A : BackwardPointTrace H'.toHistory j.succ (Fin.last H.eventCount) hl (P 0))
      (b : (H'.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records' j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
        t - H'.time j.succ ≤ θ * (((records' j hj).static b).neck.scale)⁻¹) := by
    rw [hP0]
    rintro ⟨j, hj, hl, A, b, xw, h1, h2, h3⟩
    exact hnot ⟨j, hj, hl, ⟨A.point, A.endpoint_eq, A.crossing⟩, b, xw, h1, h2, h3⟩
  have hres := nonempty_backwardPointTrace_of_chain_of_not_capWindowPoint_aux_O3L H' T₀ records'
    (fun i hi b => hcan i hi b) (fun i hi b w => hscale i hi b w) hacc hphi hpinch hut
    (by
      change T₀ ≤ t - τ
      nlinarith [mul_le_mul_of_nonneg_right hM1 hτ0]) hh hlastA hfp
    (Fin.last H.eventCount) hlastA P Δ hΔ hchainP hslabs
    (RetainedCoreHistory.extendHorizon_finalSlab_derivativeBoundBefore (H := H) (G := G)
      (hG := hG) (T := t) (hHT := hHt) (hT := ht) (hTs := hts) hderG le_rfl hh)
    hM1 hq hspaceP (by rw [htu]; exact hC) hDstar hDmodel (by rw [htu]; exact h4)
    (by
      rw [htu]
      refine lt_of_le_of_lt ?_ hD
      have hs0 : 0 ≤ Real.sqrt (8 * M) *
          Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * τ) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
      have := mul_le_mul_of_nonneg_left hsum hs0
      linarith)
    hnot' (Nc + k) (by omega) z (by
      rw [hmet]
      change z ∈ riemannianBallOf (S.flow.base.metric t)
        (if Nc + k < Nc then pc (Nc + k) else pp (Nc + k - Nc))
        (if Nc + k < Nc then δc (Nc + k) else δ (Nc + k - Nc))
      rw [ite_eq_right (show ¬ (Nc + k < Nc) by omega), ite_eq_right (show ¬ (Nc + k < Nc) by omega),
        Nat.add_sub_cancel_left]
      exact hz)
  obtain ⟨A⟩ := hres
  refine ⟨H'.toHistory.activeStage u', ?_, ⟨⟨A.point, A.endpoint_eq, A.crossing⟩⟩⟩
  exact H'.toHistory.activeStage_time_le u'

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private theorem rebase_lam_bound_O3L {A K Q R r₀ L : ℝ} (hA : 0 < A) (hK : 1 ≤ K) (hR : 0 < R)
    (hRQ : R ≤ Q) (hQK : Q ≤ K * R) (hL : 0 < L) (hr₀ : r₀ = L / (2 * Real.sqrt (2 * Q)))
    {N : ℕ} (hN : (N : ℝ) * r₀ ≤ 2 * (A / Real.sqrt R) + 2 * r₀) :
    (N : ℝ) * r₀ ≤ (2 * A * Real.sqrt K + L) / Real.sqrt Q := by
  have hQ : 0 < Q := hR.trans_le hRQ
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have h1 : A / Real.sqrt R ≤ A * Real.sqrt K / Real.sqrt Q := by
    rw [div_le_div_iff₀ hsR hsQ]
    have : Real.sqrt Q ≤ Real.sqrt K * Real.sqrt R := by
      rw [← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt hQK
    nlinarith
  have h2 : 2 * r₀ ≤ L / Real.sqrt Q := by
    rw [hr₀]
    have h2Q : Real.sqrt Q ≤ Real.sqrt (2 * Q) := Real.sqrt_le_sqrt (by linarith)
    rw [show 2 * (L / (2 * Real.sqrt (2 * Q))) = L / Real.sqrt (2 * Q) by field_simp]
    exact div_le_div_of_nonneg_left hL.le hsQ h2Q
  calc (N : ℝ) * r₀ ≤ 2 * (A / Real.sqrt R) + 2 * r₀ := hN
    _ ≤ 2 * (A * Real.sqrt K / Real.sqrt Q) + L / Real.sqrt Q := by linarith
    _ = (2 * A * Real.sqrt K + L) / Real.sqrt Q := by ring

private theorem false_of_terminal_counterexamples_late_O3L {ε : ℝ}
    (heps : 13000 * (13000 * ε) ≤
      min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64))
    {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) {A Cq θ : ℝ} (hA : 0 < A) (hθ : 0 < θ)
    {K : ℝ} (hK : K = max Cq 1) (Dn : ℕ → ℝ) (hDn : Tendsto Dn atTop atTop)
    (H : ℕ → RetainedCoreHistory.{u})
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) (s : ℕ → ℝ)
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    {p : ℕ → CutoffParameters}
    (T₀ : ℕ → ℝ)
    (records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n))
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hscale : ∀ n i hi b z, ((records n i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records n i hi).static b).witness.metric
        (((records n i hi).static b).witness.cap z))
    (hacc : ∀ n, (p n).modelAccuracy ≤ 1 / 2) (hradius : ∀ n, Dn n ≤ (p n).modelRadius)
    (t : ℕ → ℝ) (ht : ∀ n, (H n).time (Fin.last (H n).eventCount) < t n)
    (hts : ∀ n, t n < s n) (hT₀ : ∀ n, T₀ n + θ ≤ t n) (y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (q ρ : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (hqy : ∀ n, q n ≤ Cq * (G n).flow.scalar (t n) (y n))
    (hΛ : ∀ n : ℕ, (n : ℝ) + K + 1 ≤ (G n).flow.scalar (t n) (y n))
    (hΛt : ∀ n : ℕ, (n : ℝ) + K + 1 ≤ (G n).flow.scalar (t n) (y n) * t n)
    (hW : ∀ n x, q n < (G n).flow.scalar (t n) x →
      ∃ W : SpatialCanonicalWitness ((G n).flow.base.metric (t n)) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hslabs : ∀ n, (H n).EventSlabsDerivative Ctime (q n) (Fin.last (H n).eventCount))
    (hder : ∀ n, (G n).DerivativeBoundBefore Ctime (q n) (t n))
    (hgrad : ∀ n, (G n).GradientBoundBefore Cgrad (q n) (t n))
    (hpinch : ∀ n, (H n).EventSlabsPinched phi)
    (hpinchG : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hnc : ∀ n, (∀ (w : ((H n).stage (Fin.last (H n).eventCount)).Carrier),
        riemannianEDistOf ((G n).flow.base.metric (t n)) (y n) w < ENNReal.ofReal (ρ n) →
        ∀ b : ℝ, 0 < b → b ≤ ρ n →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((H n).stage (Fin.last (H n).eventCount)).Carrier
              ((G n).flow.base.metric (t n)) (riemannianBallOf ((G n).flow.base.metric (t n)) w b)))
    (hρ : ∀ n : ℕ, (n : ℝ) + K + 1 ≤ ρ n * Real.sqrt ((G n).flow.scalar (t n) (y n)))
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < Dn n + 1 ∧
        t n - (H n).time j.succ ≤ θ * (((records n j hj).static b).neck.scale)⁻¹)
    (z : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (hz : ∀ n, z n ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (y n)
      (A / Real.sqrt ((G n).flow.scalar (t n) (y n))))
    (hbad : ∀ n : ℕ, ((n : ℝ) + K + 1) * (G n).flow.scalar (t n) (y n) <
      (G n).flow.scalar (t n) (z n)) : False := by
  have hK1 : 1 ≤ K := hK ▸ le_max_right _ _
  have hn0 (n : ℕ) : (0 : ℝ) ≤ n := n.cast_nonneg
  have hRpos (n : ℕ) : 0 < (G n).flow.scalar (t n) (y n) := by linarith [hΛ n, hn0 n]
  have hqK (n : ℕ) : q n ≤ K * (G n).flow.scalar (t n) (y n) :=
    (hqy n).trans (mul_le_mul_of_nonneg_right (hK ▸ le_max_left _ _) (hRpos n).le)
  let Asl : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).ClosedSlab
      ((H n).time (Fin.last (H n).eventCount)) (t n) := fun n =>
    (G n).closedPrefix (t n) (ht n) (hts n)
  have hzmax (n : ℕ) : max (q n) ((G n).flow.scalar (t n) (y n)) ≤
      (G n).flow.scalar (t n) (z n) := by
    refine max_le ?_ ?_
    · nlinarith [hbad n, hqK n, hRpos n, hn0 n]
    · nlinarith [hbad n, hRpos n, hn0 n]
  choose xc Nc pc hxc hxy hpc0 hpcN hchainc hMc hNc using fun n =>
    (Asl n).exists_rebase_chain Cgrad (hq n) (fun y' t' ht' hq' v => hgrad n y' t' ht' hq' v)
      (y n) (z n) (hz n) (hzmax n)
  have hQy (n : ℕ) : (G n).flow.scalar (t n) (y n) ≤ max (q n) ((G n).flow.scalar (t n) (y n)) :=
    le_max_right _ _
  have hQK (n : ℕ) : max (q n) ((G n).flow.scalar (t n) (y n)) ≤
      K * (G n).flow.scalar (t n) (y n) :=
    max_le (hqK n) (le_mul_of_one_le_left (hRpos n).le hK1)
  have hU (n : ℕ) (w : ((H n).stage (Fin.last (H n).eventCount)).Carrier) :
      w ∈ ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen := by
    change w ∈ ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularRegion
    rw [(Asl n).terminalRegularRegion_eq_univ _]
    trivial
  let x : ∀ n, ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen :=
    fun n => ⟨xc n, hU n (xc n)⟩
  have hxQ (n : ℕ) : (Asl n).flow.scalar (t n) (x n).val =
      max (q n) ((G n).flow.scalar (t n) (y n)) := hxc n
  have hQ1 (n : ℕ) : 1 ≤ (Asl n).flow.scalar (t n) (x n).val := by
    rw [hxQ n]
    linarith [hQy n, hΛ n, hn0 n]
  have hlp := localPropagationRadius_pos Cgrad.coe_nonneg
  have hr₀ (n : ℕ) : 0 < localPropagationRadius Cgrad /
      (2 * Real.sqrt (2 * max (q n) ((G n).flow.scalar (t n) (y n)))) := by
    have : 0 < max (q n) ((G n).flow.scalar (t n) (y n)) := (hq n).trans_le (le_max_left _ _)
    positivity
  have hlamc (n : ℕ) : ∑ k ∈ Finset.range (Nc n), (fun _ : ℕ => localPropagationRadius Cgrad /
      (2 * Real.sqrt (2 * max (q n) ((G n).flow.scalar (t n) (y n))))) k ≤
      (2 * A * Real.sqrt K + localPropagationRadius Cgrad) /
        Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hxQ n]
    exact rebase_lam_bound_O3L hA hK1 (hRpos n) (hQy n) (hQK n) hlp rfl (hNc n)
  have htr (n : ℕ) := chain_traces_of_not_capWindowPoint_of_incomingSlab_O3L
    (H n) (hend n) (G n) (hG n) (ht n) (hts n) (T₀ n) (hT₀ n) (records n) (hcan n) (hscale n) (hacc n) hphi
    (hpinch n) (hpinchG n) (hslabs n) (hder n) le_rfl (hradius n) (y n) (hnot n) (pc n)
    (fun _ => localPropagationRadius Cgrad /
      (2 * Real.sqrt (2 * max (q n) ((G n).flow.scalar (t n) (y n))))) (hpc0 n)
    (fun _ _ => hr₀ n) (hchainc n) (hMc n) (hlamc n)
  have hlam : 0 ≤ 2 * A * Real.sqrt K + localPropagationRadius Cgrad := by positivity
  have hDn' : Tendsto Dn atTop atTop := hDn
  have hQlim : Tendsto (fun n => (Asl n).flow.scalar (t n) (x n).val) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    rw [hxQ n]
    linarith [hQy n, hΛ n, hK1]
  have htime : Tendsto (fun n => (Asl n).flow.scalar (t n) (x n).val * t n) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    have ht0 : 0 ≤ t n := ((H n).toHistory.time_nonneg _).trans (ht n).le
    rw [hxQ n]
    have := mul_le_mul_of_nonneg_right (hQy n) ht0
    linarith [hΛt n, hK1]
  let σ : ℕ → ℝ := fun n => ρ n - A / Real.sqrt ((G n).flow.scalar (t n) (y n))
  have hσlim : Tendsto (fun n => σ n * Real.sqrt ((Asl n).flow.scalar (t n) (x n).val))
      atTop atTop := by
    have hbase : Tendsto (fun n : ℕ => (n : ℝ) + (K + 1 - A)) atTop atTop :=
      tendsto_atTop_add_const_right atTop _ tendsto_natCast_atTop_atTop
    refine tendsto_atTop_mono' atTop ?_ hbase
    filter_upwards [eventually_ge_atTop ⌈A⌉₊] with n hn
    have hsy := Real.sqrt_pos.mpr (hRpos n)
    have hid : σ n * Real.sqrt ((G n).flow.scalar (t n) (y n)) =
        ρ n * Real.sqrt ((G n).flow.scalar (t n) (y n)) - A := by
      change (ρ n - A / Real.sqrt ((G n).flow.scalar (t n) (y n))) *
        Real.sqrt ((G n).flow.scalar (t n) (y n)) = _
      field_simp
    have hAn : A ≤ (n : ℝ) := (Nat.le_ceil A).trans (by exact_mod_cast hn)
    have hρn := hρ n
    have hlow : (n : ℝ) + (K + 1 - A) ≤ σ n * Real.sqrt ((G n).flow.scalar (t n) (y n)) := by
      rw [hid]; linarith
    have hσ0 : 0 ≤ σ n := by
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_neg_of_pos hneg hsy
      linarith
    rw [hxQ n]
    exact hlow.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hQy n)) hσ0)
  have hloc : ∀ n (zz : ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen),
      riemannianEDistOf ((Asl n).endpointTerminalLimitMetric
        ((H n).stage (Fin.last (H n).eventCount))).metric (x n) zz < ENNReal.ofReal (σ n) →
      ∀ b : ℝ, 0 < b → b ≤ σ n →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel
            ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen
            ((Asl n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric
            (riemannianBallOf ((Asl n).endpointTerminalLimitMetric
              ((H n).stage (Fin.last (H n).eventCount))).metric zz b) := by
    intro n zz hzz b hb hbσ
    have hsy := Real.sqrt_pos.mpr (hRpos n)
    have ha'0 : 0 ≤ A / Real.sqrt ((G n).flow.scalar (t n) (y n)) := div_nonneg hA.le hsy.le
    have hσpos : 0 < σ n := hb.trans_le hbσ
    have hσρ : σ n ≤ ρ n := by
      change ρ n - A / Real.sqrt ((G n).flow.scalar (t n) (y n)) ≤ ρ n; linarith
    rw [(Asl n).riemannianEDistOf_endpointTerminalLimitMetric] at hzz
    have hyz : riemannianEDistOf ((G n).flow.base.metric (t n)) (y n) zz.val <
        ENNReal.ofReal (ρ n) := by
      calc riemannianEDistOf ((G n).flow.base.metric (t n)) (y n) zz.val
          ≤ riemannianEDistOf ((G n).flow.base.metric (t n)) (y n) (xc n) +
              riemannianEDistOf ((G n).flow.base.metric (t n)) (xc n) zz.val :=
            riemannianEDistOf_triangle _ _ _ _
        _ < ENNReal.ofReal (A / Real.sqrt ((G n).flow.scalar (t n) (y n))) +
            ENNReal.ofReal (σ n) := ENNReal.add_lt_add (hxy n) hzz
        _ = ENNReal.ofReal (ρ n) := by
            rw [← ENNReal.ofReal_add ha'0 hσpos.le]
            congr 1
            change A / Real.sqrt ((G n).flow.scalar (t n) (y n)) +
              (ρ n - A / Real.sqrt ((G n).flow.scalar (t n) (y n))) = ρ n
            ring
    have hv := hnc n zz.val hyz b hb (hbσ.trans hσρ)
    have hUc : IsClosed ((((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen :
        TopologicalSpace.Opens ((H n).stage (Fin.last (H n).eventCount)).Carrier) :
          Set ((H n).stage (Fin.last (H n).eventCount)).Carrier) := by
      change IsClosed ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularRegion
      rw [(Asl n).terminalRegularRegion_eq_univ _]
      exact isClosed_univ
    have heq := riemannianVolumeMeasure_ball_restrictOpen_of_isClosed
      ((Asl n).flow.base.metric (t n))
      ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen hUc zz b
    dsimp only at heq
    change _ ≤ riemannianVolumeMeasure ThreeModel
      ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen
      (((Asl n).flow.base.metric (t n)).restrictOpen
        ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen)
      (riemannianBallOf (((Asl n).flow.base.metric (t n)).restrictOpen
        ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen) zz b)
    rw [heq]
    exact hv
  obtain ⟨B, hB⟩ := exists_normalized_scalar_bound_of_chain_traces_local_O3
    H t Asl (fun n => hG n) (fun n => (hend n) ▸ ht n) Ctime Cgrad q hq
    (fun n j y' t' ht' hq' => hslabs n j (Fin.castSucc_lt_last j) y' t' ht' hq')
    (fun n y' t' ht' hq' => hder n y' t' ht' hq')
    (fun n y' t' ht' hq' v => hgrad n y' t' ht' hq' v) x hQ1
    (fun n => by rw [hxQ n]; exact le_max_left _ _) hQlim hphi (fun n => hpinch n)
    (fun n τ hτ w => hpinchG n τ ⟨hτ.1, hτ.2.trans (hts n)⟩ w) σ hκ hσlim hloc
    heps (fun n => hW n) htime (Kc := 6) hlam hθ Dn hDn'
    (fun n N pp δ M τ h0 hδ hch hb hKc h1 hτ0 hτt hC h4 hDD =>
      htr n N pp δ M τ (h0.trans (hpcN n).symm) hδ hch hb
        (by rw [hxQ n] at hKc; exact hKc) (by
          rw [hxQ n] at hKc
          have := le_max_left (q n) ((G n).flow.scalar (t n) (y n))
          linarith) h1 hτ0 hτt hC h4 hDD)
    (2 * A * Real.sqrt K + 1) (by positivity)
  obtain ⟨n, hn, hnB⟩ := (hB.and (eventually_gt_atTop ⌈B * K⌉₊)).exists
  let z' : ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen :=
    ⟨z n, hU n (z n)⟩
  have hsx : 0 < Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le (hQ1 n))
  have hsy : 0 < Real.sqrt ((G n).flow.scalar (t n) (y n)) := Real.sqrt_pos.mpr (hRpos n)
  have hratio : Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) ≤
      Real.sqrt K * Real.sqrt ((G n).flow.scalar (t n) (y n)) := by
    rw [← Real.sqrt_mul (by linarith), hxQ n]
    exact Real.sqrt_le_sqrt (hQK n)
  have hxz : riemannianEDistOf ((G n).flow.base.metric (t n)) (xc n) (z n) <
      ENNReal.ofReal (2 * (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))) := by
    calc riemannianEDistOf ((G n).flow.base.metric (t n)) (xc n) (z n)
        ≤ riemannianEDistOf ((G n).flow.base.metric (t n)) (xc n) (y n) +
          riemannianEDistOf ((G n).flow.base.metric (t n)) (y n) (z n) :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal (A / Real.sqrt ((G n).flow.scalar (t n) (y n))) +
          ENNReal.ofReal (A / Real.sqrt ((G n).flow.scalar (t n) (y n))) := by
          rw [riemannianEDistOf_comm]
          exact ENNReal.add_lt_add (hxy n) (hz n)
      _ = ENNReal.ofReal (2 * (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))) := by
          rw [← ENNReal.ofReal_add (div_nonneg hA.le (Real.sqrt_nonneg _))
            (div_nonneg hA.le (Real.sqrt_nonneg _))]
          ring_nf
  have hdist : riemannianEDistOf (scaleMetric ((Asl n).flow.scalar (t n) (x n).val)
      (zero_lt_one.trans_le (hQ1 n))
      ((Asl n).endpointTerminalLimitMetric _).metric) (x n) z' <
        ENNReal.ofReal (2 * A * Real.sqrt K + 1) := by
    rw [(Asl n).scaled_endpoint_edist_eq]
    calc ENNReal.ofReal (Real.sqrt ((Asl n).flow.scalar (t n) (x n).val)) *
          riemannianEDistOf ((Asl n).flow.base.metric (t n)) (x n).val z'.val <
        ENNReal.ofReal (Real.sqrt ((Asl n).flow.scalar (t n) (x n).val)) *
          ENNReal.ofReal (2 * (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))) :=
          ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hsx).ne' ENNReal.ofReal_ne_top hxz
      _ = ENNReal.ofReal (Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) *
          (2 * (A / Real.sqrt ((G n).flow.scalar (t n) (y n))))) :=
          (ENNReal.ofReal_mul hsx.le).symm
      _ ≤ ENNReal.ofReal (2 * A * Real.sqrt K) := by
          apply ENNReal.ofReal_le_ofReal
          rw [show Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) *
            (2 * (A / Real.sqrt ((G n).flow.scalar (t n) (y n)))) =
            2 * A * (Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) /
              Real.sqrt ((G n).flow.scalar (t n) (y n))) by ring]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_iff₀ hsy]
          exact hratio
      _ < ENNReal.ofReal (2 * A * Real.sqrt K + 1) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  have hle := hn z' hdist
  have hscal : metricScalarAt ((Asl n).endpointTerminalLimitMetric _).metric z' =
      (G n).flow.scalar (t n) (z n) := metricScalarAt_restrictOpen _ _ _
  rw [hscal, div_le_iff₀ (zero_lt_one.trans_le (hQ1 n)), hxQ n] at hle
  have hceil : B * K ≤ (n : ℝ) := (Nat.le_ceil (B * K)).trans (by exact_mod_cast hnB.le)
  have hbig := hbad n
  have hQKn := hQK n
  have hRyn := hRpos n
  have hn1 := hn0 n
  rcases le_or_gt 0 B with hB0 | hB0
  · have h1 : B * max (q n) ((G n).flow.scalar (t n) (y n)) ≤
        B * (K * (G n).flow.scalar (t n) (y n)) := mul_le_mul_of_nonneg_left hQKn hB0
    have h2 : B * K * (G n).flow.scalar (t n) (y n) ≤ n * (G n).flow.scalar (t n) (y n) :=
      mul_le_mul_of_nonneg_right hceil hRyn.le
    nlinarith
  · have h1 : B * max (q n) ((G n).flow.scalar (t n) (y n)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hB0.le (by linarith [hQy n])
    nlinarith

theorem exists_scalar_bound_at_distance_of_not_capWindowPoint_terminal_late_O3L
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq θ : ℝ) (hθ : 0 < θ) :
    ∃ Q Λ Dcap Rrad ζ₀ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧ Dcap ≤ Rrad ∧
    0 < ζ₀ ∧
    ∀ (H : RetainedCoreHistory.{u})
      (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount))
      (T₀ : ℝ) {p : CutoffParameters}
      (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ → GeometricCutoffRecord H.toHistory i p),
      (∀ i hi b, ((records i hi).static b).hasCanonicalWindow) →
      Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
      ∀ {t : ℝ} (_ : H.time (Fin.last H.eventCount) < t) (_ : t < s), T₀ + θ ≤ t →
      ∀ (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
      0 < q → q ≤ Cq * G.flow.scalar t y → Λ ≤ G.flow.scalar t y →
      Λ ≤ G.flow.scalar t y * t →
      (∀ x, q < G.flow.scalar t x →
        ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 x,
          W.capTubeHasNeckChart ε) →
      H.EventSlabsDerivative Ctime q (Fin.last H.eventCount) →
      G.DerivativeBoundBefore Ctime q t → G.GradientBoundBefore Cgrad q t →
      H.EventSlabsPinched phi →
      Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
      (∀ (w : ((H).stage (Fin.last (H).eventCount)).Carrier),
        riemannianEDistOf ((G).flow.base.metric (t)) (y) w < ENNReal.ofReal (ρ) →
        ∀ b : ℝ, 0 < b → b ≤ ρ →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((H).stage (Fin.last (H).eventCount)).Carrier
              ((G).flow.base.metric (t)) (riemannianBallOf ((G).flow.base.metric (t)) w b)) →
      Λ ≤ ρ * Real.sqrt (G.flow.scalar t y) →
      (¬ ∃ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ Fin.last H.eventCount)
        (A : BackwardPointTrace H.toHistory j.succ (Fin.last H.eventCount) hl y)
        (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        A.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
          t - H.time j.succ ≤ θ * (((records j hj).static b).neck.scale)⁻¹) →
      ∀ z ∈ riemannianBallOf (G.flow.base.metric t) y (A / Real.sqrt (G.flow.scalar t y)),
        G.flow.scalar t z ≤ Q * G.flow.scalar t y := by
  have heps : 13000 * (13000 * ε) ≤
      min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) := by
    unfold coneAccuracy at hεle
    have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 13000 * 13000)).mp hεle
    linarith
  have hTE := StandardCap.transitionEnd_pos
  have hn0 (n : ℕ) : (0 : ℝ) ≤ n := n.cast_nonneg
  have hDn (n : ℕ) : StandardCap.transitionEnd < StandardCap.transitionEnd + 1 + n := by
    linarith [hn0 n]
  have hK1 : (1 : ℝ) ≤ max Cq 1 := le_max_right _ _
  choose ε₀ hε₀ hsc using fun n : ℕ =>
    exists_presented_cap_scalar_lower_bound_of_canonical_window_core.{u}
      (StandardCap.transitionEnd + 1 + n) (hDn n)
  by_contra hcon
  push Not at hcon
  choose H hend s G hG T₀ p records hcan hRrad hord hζ t ht hts hT₀ y q ρ hq hqy hΛ hΛt hW
    hslabs hder hgrad hpinch hpinchG hnc hρ hnot z hz hbad using fun n : ℕ =>
    hcon ((n : ℝ) + max Cq 1 + 1) ((n : ℝ) + max Cq 1 + 1) (StandardCap.transitionEnd + 1 + n)
      (StandardCap.transitionEnd + 1 + n) (min (1 / 2) (ε₀ n)) (by linarith [hn0 n])
      (by linarith [hn0 n]) (hDn n) le_rfl (lt_min (by norm_num) (hε₀ n))
  have hradius (n : ℕ) : StandardCap.transitionEnd + 1 + n ≤ (p n).modelRadius := hRrad n
  have hacc (n : ℕ) : (p n).modelAccuracy ≤ 1 / 2 := (hζ n).trans (min_le_left _ _)
  have hscale (n : ℕ) (i : Fin (H n).eventCount) (hi : T₀ n ≤ (H n).time i.succ)
      (b : ((H n).toHistory.event i).RetainedBoundaryIndex) (w : ThreeBall) :
      ((records n i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records n i hi).static b).witness.metric
        (((records n i hi).static b).witness.cap w) :=
    hsc n ((H n).toHistory.event i) (hradius n) ((hζ n).trans (min_le_right _ _))
      (hord n) ((records n i hi).static b) (hcan n i hi b) w
  refine false_of_terminal_counterexamples_late_O3L heps hκ hphi hA hθ rfl
    (fun n => StandardCap.transitionEnd + 1 + n) ?_ H hend s G hG T₀ records hcan hscale hacc
    hradius t ht hts hT₀ y q ρ hq hqy hΛ hΛt hW hslabs hder hgrad hpinch hpinchG hnc hρ
    (fun n ⟨j, hj, hl, A, b, x, h1, h2, h3⟩ => absurd h3 (not_le.mpr (hnot n j hj hl A b x h1 h2)))
    z hz hbad
  exact tendsto_atTop_add_const_left atTop _ tendsto_natCast_atTop_atTop


theorem chain_traces_of_not_capWindowPoint_of_closedSlab_O3L
    (H : RetainedCoreHistory.{u}) (hend : H.time (Fin.last H.eventCount) = H.horizon) {t : ℝ}
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) t)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {θ : ℝ}
    {p : CutoffParameters} (T₀ : ℝ) (hT₀t : T₀ + θ ≤ t)
    (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ → GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i hi b, ((records i hi).static b).hasCanonicalWindow)
    (hscale : ∀ i hi b z, ((records i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records i hi).static b).witness.metric
        (((records i hi).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2)
    {Ctime : ℝ≥0} {qcan Dcap Dstar : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    (hpinchS : Perelman.PhiAlmostNonnegative S.flow (Icc (H.time (Fin.last H.eventCount)) t) phi)
    (hslabs : H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount))
    (hderS : (S.restrictIncoming le_rfl S.lt le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hDstar : Dcap ≤ Dstar) (hDmodel : Dstar ≤ p.modelRadius)
    (y : (H.stage (Fin.last H.eventCount)).Carrier)
    (hnot : ¬ ∃ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ (Fin.last H.eventCount))
      (A : BackwardPointTrace H.toHistory j.succ (Fin.last H.eventCount) hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
        t - H.time j.succ ≤ θ * (((records j hj).static b).neck.scale)⁻¹)
    {Nc : ℕ} (pc : ℕ → (H.stage (Fin.last H.eventCount)).Carrier) (δc : ℕ → ℝ) (hpc0 : pc 0 = y)
    (hδc : ∀ k < Nc, 0 < δc k)
    (hchainc : ∀ k < Nc, pc (k + 1) ∈
      riemannianBallOf (S.flow.base.metric t) (pc k) (δc k))
    {Mc lamc : ℝ}
    (hMc : ∀ k < Nc, ∀ z ∈ riemannianBallOf (S.flow.base.metric t)
      (pc k) (δc k), S.flow.scalar t z ≤ Mc)
    (hlamc : ∑ k ∈ Finset.range Nc, δc k ≤ lamc) :
    ∀ (N : ℕ) (pp : ℕ → (H.stage (Fin.last H.eventCount)).Carrier) (δ : ℕ → ℝ) (M τ : ℝ),
      pp 0 = pc Nc → (∀ k ≤ N, 0 < δ k) →
      (∀ k < N, pp (k + 1) ∈
        riemannianBallOf (S.flow.base.metric t) (pp k) (δ k)) →
      (∀ k ≤ N, ∀ z ∈ riemannianBallOf (S.flow.base.metric t)
        (pp k) (δ k), S.flow.scalar t z ≤ M) →
      Mc ≤ M → qcan ≤ M → 1 ≤ M → 0 ≤ τ → τ ≤ t →
      (Ctime : ℝ) * M * τ ≤ 1 / 2 → 4 * M * τ ≤ θ →
      2 * StandardCap.transitionEnd + Real.sqrt (8 * M) *
        Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * τ) *
          (lamc + ∑ k ∈ Finset.range (N + 1), δ k) < Dcap →
      ∀ k ≤ N, ∀ z ∈ riemannianBallOf (S.flow.base.metric t)
        (pp k) (δ k),
        ∃ first : Fin (H.eventCount + 1), H.time first ≤ t - τ ∧
          Nonempty (BackwardPointTrace H.toHistory first (Fin.last H.eventCount)
            (Fin.le_last first) z) := by
  intro N pp δ M τ h0 hδ hch hb hMcM hq hM1 hτ0 hτt hC h4 hD k hk z hz
  have ht : H.time (Fin.last H.eventCount) < t := S.lt
  have hHt : H.horizon ≤ t := hend ▸ ht.le
  set H' := H.extendHorizon t hHt S hS with hH'def
  have hh : H'.time (Fin.last H'.eventCount) < H'.horizon := ht
  let t' : Icc (0 : ℝ) H'.toHistory.horizon := ⟨t, H'.horizon_nonneg, le_rfl⟩
  have hu0 : 0 ≤ t - τ := by linarith
  let u' : Icc (0 : ℝ) H'.toHistory.horizon := ⟨t - τ, hu0, by
    change t - τ ≤ t
    linarith⟩
  have hut : u' ≤ t' := by
    change t - τ ≤ t
    linarith
  have hlastA : H'.toHistory.activeStage t' = Fin.last H.eventCount :=
    H.activeStage_extendHorizon_eq_last hHt S hS t' ht.le
  obtain ⟨h, hfp⟩ : ∃ h : H.time (Fin.last H.eventCount) < (H.extendHorizon t hHt S hS).horizon,
      Perelman.PhiAlmostNonnegative ((H.extendHorizon t hHt S hS).finalSlab h).flow
        (Icc (H.time (Fin.last H.eventCount)) (H.extendHorizon t hHt S hS).horizon) phi :=
    ⟨ht, fun v hv x => hpinchS v hv x⟩
  have hmet : H'.toHistory.stageMetric (Fin.last H.eventCount) t = S.flow.base.metric t :=
    H.stageMetric_extendHorizon_last hHt S hS ht t
  let records' : ∀ i : Fin H'.eventCount, T₀ ≤ H'.time i.succ →
      GeometricCutoffRecord H'.toHistory i p :=
    fun i hi => (records i hi).extendHorizon t hHt S hS
  let P : ℕ → (H.stage (Fin.last H.eventCount)).Carrier := fun j =>
    if j < Nc then pc j else pp (j - Nc)
  let Δ : ℕ → ℝ := fun j => if j < Nc then δc j else δ (j - Nc)
  have hP0 : P 0 = y := by
    by_cases hN : 0 < Nc
    · exact (ite_eq_left hN).trans hpc0
    · have : Nc = 0 := by omega
      change (if 0 < Nc then pc 0 else pp (0 - Nc)) = y
      rw [ite_eq_right hN, Nat.zero_sub, h0, this, hpc0]
  have hΔ : ∀ j ≤ Nc + N, 0 < Δ j := by
    intro j hj
    by_cases hjc : j < Nc
    · change 0 < (if j < Nc then δc j else δ (j - Nc))
      rw [ite_eq_left hjc]
      exact hδc j hjc
    · change 0 < (if j < Nc then δc j else δ (j - Nc))
      rw [ite_eq_right hjc]
      exact hδ _ (by omega)
  have hchainP : ∀ j < Nc + N, P (j + 1) ∈
      riemannianBallOf (H'.toHistory.stageMetric (Fin.last H.eventCount) t) (P j) (Δ j) := by
    intro j hj
    rw [hmet]
    by_cases hjc : j < Nc
    · change (if j + 1 < Nc then pc (j + 1) else pp (j + 1 - Nc)) ∈
        riemannianBallOf (S.flow.base.metric t)
        (if j < Nc then pc j else pp (j - Nc)) (if j < Nc then δc j else δ (j - Nc))
      rw [ite_eq_left hjc, ite_eq_left hjc]
      by_cases hjc' : j + 1 < Nc
      · rw [ite_eq_left hjc']
        exact hchainc j hjc
      · rw [ite_eq_right hjc', show j + 1 - Nc = 0 by omega, h0, show Nc = j + 1 by omega]
        exact hchainc j (by omega)
    · change (if j + 1 < Nc then pc (j + 1) else pp (j + 1 - Nc)) ∈
        riemannianBallOf (S.flow.base.metric t)
        (if j < Nc then pc j else pp (j - Nc)) (if j < Nc then δc j else δ (j - Nc))
      rw [ite_eq_right hjc, ite_eq_right hjc, ite_eq_right (show ¬ (j + 1 < Nc) by omega),
        show j + 1 - Nc = j - Nc + 1 by omega]
      exact hch (j - Nc) (by omega)
  have hspaceP : ∀ j ≤ Nc + N, ∀ w ∈ riemannianBallOf
      (H'.toHistory.stageMetric (Fin.last H.eventCount) t) (P j) (Δ j),
      metricScalarAt (H'.toHistory.stageMetric (Fin.last H.eventCount) t) w ≤ M := by
    intro j hj w hw
    rw [hmet] at hw ⊢
    by_cases hjc : j < Nc
    · change w ∈ riemannianBallOf (S.flow.base.metric t) (if j < Nc then pc j else pp (j - Nc))
        (if j < Nc then δc j else δ (j - Nc)) at hw
      rw [ite_eq_left hjc, ite_eq_left hjc] at hw
      exact (hMc j hjc w hw).trans hMcM
    · change w ∈ riemannianBallOf (S.flow.base.metric t) (if j < Nc then pc j else pp (j - Nc))
        (if j < Nc then δc j else δ (j - Nc)) at hw
      rw [ite_eq_right hjc, ite_eq_right hjc] at hw
      exact hb _ (by omega) w hw
  have hsum : ∑ j ∈ Finset.range (Nc + N + 1), Δ j ≤ lamc + ∑ j ∈ Finset.range (N + 1), δ j := by
    have := sum_range_ite_add_O3L (Nc := Nc) (N := N) δc δ
    change ∑ j ∈ Finset.range (Nc + N + 1), (if j < Nc then δc j else δ (j - Nc)) ≤ _
    rw [this]
    linarith
  have htu : (t' : ℝ) - u' = τ := by
    change t - (t - τ) = τ
    ring
  have hnot' : ¬ (∃ (j : Fin H'.eventCount) (hj : T₀ ≤ H'.time j.succ) (hl : j.succ ≤ (Fin.last H.eventCount))
      (A : BackwardPointTrace H'.toHistory j.succ (Fin.last H.eventCount) hl (P 0))
      (b : (H'.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records' j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
        t - H'.time j.succ ≤ θ * (((records' j hj).static b).neck.scale)⁻¹) := by
    rw [hP0]
    rintro ⟨j, hj, hl, A, b, xw, h1, h2, h3⟩
    exact hnot ⟨j, hj, hl, ⟨A.point, A.endpoint_eq, A.crossing⟩, b, xw, h1, h2, h3⟩
  have hres := nonempty_backwardPointTrace_of_chain_of_not_capWindowPoint_aux_O3L H' T₀ records'
    (fun i hi b => hcan i hi b) (fun i hi b w => hscale i hi b w) hacc hphi hpinch hut
    (by
      change T₀ ≤ t - τ
      nlinarith [mul_le_mul_of_nonneg_right hM1 hτ0]) hh hlastA hfp
    (Fin.last H.eventCount) hlastA P Δ hΔ hchainP hslabs
    (fun y' v hv hq' => hderS y' v hv hq')
    hM1 hq hspaceP (by rw [htu]; exact hC) hDstar hDmodel (by rw [htu]; exact h4)
    (by
      rw [htu]
      refine lt_of_le_of_lt ?_ hD
      have hs0 : 0 ≤ Real.sqrt (8 * M) *
          Real.exp (9 * (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) * τ) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
      have := mul_le_mul_of_nonneg_left hsum hs0
      linarith)
    hnot' (Nc + k) (by omega) z (by
      rw [hmet]
      change z ∈ riemannianBallOf (S.flow.base.metric t)
        (if Nc + k < Nc then pc (Nc + k) else pp (Nc + k - Nc))
        (if Nc + k < Nc then δc (Nc + k) else δ (Nc + k - Nc))
      rw [ite_eq_right (show ¬ (Nc + k < Nc) by omega), ite_eq_right (show ¬ (Nc + k < Nc) by omega),
        Nat.add_sub_cancel_left]
      exact hz)
  obtain ⟨A⟩ := hres
  refine ⟨H'.toHistory.activeStage u', ?_, ⟨⟨A.point, A.endpoint_eq, A.crossing⟩⟩⟩
  exact H'.toHistory.activeStage_time_le u'

private theorem false_of_closed_counterexamples_late_O3L {ε : ℝ}
    (heps : 13000 * (13000 * ε) ≤
      min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64))
    {κ C1 C2 : ℝ} (hκ : 0 < κ) {Ctime Cgrad : ℝ≥0} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) {A Cq θ : ℝ} (hA : 0 < A) (hθ : 0 < θ)
    {K : ℝ} (hK : K = max Cq 1) (Dn : ℕ → ℝ) (hDn : Tendsto Dn atTop atTop)
    (H : ℕ → RetainedCoreHistory.{u})
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) (t : ℕ → ℝ)
    (S : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).ClosedSlab
      ((H n).time (Fin.last (H n).eventCount)) (t n))
    (hS : ∀ n, (S n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    {p : ℕ → CutoffParameters}
    (T₀ : ℕ → ℝ)
    (records : ∀ n (i : Fin (H n).eventCount), T₀ n ≤ (H n).time i.succ →
      GeometricCutoffRecord (H n).toHistory i (p n))
    (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow)
    (hscale : ∀ n i hi b z, ((records n i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records n i hi).static b).witness.metric
        (((records n i hi).static b).witness.cap z))
    (hacc : ∀ n, (p n).modelAccuracy ≤ 1 / 2) (hradius : ∀ n, Dn n ≤ (p n).modelRadius)
    (hT₀ : ∀ n, T₀ n + θ ≤ t n) (y : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (q ρ : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (hqy : ∀ n, q n ≤ Cq * (S n).flow.scalar (t n) (y n))
    (hΛ : ∀ n : ℕ, (n : ℝ) + K + 1 ≤ (S n).flow.scalar (t n) (y n))
    (hΛt : ∀ n : ℕ, (n : ℝ) + K + 1 ≤ (S n).flow.scalar (t n) (y n) * t n)
    (hW : ∀ n x, q n < (S n).flow.scalar (t n) x →
      ∃ W : SpatialCanonicalWitness ((S n).flow.base.metric (t n)) ε C1 C2 x,
        W.capTubeHasNeckChart ε)
    (hslabs : ∀ n, (H n).EventSlabsDerivative Ctime (q n) (Fin.last (H n).eventCount))
    (hder : ∀ n, ((S n).restrictIncoming le_rfl (S n).lt le_rfl).DerivativeBoundBefore Ctime (q n) (t n))
    (hgrad : ∀ n, ((S n).restrictIncoming le_rfl (S n).lt le_rfl).GradientBoundBefore Cgrad (q n) (t n))
    (hpinch : ∀ n, (H n).EventSlabsPinched phi)
    (hpinchS : ∀ n, Perelman.PhiAlmostNonnegative (S n).flow
      (Icc ((H n).time (Fin.last (H n).eventCount)) (t n)) phi)
    (hnc : ∀ n, (∀ (w : ((H n).stage (Fin.last (H n).eventCount)).Carrier),
        riemannianEDistOf ((S n).flow.base.metric (t n)) (y n) w < ENNReal.ofReal (ρ n) →
        ∀ b : ℝ, 0 < b → b ≤ ρ n →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((H n).stage (Fin.last (H n).eventCount)).Carrier
              ((S n).flow.base.metric (t n)) (riemannianBallOf ((S n).flow.base.metric (t n)) w b)))
    (hρ : ∀ n : ℕ, (n : ℝ) + K + 1 ≤ ρ n * Real.sqrt ((S n).flow.scalar (t n) (y n)))
    (hnot : ∀ n, ¬ ∃ (j : Fin (H n).eventCount) (hj : T₀ n ≤ (H n).time j.succ)
      (hl : j.succ ≤ Fin.last (H n).eventCount)
      (A : BackwardPointTrace (H n).toHistory j.succ (Fin.last (H n).eventCount) hl (y n))
      (b : ((H n).toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow (p n).modelRadius),
      A.point j.succ le_rfl hl = ((records n j hj).static b).window x ∧ ‖x.val‖ < Dn n + 1 ∧
        t n - (H n).time j.succ ≤ θ * (((records n j hj).static b).neck.scale)⁻¹)
    (z : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).Carrier)
    (hz : ∀ n, z n ∈ riemannianBallOf ((S n).flow.base.metric (t n)) (y n)
      (A / Real.sqrt ((S n).flow.scalar (t n) (y n))))
    (hbad : ∀ n : ℕ, ((n : ℝ) + K + 1) * (S n).flow.scalar (t n) (y n) <
      (S n).flow.scalar (t n) (z n)) : False := by
  have hK1 : 1 ≤ K := hK ▸ le_max_right _ _
  have hn0 (n : ℕ) : (0 : ℝ) ≤ n := n.cast_nonneg
  have hRpos (n : ℕ) : 0 < (S n).flow.scalar (t n) (y n) := by linarith [hΛ n, hn0 n]
  have hqK (n : ℕ) : q n ≤ K * (S n).flow.scalar (t n) (y n) :=
    (hqy n).trans (mul_le_mul_of_nonneg_right (hK ▸ le_max_left _ _) (hRpos n).le)
  let Asl : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).ClosedSlab
      ((H n).time (Fin.last (H n).eventCount)) (t n) := fun n =>
    S n
  have hzmax (n : ℕ) : max (q n) ((S n).flow.scalar (t n) (y n)) ≤
      (S n).flow.scalar (t n) (z n) := by
    refine max_le ?_ ?_
    · nlinarith [hbad n, hqK n, hRpos n, hn0 n]
    · nlinarith [hbad n, hRpos n, hn0 n]
  choose xc Nc pc hxc hxy hpc0 hpcN hchainc hMc hNc using fun n =>
    (Asl n).exists_rebase_chain Cgrad (hq n) (fun y' t' ht' hq' v => hgrad n y' t' ht' hq' v)
      (y n) (z n) (hz n) (hzmax n)
  have hQy (n : ℕ) : (S n).flow.scalar (t n) (y n) ≤ max (q n) ((S n).flow.scalar (t n) (y n)) :=
    le_max_right _ _
  have hQK (n : ℕ) : max (q n) ((S n).flow.scalar (t n) (y n)) ≤
      K * (S n).flow.scalar (t n) (y n) :=
    max_le (hqK n) (le_mul_of_one_le_left (hRpos n).le hK1)
  have hU (n : ℕ) (w : ((H n).stage (Fin.last (H n).eventCount)).Carrier) :
      w ∈ ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen := by
    change w ∈ ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularRegion
    rw [(Asl n).terminalRegularRegion_eq_univ _]
    trivial
  let x : ∀ n, ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen :=
    fun n => ⟨xc n, hU n (xc n)⟩
  have hxQ (n : ℕ) : (Asl n).flow.scalar (t n) (x n).val =
      max (q n) ((S n).flow.scalar (t n) (y n)) := hxc n
  have hQ1 (n : ℕ) : 1 ≤ (Asl n).flow.scalar (t n) (x n).val := by
    rw [hxQ n]
    linarith [hQy n, hΛ n, hn0 n]
  have hlp := localPropagationRadius_pos Cgrad.coe_nonneg
  have hr₀ (n : ℕ) : 0 < localPropagationRadius Cgrad /
      (2 * Real.sqrt (2 * max (q n) ((S n).flow.scalar (t n) (y n)))) := by
    have : 0 < max (q n) ((S n).flow.scalar (t n) (y n)) := (hq n).trans_le (le_max_left _ _)
    positivity
  have hlamc (n : ℕ) : ∑ k ∈ Finset.range (Nc n), (fun _ : ℕ => localPropagationRadius Cgrad /
      (2 * Real.sqrt (2 * max (q n) ((S n).flow.scalar (t n) (y n))))) k ≤
      (2 * A * Real.sqrt K + localPropagationRadius Cgrad) /
        Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hxQ n]
    exact rebase_lam_bound_O3L hA hK1 (hRpos n) (hQy n) (hQK n) hlp rfl (hNc n)
  have htr (n : ℕ) := chain_traces_of_not_capWindowPoint_of_closedSlab_O3L
    (H n) (hend n) (S n) (hS n) (T₀ n) (hT₀ n) (records n) (hcan n) (hscale n) (hacc n) hphi
    (hpinch n) (hpinchS n) (hslabs n) (hder n) le_rfl (hradius n) (y n) (hnot n) (pc n)
    (fun _ => localPropagationRadius Cgrad /
      (2 * Real.sqrt (2 * max (q n) ((S n).flow.scalar (t n) (y n))))) (hpc0 n)
    (fun _ _ => hr₀ n) (hchainc n) (hMc n) (hlamc n)
  have hlam : 0 ≤ 2 * A * Real.sqrt K + localPropagationRadius Cgrad := by positivity
  have hDn' : Tendsto Dn atTop atTop := hDn
  have hQlim : Tendsto (fun n => (Asl n).flow.scalar (t n) (x n).val) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    rw [hxQ n]
    linarith [hQy n, hΛ n, hK1]
  have htime : Tendsto (fun n => (Asl n).flow.scalar (t n) (x n).val * t n) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_)
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    have ht0 : 0 ≤ t n := ((H n).toHistory.time_nonneg _).trans (S n).lt.le
    rw [hxQ n]
    have := mul_le_mul_of_nonneg_right (hQy n) ht0
    linarith [hΛt n, hK1]
  let σ : ℕ → ℝ := fun n => ρ n - A / Real.sqrt ((S n).flow.scalar (t n) (y n))
  have hσlim : Tendsto (fun n => σ n * Real.sqrt ((Asl n).flow.scalar (t n) (x n).val))
      atTop atTop := by
    have hbase : Tendsto (fun n : ℕ => (n : ℝ) + (K + 1 - A)) atTop atTop :=
      tendsto_atTop_add_const_right atTop _ tendsto_natCast_atTop_atTop
    refine tendsto_atTop_mono' atTop ?_ hbase
    filter_upwards [eventually_ge_atTop ⌈A⌉₊] with n hn
    have hsy := Real.sqrt_pos.mpr (hRpos n)
    have hid : σ n * Real.sqrt ((S n).flow.scalar (t n) (y n)) =
        ρ n * Real.sqrt ((S n).flow.scalar (t n) (y n)) - A := by
      change (ρ n - A / Real.sqrt ((S n).flow.scalar (t n) (y n))) *
        Real.sqrt ((S n).flow.scalar (t n) (y n)) = _
      field_simp
    have hAn : A ≤ (n : ℝ) := (Nat.le_ceil A).trans (by exact_mod_cast hn)
    have hρn := hρ n
    have hlow : (n : ℝ) + (K + 1 - A) ≤ σ n * Real.sqrt ((S n).flow.scalar (t n) (y n)) := by
      rw [hid]; linarith
    have hσ0 : 0 ≤ σ n := by
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_neg_of_pos hneg hsy
      linarith
    rw [hxQ n]
    exact hlow.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hQy n)) hσ0)
  have hloc : ∀ n (zz : ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen),
      riemannianEDistOf ((Asl n).endpointTerminalLimitMetric
        ((H n).stage (Fin.last (H n).eventCount))).metric (x n) zz < ENNReal.ofReal (σ n) →
      ∀ b : ℝ, 0 < b → b ≤ σ n →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel
            ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen
            ((Asl n).endpointTerminalLimitMetric ((H n).stage (Fin.last (H n).eventCount))).metric
            (riemannianBallOf ((Asl n).endpointTerminalLimitMetric
              ((H n).stage (Fin.last (H n).eventCount))).metric zz b) := by
    intro n zz hzz b hb hbσ
    have hsy := Real.sqrt_pos.mpr (hRpos n)
    have ha'0 : 0 ≤ A / Real.sqrt ((S n).flow.scalar (t n) (y n)) := div_nonneg hA.le hsy.le
    have hσpos : 0 < σ n := hb.trans_le hbσ
    have hσρ : σ n ≤ ρ n := by
      change ρ n - A / Real.sqrt ((S n).flow.scalar (t n) (y n)) ≤ ρ n; linarith
    rw [(Asl n).riemannianEDistOf_endpointTerminalLimitMetric] at hzz
    have hyz : riemannianEDistOf ((S n).flow.base.metric (t n)) (y n) zz.val <
        ENNReal.ofReal (ρ n) := by
      calc riemannianEDistOf ((S n).flow.base.metric (t n)) (y n) zz.val
          ≤ riemannianEDistOf ((S n).flow.base.metric (t n)) (y n) (xc n) +
              riemannianEDistOf ((S n).flow.base.metric (t n)) (xc n) zz.val :=
            riemannianEDistOf_triangle _ _ _ _
        _ < ENNReal.ofReal (A / Real.sqrt ((S n).flow.scalar (t n) (y n))) +
            ENNReal.ofReal (σ n) := ENNReal.add_lt_add (hxy n) hzz
        _ = ENNReal.ofReal (ρ n) := by
            rw [← ENNReal.ofReal_add ha'0 hσpos.le]
            congr 1
            change A / Real.sqrt ((S n).flow.scalar (t n) (y n)) +
              (ρ n - A / Real.sqrt ((S n).flow.scalar (t n) (y n))) = ρ n
            ring
    have hv := hnc n zz.val hyz b hb (hbσ.trans hσρ)
    have hUc : IsClosed ((((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen :
        TopologicalSpace.Opens ((H n).stage (Fin.last (H n).eventCount)).Carrier) :
          Set ((H n).stage (Fin.last (H n).eventCount)).Carrier) := by
      change IsClosed ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularRegion
      rw [(Asl n).terminalRegularRegion_eq_univ _]
      exact isClosed_univ
    have heq := riemannianVolumeMeasure_ball_restrictOpen_of_isClosed
      ((Asl n).flow.base.metric (t n))
      ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen hUc zz b
    dsimp only at heq
    change _ ≤ riemannianVolumeMeasure ThreeModel
      ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen
      (((Asl n).flow.base.metric (t n)).restrictOpen
        ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen)
      (riemannianBallOf (((Asl n).flow.base.metric (t n)).restrictOpen
        ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen) zz b)
    rw [heq]
    exact hv
  obtain ⟨B, hB⟩ := exists_normalized_scalar_bound_of_chain_traces_local_O3
    H t Asl (fun n => hS n) (fun n => (hend n) ▸ (S n).lt) Ctime Cgrad q hq
    (fun n j y' t' ht' hq' => hslabs n j (Fin.castSucc_lt_last j) y' t' ht' hq')
    (fun n y' t' ht' hq' => hder n y' t' ht' hq')
    (fun n y' t' ht' hq' v => hgrad n y' t' ht' hq' v) x hQ1
    (fun n => by rw [hxQ n]; exact le_max_left _ _) hQlim hphi (fun n => hpinch n)
    (fun n τ hτ w => hpinchS n τ ⟨hτ.1, hτ.2.le⟩ w) σ hκ hσlim hloc
    heps (fun n => hW n) htime (Kc := 6) hlam hθ Dn hDn'
    (fun n N pp δ M τ h0 hδ hch hb hKc h1 hτ0 hτt hC h4 hDD =>
      htr n N pp δ M τ (h0.trans (hpcN n).symm) hδ hch hb
        (by rw [hxQ n] at hKc; exact hKc) (by
          rw [hxQ n] at hKc
          have := le_max_left (q n) ((S n).flow.scalar (t n) (y n))
          linarith) h1 hτ0 hτt hC h4 hDD)
    (2 * A * Real.sqrt K + 1) (by positivity)
  obtain ⟨n, hn, hnB⟩ := (hB.and (eventually_gt_atTop ⌈B * K⌉₊)).exists
  let z' : ((Asl n).restrictIncoming le_rfl (Asl n).lt le_rfl).terminalRegularOpen :=
    ⟨z n, hU n (z n)⟩
  have hsx : 0 < Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le (hQ1 n))
  have hsy : 0 < Real.sqrt ((S n).flow.scalar (t n) (y n)) := Real.sqrt_pos.mpr (hRpos n)
  have hratio : Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) ≤
      Real.sqrt K * Real.sqrt ((S n).flow.scalar (t n) (y n)) := by
    rw [← Real.sqrt_mul (by linarith), hxQ n]
    exact Real.sqrt_le_sqrt (hQK n)
  have hxz : riemannianEDistOf ((S n).flow.base.metric (t n)) (xc n) (z n) <
      ENNReal.ofReal (2 * (A / Real.sqrt ((S n).flow.scalar (t n) (y n)))) := by
    calc riemannianEDistOf ((S n).flow.base.metric (t n)) (xc n) (z n)
        ≤ riemannianEDistOf ((S n).flow.base.metric (t n)) (xc n) (y n) +
          riemannianEDistOf ((S n).flow.base.metric (t n)) (y n) (z n) :=
          riemannianEDistOf_triangle _ _ _ _
      _ < ENNReal.ofReal (A / Real.sqrt ((S n).flow.scalar (t n) (y n))) +
          ENNReal.ofReal (A / Real.sqrt ((S n).flow.scalar (t n) (y n))) := by
          rw [riemannianEDistOf_comm]
          exact ENNReal.add_lt_add (hxy n) (hz n)
      _ = ENNReal.ofReal (2 * (A / Real.sqrt ((S n).flow.scalar (t n) (y n)))) := by
          rw [← ENNReal.ofReal_add (div_nonneg hA.le (Real.sqrt_nonneg _))
            (div_nonneg hA.le (Real.sqrt_nonneg _))]
          ring_nf
  have hdist : riemannianEDistOf (scaleMetric ((Asl n).flow.scalar (t n) (x n).val)
      (zero_lt_one.trans_le (hQ1 n))
      ((Asl n).endpointTerminalLimitMetric _).metric) (x n) z' <
        ENNReal.ofReal (2 * A * Real.sqrt K + 1) := by
    rw [(Asl n).scaled_endpoint_edist_eq]
    calc ENNReal.ofReal (Real.sqrt ((Asl n).flow.scalar (t n) (x n).val)) *
          riemannianEDistOf ((Asl n).flow.base.metric (t n)) (x n).val z'.val <
        ENNReal.ofReal (Real.sqrt ((Asl n).flow.scalar (t n) (x n).val)) *
          ENNReal.ofReal (2 * (A / Real.sqrt ((S n).flow.scalar (t n) (y n)))) :=
          ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hsx).ne' ENNReal.ofReal_ne_top hxz
      _ = ENNReal.ofReal (Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) *
          (2 * (A / Real.sqrt ((S n).flow.scalar (t n) (y n))))) :=
          (ENNReal.ofReal_mul hsx.le).symm
      _ ≤ ENNReal.ofReal (2 * A * Real.sqrt K) := by
          apply ENNReal.ofReal_le_ofReal
          rw [show Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) *
            (2 * (A / Real.sqrt ((S n).flow.scalar (t n) (y n)))) =
            2 * A * (Real.sqrt ((Asl n).flow.scalar (t n) (x n).val) /
              Real.sqrt ((S n).flow.scalar (t n) (y n))) by ring]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_iff₀ hsy]
          exact hratio
      _ < ENNReal.ofReal (2 * A * Real.sqrt K + 1) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  have hle := hn z' hdist
  have hscal : metricScalarAt ((Asl n).endpointTerminalLimitMetric _).metric z' =
      (S n).flow.scalar (t n) (z n) := metricScalarAt_restrictOpen _ _ _
  rw [hscal, div_le_iff₀ (zero_lt_one.trans_le (hQ1 n)), hxQ n] at hle
  have hceil : B * K ≤ (n : ℝ) := (Nat.le_ceil (B * K)).trans (by exact_mod_cast hnB.le)
  have hbig := hbad n
  have hQKn := hQK n
  have hRyn := hRpos n
  have hn1 := hn0 n
  rcases le_or_gt 0 B with hB0 | hB0
  · have h1 : B * max (q n) ((S n).flow.scalar (t n) (y n)) ≤
        B * (K * (S n).flow.scalar (t n) (y n)) := mul_le_mul_of_nonneg_left hQKn hB0
    have h2 : B * K * (S n).flow.scalar (t n) (y n) ≤ n * (S n).flow.scalar (t n) (y n) :=
      mul_le_mul_of_nonneg_right hceil hRyn.le
    nlinarith
  · have h1 : B * max (q n) ((S n).flow.scalar (t n) (y n)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hB0.le (by linarith [hQy n])
    nlinarith

theorem exists_scalar_bound_at_distance_of_not_capWindowPoint_closed_late_O3L
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) (A : ℝ) (hA : 0 < A)
    (Cq θ : ℝ) (hθ : 0 < θ) :
    ∃ Q Λ Dcap Rrad ζ₀ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧ StandardCap.transitionEnd < Dcap ∧ Dcap ≤ Rrad ∧
    0 < ζ₀ ∧
    ∀ (H : RetainedCoreHistory.{u})
      (hend : H.time (Fin.last H.eventCount) = H.horizon) {t : ℝ}
      (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) t)
      (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount))
      (T₀ : ℝ) {p : CutoffParameters}
      (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ → GeometricCutoffRecord H.toHistory i p),
      (∀ i hi b, ((records i hi).static b).hasCanonicalWindow) →
      Rrad ≤ p.modelRadius → 2 ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
      T₀ + θ ≤ t →
      ∀ (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
      0 < q → q ≤ Cq * S.flow.scalar t y → Λ ≤ S.flow.scalar t y →
      Λ ≤ S.flow.scalar t y * t →
      (∀ x, q < S.flow.scalar t x →
        ∃ W : SpatialCanonicalWitness (S.flow.base.metric t) ε C1 C2 x,
          W.capTubeHasNeckChart ε) →
      H.EventSlabsDerivative Ctime q (Fin.last H.eventCount) →
      (S.restrictIncoming le_rfl S.lt le_rfl).DerivativeBoundBefore Ctime q t →
      (S.restrictIncoming le_rfl S.lt le_rfl).GradientBoundBefore Cgrad q t →
      H.EventSlabsPinched phi →
      Perelman.PhiAlmostNonnegative S.flow (Icc (H.time (Fin.last H.eventCount)) t) phi →
      (∀ (w : ((H).stage (Fin.last (H).eventCount)).Carrier),
        riemannianEDistOf ((S).flow.base.metric (t)) (y) w < ENNReal.ofReal (ρ) →
        ∀ b : ℝ, 0 < b → b ≤ ρ →
          ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
            riemannianVolumeMeasure ThreeModel ((H).stage (Fin.last (H).eventCount)).Carrier
              ((S).flow.base.metric (t)) (riemannianBallOf ((S).flow.base.metric (t)) w b)) →
      Λ ≤ ρ * Real.sqrt (S.flow.scalar t y) →
      (¬ ∃ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ Fin.last H.eventCount)
        (A : BackwardPointTrace H.toHistory j.succ (Fin.last H.eventCount) hl y)
        (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
        A.point j.succ le_rfl hl = ((records j hj).static b).window x ∧ ‖x.val‖ < Dcap + 1 ∧
          t - H.time j.succ ≤ θ * (((records j hj).static b).neck.scale)⁻¹) →
      ∀ z ∈ riemannianBallOf (S.flow.base.metric t) y (A / Real.sqrt (S.flow.scalar t y)),
        S.flow.scalar t z ≤ Q * S.flow.scalar t y := by
  have heps : 13000 * (13000 * ε) ≤
      min (neckModelTolerance (1 / 4000000 / 26000)) (1 / 4000000 / 26000 / 64) := by
    unfold coneAccuracy at hεle
    have h := (le_div_iff₀ (by norm_num : (0 : ℝ) < 13000 * 13000)).mp hεle
    linarith
  have hTE := StandardCap.transitionEnd_pos
  have hn0 (n : ℕ) : (0 : ℝ) ≤ n := n.cast_nonneg
  have hDn (n : ℕ) : StandardCap.transitionEnd < StandardCap.transitionEnd + 1 + n := by
    linarith [hn0 n]
  have hK1 : (1 : ℝ) ≤ max Cq 1 := le_max_right _ _
  choose ε₀ hε₀ hsc using fun n : ℕ =>
    exists_presented_cap_scalar_lower_bound_of_canonical_window_core.{u}
      (StandardCap.transitionEnd + 1 + n) (hDn n)
  by_contra hcon
  push Not at hcon
  choose H hend t S hS T₀ p records hcan hRrad hord hζ hT₀ y q ρ hq hqy hΛ hΛt hW
    hslabs hder hgrad hpinch hpinchS hnc hρ hnot z hz hbad using fun n : ℕ =>
    hcon ((n : ℝ) + max Cq 1 + 1) ((n : ℝ) + max Cq 1 + 1) (StandardCap.transitionEnd + 1 + n)
      (StandardCap.transitionEnd + 1 + n) (min (1 / 2) (ε₀ n)) (by linarith [hn0 n])
      (by linarith [hn0 n]) (hDn n) le_rfl (lt_min (by norm_num) (hε₀ n))
  have hradius (n : ℕ) : StandardCap.transitionEnd + 1 + n ≤ (p n).modelRadius := hRrad n
  have hacc (n : ℕ) : (p n).modelAccuracy ≤ 1 / 2 := (hζ n).trans (min_le_left _ _)
  have hscale (n : ℕ) (i : Fin (H n).eventCount) (hi : T₀ n ≤ (H n).time i.succ)
      (b : ((H n).toHistory.event i).RetainedBoundaryIndex) (w : ThreeBall) :
      ((records n i hi).static b).neck.scale / 2 ≤
      metricScalarAt ((records n i hi).static b).witness.metric
        (((records n i hi).static b).witness.cap w) :=
    hsc n ((H n).toHistory.event i) (hradius n) ((hζ n).trans (min_le_right _ _))
      (hord n) ((records n i hi).static b) (hcan n i hi b) w
  refine false_of_closed_counterexamples_late_O3L heps hκ hphi hA hθ rfl
    (fun n => StandardCap.transitionEnd + 1 + n) ?_ H hend t S hS T₀ records hcan hscale hacc
    hradius hT₀ y q ρ hq hqy hΛ hΛt hW hslabs hder hgrad hpinch hpinchS hnc hρ
    (fun n ⟨j, hj, hl, A, b, x, h1, h2, h3⟩ => absurd h3 (not_le.mpr (hnot n j hj hl A b x h1 h2)))
    z hz hbad
  exact tendsto_atTop_add_const_left atTop _ tendsto_natCast_atTop_atTop


end GC.LongTime.Ch12
