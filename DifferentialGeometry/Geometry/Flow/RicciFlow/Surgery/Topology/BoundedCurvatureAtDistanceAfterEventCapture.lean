import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalNeighborhoodContinuationLeaves
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFirstLoss
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessClosedBallJets

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace Manifold Bundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem OrientedThreeStage.exists_first_touch_of_not_subset (P : OrientedThreeStage.{u})
    (g : P.Metric) (U : Opens P.Carrier) {y : P.Carrier} (hy : y ∈ U) {r : ℝ}
    (hnot : ¬ riemannianBallOf g y r ⊆ U) :
    ∃ q : P.Carrier, q ∉ U ∧ ∃ d : ℝ, 0 < d ∧ d < r ∧
      riemannianEDistOf g y q = ENNReal.ofReal d ∧ riemannianBallOf g y d ⊆ U ∧
      q ∈ closure (riemannianBallOf g y d) := by
  have hcomplete : RiemannianMetricComplete g := by
    refine ⟨?_⟩
    infer_instance
  obtain ⟨z, hz, hzU⟩ := not_subset.mp hnot
  have hK : IsCompact ((U : Set P.Carrier)ᶜ) := U.isOpen.isClosed_compl.isCompact
  have hcont : Continuous fun q => riemannianEDistOf g y q :=
    Geometry.Riemannian.continuous_riemannianEDist g y
  obtain ⟨q, hqK, hmin⟩ := hK.exists_isMinOn ⟨z, hzU⟩ hcont.continuousOn
  have hqz : riemannianEDistOf g y q < ENNReal.ofReal r := (hmin hzU).trans_lt hz
  let _ : TopologicalSpace.MetrizableSpace P.Carrier :=
    Manifold.metrizableSpace ThreeModel P.Carrier
  let _ : RegularSpace P.Carrier := inferInstance
  let _ : RiemannianBundle (fun x : P.Carrier => TangentSpace ThreeModel x) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace
      (fun x : P.Carrier => TangentSpace ThreeModel x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  obtain ⟨c, hc, hball⟩ := setOfPred_riemannianEDist_lt_subset_nhds ThreeModel
    (U.isOpen.mem_nhds hy)
  have hcq : (c : ℝ≥0∞) ≤ riemannianEDistOf g y q := by
    by_contra hlt
    exact hqK (hball (not_le.mp hlt))
  have hne : riemannianEDistOf g y q ≠ ⊤ := ne_top_of_lt hqz
  set d := (riemannianEDistOf g y q).toReal with hd
  have hdeq : riemannianEDistOf g y q = ENNReal.ofReal d := (ENNReal.ofReal_toReal hne).symm
  have hdpos : 0 < d := by
    have h0 : (0 : ℝ≥0∞) < riemannianEDistOf g y q :=
      lt_of_lt_of_le (by exact_mod_cast hc) hcq
    exact ENNReal.toReal_pos h0.ne' hne
  have hdr : d < r := by
    rw [hdeq] at hqz
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hdpos.le).mp hqz
  have hsub : riemannianBallOf g y d ⊆ U := by
    intro w hw
    by_contra hwU
    have h1 : riemannianEDistOf g y q ≤ riemannianEDistOf g y w := hmin hwU
    have h2 : riemannianEDistOf g y w < ENNReal.ofReal d := hw
    rw [hdeq] at h1
    exact (not_lt_of_ge h1) h2
  refine ⟨q, hqK, d, hdpos, hdr, hdeq, hsub, ?_⟩
  rw [closure_riemannianBallOf g hcomplete y hdpos]
  change riemannianEDistOf g y q ≤ ENNReal.ofReal d
  exact hdeq.le

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

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

theorem not_regularCrossing_of_not_mem_backwardSurvivorDomain (j : Fin H.eventCount)
    {q : (H.stage j.succ).Carrier}
    (hq : q ∉ H.toHistory.backwardSurvivorDomain j.castSucc j.succ j.castSucc_lt_succ.le) :
    ∀ p' : (H.stage j.castSucc).Carrier, ¬ (H.toHistory.event j).RegularCrossing p' q :=
  fun p' hp' => hq ⟨(BackwardPointTrace.singleton H.toHistory j.castSucc p').append q hp'⟩

theorem capWindowPoint_at_event_of_not_regularCrossing {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow) (j : Fin H.eventCount)
    {y : (H.stage j.succ).Carrier}
    (hy : ∀ p' : (H.stage j.castSucc).Carrier, ¬ (H.toHistory.event j).RegularCrossing p' y)
    {Dcap θ : ℝ} (hD : StandardCap.transitionEnd < Dcap + 1) (hθ : 0 ≤ θ) :
    H.CapWindowPoint records j.succ y (H.time j.succ) Dcap θ := by
  obtain ⟨b, zc, hzc⟩ := (records j).exists_cap_of_not_regularCrossing_target hy
  obtain ⟨-, -, -, -, -, -, -, hcap⟩ := hcan j b
  obtain ⟨x, hxn, hx⟩ := hcap zc
  refine ⟨j, le_rfl, BackwardPointTrace.singleton H.toHistory j.succ y, b, x,
    (BackwardPointTrace.singleton H.toHistory j.succ y).endpoint_eq.trans (hzc.trans hx.symm),
    hxn.trans_lt hD, ?_⟩
  rw [sub_self]
  exact mul_nonneg hθ (inv_nonneg.mpr ((records j).static b).neck.scale_pos.le)

theorem capWindowPoint_at_event_of_edist_le {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (hcan : ∀ i b, ((records i).static b).hasCanonicalWindow)
    (hscale : ∀ i b z, ((records i).static b).neck.scale / 2 ≤
      metricScalarAt ((records i).static b).witness.metric (((records i).static b).witness.cap z))
    (hacc : p.modelAccuracy ≤ 1 / 2) (j : Fin H.eventCount)
    {y q : (H.stage j.succ).Carrier}
    (hq : ∀ p' : (H.stage j.castSucc).Carrier, ¬ (H.toHistory.event j).RegularCrossing p' q)
    {M dd Dcap θ : ℝ} (hM : metricScalarAt (H.initialMetric j.succ) q ≤ M)
    (hnear : riemannianEDistOf (H.initialMetric j.succ) q y ≤ ENNReal.ofReal dd)
    (hdd : 0 ≤ dd) (hwin : 2 * StandardCap.transitionEnd + Real.sqrt (8 * M) * dd < Dcap)
    (hDmodel : Dcap ≤ p.modelRadius) (hθ : 0 ≤ θ) :
    H.CapWindowPoint records j.succ y (H.time j.succ) Dcap θ := by
  obtain ⟨b, zc, hzc⟩ := (records j).exists_cap_of_not_regularCrossing_target hq
  obtain ⟨-, -, -, -, -, -, -, hcap⟩ := hcan j b
  obtain ⟨xz, hxzn, hxz⟩ := hcap zc
  have hspos : 0 < ((records j).static b).neck.scale := ((records j).static b).neck.scale_pos
  have hsM : ((records j).static b).neck.scale ≤ 4 * M := by
    have h2 : metricScalarAt ((records j).static b).witness.metric
        (((records j).static b).witness.cap zc) ≤ M := by
      rw [((records j).static b).scalar_eq, ← hzc, H.toHistory.event_output j]
      exact hM
    linarith [hscale j b zc]
  obtain ⟨x, hxn, hxeq⟩ := H.exists_window_point_of_edist_le records hcan hacc j b hsM le_rfl
    hDmodel xz hxzn y (by rw [hxz, ← hzc]; exact hnear) hdd hwin
  refine ⟨j, le_rfl, BackwardPointTrace.singleton H.toHistory j.succ y, b, x,
    (BackwardPointTrace.singleton H.toHistory j.succ y).endpoint_eq.trans hxeq.symm,
    by linarith, ?_⟩
  rw [sub_self]
  exact mul_nonneg hθ (inv_nonneg.mpr hspos.le)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
