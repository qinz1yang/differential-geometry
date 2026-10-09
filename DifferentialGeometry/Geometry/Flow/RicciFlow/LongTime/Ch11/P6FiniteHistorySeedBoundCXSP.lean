import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedArithmeticCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SeedScaleP6A
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingModelCoverage
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IdentifiedHistoryPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceConstants
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefixTransport

/-!
# CX-SPINE: fixed finite history, small-seed scalar bound

Every incoming slab is split at its midpoint. Compactness pays its first half,
and the actual incoming model theorem pays full canonical derivatives on its
second half. The final stage is a closed slab or a single birth metric.
No time-derivative, pinching, compact scalar bound, or extra noncollapse supply
is assumed: these are produced from the fixed actual history and its records.
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal

namespace GC.LongTime.Ch11

universe u

private theorem finite_seed_radius_budget_CXSP
    {L q d rho : ℝ} (hL : 1 ≤ L) (hq : 1 ≤ q) (hd : 0 < d) (hrho : 0 < rho) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 →
      L * q < 4 * (r ^ 2)⁻¹ ∧
      L / (4 * (r ^ 2)⁻¹) ≤ d ∧
      L ≤ rho * Real.sqrt (4 * (r ^ 2)⁻¹) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hqp : 0 < q := zero_lt_one.trans_le hq
  let r0 := min 1 (min (1 / (L * q + 1))
    (min (d / (L + 1)) (rho / (L + 1))))
  have hr0 : 0 < r0 := by dsimp [r0]; positivity
  have hr01 : r0 ≤ 1 := min_le_left _ _
  refine ⟨r0, hr0, hr01, ?_⟩
  intro r hr hrr0
  have hr1 : r ≤ 1 := hrr0.trans hr01
  have hrq : r ≤ 1 / (L * q + 1) :=
    hrr0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrd : r ≤ d / (L + 1) :=
    hrr0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hrrho : r ≤ rho / (L + 1) :=
    hrr0.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hr2r : r ^ 2 ≤ r := by nlinarith
  have hqr : r * (L * q + 1) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < L * q + 1)).mp hrq
  have hdr : r * (L + 1) ≤ d :=
    (le_div_iff₀ (by positivity : 0 < L + 1)).mp hrd
  have hrhor : r * (L + 1) ≤ rho :=
    (le_div_iff₀ (by positivity : 0 < L + 1)).mp hrrho
  have hqmul : L * q * r ^ 2 ≤ L * q * r :=
    mul_le_mul_of_nonneg_left hr2r (mul_pos hLp hqp).le
  have hdmul : L * r ^ 2 ≤ L * r :=
    mul_le_mul_of_nonneg_left hr2r hLp.le
  refine ⟨?_, ?_, ?_⟩
  · rw [← div_eq_mul_inv]
    apply (lt_div_iff₀ hr2).mpr
    nlinarith
  · have heq : L / (4 * (r ^ 2)⁻¹) = L * r ^ 2 / 4 := by
      field_simp [hr.ne']
    rw [heq]
    nlinarith
  · rw [sqrt_seed_scale_CXSP (by norm_num : (0 : ℝ) < 4) hr]
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by norm_num
    rw [hs4, ← mul_div_assoc]
    apply (le_div_iff₀ hr).mpr
    nlinarith

private theorem scalar_seed_bound_of_compact_bound_CXSP
    {R M K r : ℝ} (hM : 0 ≤ M) (hRM : R ≤ M) (hMK : M ≤ K)
    (hr : 0 < r) (hr1 : r ≤ 1) : R ≤ K * (r ^ 2)⁻¹ := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hr21 : r ^ 2 ≤ 1 := by nlinarith
  have hprod : R * r ^ 2 ≤ K := calc
    R * r ^ 2 ≤ M * r ^ 2 := mul_le_mul_of_nonneg_right hRM hr2.le
    _ ≤ M := by nlinarith
    _ ≤ K := hMK
  simpa only [div_eq_mul_inv] using (le_div_iff₀ hr2).mpr hprod

private theorem incoming_early_scalar_bound_CXSP
    {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc a ((a + s) / 2),
      ∀ x : P.Carrier, G.flow.scalar t x ≤ M := by
  have hb : (a + s) / 2 < s := by linarith [G.lt]
  have hK : IsCompact (Icc a ((a + s) / 2) ×ˢ (univ : Set P.Carrier)) :=
    isCompact_Icc.prod isCompact_univ
  have hsub : Icc a ((a + s) / 2) ×ˢ (univ : Set P.Carrier) ⊆
      (RealTimeInterval.closedOpen a s G.lt).carrier ×ˢ univ :=
    prod_mono (fun _ hz => ⟨hz.1, hz.2.trans_lt hb⟩) subset_rfl
  obtain ⟨B, hB⟩ := hK.bddAbove_image (G.equation.scalarCont.mono hsub)
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro t ht x
  exact (hB ⟨(t, x), ⟨ht, mem_univ x⟩, rfl⟩).trans (le_max_right _ _)

private theorem final_stage_scalar_bound_CXSP (V : RetainedCoreHistory.{u}) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ t ∈ Icc (V.time (Fin.last V.eventCount)) V.horizon,
      ∀ x : (V.stage (Fin.last V.eventCount)).Carrier,
        metricScalarAt (V.toHistory.stageMetric (Fin.last V.eventCount) t) x ≤ M := by
  by_cases hfinal : V.time (Fin.last V.eventCount) < V.horizon
  · let G := V.finalSlab hfinal
    have hK : IsCompact
        (Icc (V.time (Fin.last V.eventCount)) V.horizon ×ˢ
          (univ : Set (V.stage (Fin.last V.eventCount)).Carrier)) :=
      isCompact_Icc.prod isCompact_univ
    obtain ⟨B, hB⟩ := hK.bddAbove_image G.equation.scalarCont
    refine ⟨max 0 B, le_max_left _ _, ?_⟩
    intro t ht x
    rw [ObservedHistory.stageMetric_last_of_lt (H := V.toHistory) (h := hfinal)]
    exact (hB ⟨(t, x), ⟨ht, mem_univ x⟩, rfl⟩).trans (le_max_right _ _)
  · have hcont : Continuous (metricScalarAt (V.initialMetric (Fin.last V.eventCount))) :=
      (metricScalar_smooth _).continuous
    obtain ⟨B, hB⟩ := isCompact_univ.bddAbove_image hcont.continuousOn
    refine ⟨max 0 B, le_max_left _ _, ?_⟩
    intro t _ht x
    rw [ObservedHistory.stageMetric_last_of_le (H := V.toHistory) (le_of_not_gt hfinal)]
    exact (hB ⟨x, mem_univ x, rfl⟩).trans (le_max_right _ _)

/-- The actual finite history supplies a uniform scalar bound from a low base
point. Surgery births and a zero-age final stage are included. -/
theorem exists_finite_history_low_base_scalar_bound_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (V : RetainedCoreHistory.{u}) (IV : InitialIdentification P g V.toHistory)
    (pCut : CutoffParameters)
    (records : ∀ j : Fin V.eventCount, GeometricCutoffRecord V.toHistory j pCut)
    (kappa rho : ℝ) (hkappa : 0 < kappa) (hrho : 0 < rho)
    (hnc : V.NoncollapsedBefore kappa rho V.horizon)
    (A : ℝ) (hA : 0 < A) :
    ∃ r0 K : ℝ, 0 < r0 ∧ 0 < K ∧
      ∀ (t : Icc (0 : ℝ) V.horizon) (p : (V.toHistory.stageAt t).Carrier) (r : ℝ),
        0 < r → r ≤ r0 →
        metricScalarAt (V.toHistory.stageMetric (V.toHistory.activeStage t) t) p ≤
          3 * (r ^ 2)⁻¹ →
        ∀ x ∈ riemannianBallOf
          (V.toHistory.stageMetric (V.toHistory.activeStage t) t) p (A * r),
          metricScalarAt (V.toHistory.stageMetric (V.toHistory.activeStage t) t) x ≤
            K * (r ^ 2)⁻¹ := by
  classical
  let eps : ℝ := min coneAccuracy (1 / 44)
  have heps : 0 < eps := lt_min coneAccuracy_pos (by norm_num)
  have hepsSmall : eps < 1 / 11 :=
    (min_le_right _ _).trans_lt (by norm_num)
  have hepsCone : eps ≤ coneAccuracy := min_le_left _ _
  obtain ⟨C, hC, hmodels⟩ :=
    OrientedThreeStage.IncomingSlab.exists_uniform_canonical_constants_with_cap_neck_charts.{u}
      heps hepsSmall
  have hCp : 0 < C := zero_lt_one.trans_le hC
  let Cn : ℝ≥0 := ⟨C, hCp.le⟩
  choose qj hqj hcanj using fun j : Fin V.eventCount =>
    hmodels (V.stage j.castSucc) (V.time j.castSucc) (V.time j.succ)
      (V.toHistory.event j).incoming
  let q : ℝ := 1 + ∑ j : Fin V.eventCount, qj j
  have hsumq : 0 ≤ ∑ j : Fin V.eventCount, qj j :=
    Finset.sum_nonneg fun j _ => (hqj j).le
  have hq : 1 ≤ q := by dsimp [q]; linarith
  have hqjle (j : Fin V.eventCount) : qj j ≤ q := by
    have hsingle := Finset.single_le_sum (fun k _ => (hqj k).le) (Finset.mem_univ j)
    dsimp [q]
    linarith
  have hcan (j : Fin V.eventCount) (x : (V.stage j.castSucc).Carrier) (t : ℝ)
      (ht : t ∈ Ico (V.time j.castSucc) (V.time j.succ))
      (hR : q < (V.toHistory.event j).incoming.flow.scalar t x) :
      ∃ W : CanonicalWitness (V.toHistory.event j).incoming.flow eps C C x t,
        W.capTubeHasNeckChart eps :=
    hcanj j x t ht ((hqjle j).trans hR.le)
  have hder (j : Fin V.eventCount) :
      (V.toHistory.event j).incoming.DerivativeBoundBefore Cn q (V.time j.succ) := by
    intro x t ht hR
    obtain ⟨W, _hchart⟩ := hcan j x t ⟨ht.1.le, ht.2⟩ hR
    exact W.time_derivative
  have hgrad (j : Fin V.eventCount) :
      (V.toHistory.event j).incoming.GradientBoundBefore Cn q (V.time j.succ) := by
    intro x t ht hR v
    obtain ⟨W, _hchart⟩ := hcan j x t ⟨ht.1.le, ht.2⟩ hR
    exact W.gradient v
  obtain ⟨phi, hphi, hpinSource⟩ := exists_pinching_certificates_for_identified_histories P g
  have hpin : V.EventSlabsPinched phi := (hpinSource V IV pCut records).1
  obtain ⟨B, L, hB, hL, hbcad⟩ :=
    RetainedCoreHistory.exists_scalar_bound_at_distance_of_final_slab_window_of_le_coneAccuracy
      hepsCone kappa C C hkappa Cn Cn hphi (4 * A) (by positivity)
  let dj : Fin V.eventCount → ℝ := fun j => (V.time j.succ - V.time j.castSucc) / 2
  have hdj (j : Fin V.eventCount) : 0 < dj j := by
    dsimp [dj]
    exact div_pos (sub_pos.mpr (V.time_strictMono j.castSucc_lt_succ)) (by norm_num)
  let den : ℝ := 1 + ∑ j : Fin V.eventCount, (dj j)⁻¹
  have hsumd : 0 ≤ ∑ j : Fin V.eventCount, (dj j)⁻¹ :=
    Finset.sum_nonneg fun j _ => (inv_pos.mpr (hdj j)).le
  have hden : 0 < den := by dsimp [den]; linarith
  let d : ℝ := den⁻¹
  have hd : 0 < d := inv_pos.mpr hden
  have hdle (j : Fin V.eventCount) : d ≤ dj j := by
    have hsingle := Finset.single_le_sum
      (fun k _ => (inv_pos.mpr (hdj k)).le) (Finset.mem_univ j)
    have hm := mul_le_mul_of_nonneg_left hsingle (hdj j).le
    rw [mul_inv_cancel₀ (hdj j).ne'] at hm
    change den⁻¹ ≤ dj j
    rw [← one_div]
    apply (div_le_iff₀ hden).mpr
    dsimp [den]
    nlinarith [hdj j]
  obtain ⟨r0, hr0, hr01, hbudget⟩ := finite_seed_radius_budget_CXSP hL hq hd hrho
  choose Mj hMj hEarly using fun j : Fin V.eventCount =>
    incoming_early_scalar_bound_CXSP (V.toHistory.event j).incoming
  obtain ⟨Mf, hMf, hFinal⟩ := final_stage_scalar_bound_CXSP V
  have hsumM : 0 ≤ ∑ j : Fin V.eventCount, Mj j :=
    Finset.sum_nonneg fun j _ => hMj j
  let K : ℝ := 1 + Mf + (∑ j : Fin V.eventCount, Mj j) + 4 + 4 * B
  have hK : 0 < K := by dsimp [K]; nlinarith
  have hMfK : Mf ≤ K := by dsimp [K]; nlinarith
  have hMjK (j : Fin V.eventCount) : Mj j ≤ K := by
    have hsingle := Finset.single_le_sum (fun k _ => hMj k) (Finset.mem_univ j)
    dsimp [K]
    nlinarith
  have h4K : 4 ≤ K := by dsimp [K]; nlinarith
  have h4BK : 4 * B ≤ K := by dsimp [K]; linarith
  have hstage : ∀ (k : Fin (V.eventCount + 1)) (t : ℝ),
      t ∈ V.toHistory.stageDomain k →
      ∀ (p x : (V.stage k).Carrier) (r : ℝ), 0 < r → r ≤ r0 →
        metricScalarAt (V.toHistory.stageMetric k t) p ≤ 3 * (r ^ 2)⁻¹ →
        x ∈ riemannianBallOf (V.toHistory.stageMetric k t) p (A * r) →
        metricScalarAt (V.toHistory.stageMetric k t) x ≤ K * (r ^ 2)⁻¹ := by
    intro k
    cases k using Fin.lastCases with
    | last =>
      intro t ht _p x r hr hrr _hseed _hx
      have ht' : t ∈ Icc (V.time (Fin.last V.eventCount)) V.horizon := by
        simpa only [ObservedHistory.stageDomain, Fin.lastCases_last] using ht
      exact scalar_seed_bound_of_compact_bound_CXSP hMf (hFinal t ht' x) hMfK
        hr (hrr.trans hr01)
    | cast j =>
      intro t ht p x r hr hrr hseed hx
      have ht' : t ∈ Ico (V.time j.castSucc) (V.time j.succ) := by
        simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using ht
      rw [ObservedHistory.stageMetric_castSucc_apply] at hseed hx ⊢
      let G := (V.toHistory.event j).incoming
      change G.flow.scalar t p ≤ 3 * (r ^ 2)⁻¹ at hseed
      change x ∈ riemannianBallOf (G.flow.base.metric t) p (A * r) at hx
      change G.flow.scalar t x ≤ K * (r ^ 2)⁻¹
      by_cases hearly : t ≤ (V.time j.castSucc + V.time j.succ) / 2
      · exact scalar_seed_bound_of_compact_bound_CXSP (hMj j)
          (hEarly j t ⟨ht'.1, hearly⟩ x) (hMjK j) hr (hrr.trans hr01)
      have hlate : (V.time j.castSucc + V.time j.succ) / 2 < t :=
        lt_of_not_ge hearly
      have hage : V.time j.castSucc < t := by
        have hbirth := V.time_strictMono j.castSucc_lt_succ
        linarith
      have hdtime : d ≤ t - V.time j.castSucc := by
        have h := hdle j
        dsimp [dj] at h
        linarith
      obtain ⟨hscale, hdepth, hrscale⟩ := hbudget r hr hrr
      let H := V.prefixAt j.castSucc
      let Sl : (H.stage (Fin.last H.eventCount)).ClosedSlab
          (H.time (Fin.last H.eventCount)) t := G.closedPrefix t hage ht'.2
      have hinit : Sl.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount) := V.event_initial j
      have hncG := V.terminalNoncollapsedBefore_prefixAt j hnc
      have hncSl : H.TerminalNoncollapsedBefore rfl
          (Sl.restrictIncoming le_rfl Sl.lt le_rfl) hinit kappa rho t := by
        intro T hT hTt _hTle
        exact H.noncollapsedBefore_closedPrefix_of_terminalNoncollapsedBefore rfl G
          (V.event_initial j) hncG hage ht'.2
          (ht'.2.le.trans (V.toHistory.time_le_horizon_at j.succ)) T hT hTt
      have hprefixDer : H.EventSlabsDerivative Cn q (Fin.last H.eventCount) :=
        V.eventSlabsDerivative_prefixAt j.castSucc (fun i _ => hder i)
      have hprefixPinch : H.EventSlabsPinched phi :=
        V.eventSlabsPinched_prefixAt j.castSucc hpin
      have hSlDer :
          (Sl.restrictIncoming le_rfl Sl.lt le_rfl).DerivativeBoundBefore Cn q t := by
        intro y v hv hRv
        exact hder j y v ⟨hv.1, hv.2.trans ht'.2⟩ hRv
      have hSlGrad :
          (Sl.restrictIncoming le_rfl Sl.lt le_rfl).GradientBoundBefore Cn q t := by
        intro y v hv hRv w
        exact hgrad j y v ⟨hv.1, hv.2.trans ht'.2⟩ hRv w
      have hSlPinch : Perelman.PhiAlmostNonnegative
          (Sl.restrictIncoming le_rfl Sl.lt le_rfl).flow
          (Ico (H.time (Fin.last H.eventCount)) t) phi := by
        intro v hv y
        exact hpin j v ⟨hv.1, hv.2.trans ht'.2⟩ y
      have hSlW : ∀ y, q < Sl.flow.scalar t y →
          ∃ W : SpatialCanonicalWitness (Sl.flow.base.metric t) eps C C y,
            W.capTubeHasNeckChart eps := by
        intro y hRy
        obtain ⟨W, hchart⟩ := hcan j y t ht' hRy
        exact ⟨W.toSpatial, W.capTubeHasNeckChart_toSpatial hchart⟩
      have hr2 : 0 < (r ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hr)
      have hseed4 : metricScalarAt (G.flow.base.metric t) p ≤ 4 * (r ^ 2)⁻¹ := by
        change G.flow.scalar t p ≤ 4 * (r ^ 2)⁻¹
        linarith
      have hbound := scalar_le_of_threshold_points_P6A (G.flow.base.metric t) p
        (q := 4 * (r ^ 2)⁻¹) (K := B) (mul_pos hA hr) hseed4
        (fun y _hy hyQ z hz => by
          have hyQ' : Sl.flow.scalar t y = 4 * (r ^ 2)⁻¹ := hyQ
          have hwindow : H.time (Fin.last H.eventCount) ≤
              t - L / Sl.flow.scalar t y := by
            rw [hyQ']
            change V.time j.castSucc ≤ t - L / (4 * (r ^ 2)⁻¹)
            linarith
          have hrad : (4 * A) / Real.sqrt (Sl.flow.scalar t y) = 2 * (A * r) := by
            rw [hyQ']
            simpa only [show Real.sqrt (4 : ℝ) = 2 by norm_num,
              show (2 : ℝ) * A * 2 = 4 * A by ring] using
              seed_distance_normalization_CXSP A (by norm_num : (0 : ℝ) < 4) hr
          have hthreshold : L * q < Sl.flow.scalar t y := hscale.trans_eq hyQ'.symm
          have htest : L ≤ rho * Real.sqrt (Sl.flow.scalar t y) :=
            hrscale.trans_eq (congrArg (fun z => rho * Real.sqrt z) hyQ').symm
          have hzSl : z ∈ riemannianBallOf (Sl.flow.base.metric t) y
              ((4 * A) / Real.sqrt (Sl.flow.scalar t y)) := by
            rw [hrad]
            exact hz
          have hh := hbcad H rfl Sl hinit y q rho hq hthreshold hwindow hSlW
            hprefixDer hSlDer hSlGrad hprefixPinch hSlPinch hncSl htest z hzSl
          change Sl.flow.scalar t z ≤ B * (4 * (r ^ 2)⁻¹)
          exact hh.trans_eq (congrArg (fun z => B * z) hyQ')) x hx
      change G.flow.scalar t x ≤ max (4 * (r ^ 2)⁻¹) (B * (4 * (r ^ 2)⁻¹)) at hbound
      refine hbound.trans (max_le ?_ ?_)
      · exact mul_le_mul_of_nonneg_right h4K hr2.le
      · calc B * (4 * (r ^ 2)⁻¹) = (4 * B) * (r ^ 2)⁻¹ := by ring
             _ ≤ K * (r ^ 2)⁻¹ := mul_le_mul_of_nonneg_right h4BK hr2.le
  refine ⟨r0, K, hr0, hK, ?_⟩
  intro t p r hr hrr hseed x hx
  exact hstage (V.toHistory.activeStage t) t (V.toHistory.activeStage_mem t)
    p x r hr hrr hseed hx

/-- Actual parabolic smallness supplies the low-base hypothesis of the finite
history estimate. No derivative or pinching data are added to the interface. -/
theorem exists_finite_history_seed_scalar_bound_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (V : RetainedCoreHistory.{u}) (IV : InitialIdentification P g V.toHistory)
    (pCut : CutoffParameters)
    (records : ∀ j : Fin V.eventCount, GeometricCutoffRecord V.toHistory j pCut)
    (kappa rho : ℝ) (hkappa : 0 < kappa) (hrho : 0 < rho)
    (hnc : V.NoncollapsedBefore kappa rho V.horizon)
    (A : ℝ) (hA : 0 < A) :
    ∃ r0 K : ℝ, 0 < r0 ∧ 0 < K ∧
      ∀ (t : Icc (0 : ℝ) V.horizon) (p : (V.toHistory.stageAt t).Carrier) (r : ℝ),
        r ≤ r0 → hasSmallParabolicCurvature V.toHistory t p r →
        ∀ x ∈ riemannianBallOf
          (V.toHistory.stageMetric (V.toHistory.activeStage t) t) p (A * r),
          metricScalarAt (V.toHistory.stageMetric (V.toHistory.activeStage t) t) x ≤
            K * (r ^ 2)⁻¹ := by
  obtain ⟨r0, K, hr0, hK, hbound⟩ := exists_finite_history_low_base_scalar_bound_CXSP
    V IV pCut records kappa rho hkappa hrho hnc A hA
  refine ⟨r0, K, hr0, hK, ?_⟩
  intro t p r hrr hsmall x hx
  have hr : 0 < r := hsmall.1
  have hpmem : p ∈ riemannianBallOf
      (V.toHistory.stageMetric (V.toHistory.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hseed := (le_abs_self _).trans
    (hasSmallParabolicCurvature_scalar_abs_le_C11S hsmall hpmem)
  exact hbound t p r hr hrr hseed x hx

end GC.LongTime.Ch11
