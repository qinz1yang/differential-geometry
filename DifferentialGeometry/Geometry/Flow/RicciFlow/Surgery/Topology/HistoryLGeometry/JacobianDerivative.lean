import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.JacobianAlong

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Matrix
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis)

open private bounds_of_action_eq_cost absolutelyContinuous_truncate from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.Truncation
open private mem_regularizedStage_Ioo from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.ExponentialSmooth
open private mem_Ioo_of_mem_stageDomain from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.IndexChain

universe u

variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {T w B₀ : ℝ} {p : (H.stage last).Carrier}

private theorem historyLAction_eq_sum_chain
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B₀ ≤ metricScalarAt (H.stageMetric j t) x)
    (hw : 0 < w) (Z₀ : H.historyLExpDomain hle T w p)
    (hZmin : Z₀.1 ∈ H.historyMinDomain hle T B₀ w p) {v : ℝ} (hv : 0 < v) (hvw : v ≤ w)
    {κ : Fin (H.eventCount + 1)} (hfκ : first ≤ κ) (hκl : κ ≤ last)
    (hvd : T - v ^ 2 ∈ H.stageDomain κ) (ch : H.LFamilyChain hle hfκ T w v p Z₀)
    (hn : 0 < ch.n) (Zv : H.historyLExpDomain hκl T v p) (hZv : Zv.1 = Z₀.1) :
    H.historyLAction hκl T v p Zv = ∑ k ∈ Finset.range ch.n,
      lRegularizedAction (ch.W k).S T (ch.γ k) (ch.c k) (ch.c (k + 1)) := by
  obtain ⟨hac, hmin, hfin⟩ := historyLCurve_minimizer hw Z₀ hZmin
  obtain ⟨hupper, hlower⟩ := bounds_of_action_eq_cost hmin hfin
  have hminv : Zv.1 ∈ H.historyMinDomain hκl T B₀ v p := by
    rw [hZv]; exact mem_historyMinDomain_of_le hfloor hκl hv hvw hvd hZmin
  have e1 := regularizedExtendedAction_historyLCurve_eq_historyLAction hfloor hv Zv hminv
  have hgeo' := (isHistoryLGeodesicOn_historyLCurve Z₀).truncate hfκ hκl hv hvw hvd
  have hinit' := (hasHistoryLInitialVector_historyLCurve Z₀).truncate hv hfκ hvd
  rw [← hZv] at hinit'
  have e2 := regularizedExtendedAction_historyLCurve_eq (B := B₀) hv Zv hgeo' hinit'
  have hac' := absolutelyContinuous_truncate hfκ hv.le hvw hupper hlower hvd hac
  have e3 := ch.toLWindowChain.regularizedExtendedAction_eq_sum hn hfloor hac'
  have h := e1.symm.trans (e2.trans e3)
  exact WithTop.coe_inj.1 h

private theorem hasDerivAt_log_bracket_nonpos {Hd E D src L A v tr : ℝ} (hv : 0 < v)
    (hsrc : 0 < src)
    (hHd : 0 ≤ Hd) (hE : 0 < E) (hD : D = tr * Hd)
    (htr : tr ≤ L / (4 * v ^ 2) - A / (4 * v ^ 3) + 3 / (2 * v ^ 2)) :
    D * (2 * v) / src * E + Hd / src * (E * (-(L * (2 * v) - A * 2) / (2 * v) ^ 2 -
      3 / 2 * (2 * v / v ^ 2))) ≤ 0 := by
  have key : D * (2 * v) / src * E + Hd / src * (E * (-(L * (2 * v) - A * 2) / (2 * v) ^ 2 -
      3 / 2 * (2 * v / v ^ 2))) = (Hd * E / src) * (2 * v * (tr - (L / (4 * v ^ 2) -
        A / (4 * v ^ 3) + 3 / (2 * v ^ 2)))) := by
    rw [hD]
    field_simp
    ring
  rw [key]
  refine mul_nonpos_of_nonneg_of_nonpos (by positivity) ?_
  have : 0 < 2 * v := by positivity
  nlinarith

theorem exists_hasDerivAt_historyReducedJacobianAlong
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B₀ ≤ metricScalarAt (H.stageMetric j t) x)
    (hw : 0 < w) (Z₀ : H.historyLExpDomain hle T w p)
    (hZmin : Z₀.1 ∈ H.historyMinDomain hle T B₀ w p)
    (hwk : T - w ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first)) {v : ℝ} (hv : 0 < v)
    (hvw : v < w) (hvF : T - v ^ 2 ∉ range H.time) :
    ∃ d ≤ 0, HasDerivAt (H.historyReducedJacobianAlong Z₀) d v := by
  classical
  have hZo := historyMinDomain_subset_historyLExpOpenDomain hw hwk hfloor hZmin
  have hT := stageDomain_last_of_historyLExpDomain Z₀
  set κ := H.historyStage T v with hκdef
  have hvd := mem_stageDomain_historyStage (mem_Icc_of_historyLExpDomain Z₀ hv hvw.le)
  have hTh : T - v ^ 2 < H.horizon := by
    have := (H.le_stageEndTime_of_mem_stageDomain hT).trans (H.stageEndTime_le_horizon last)
    nlinarith
  have hvk := mem_Ioo_of_mem_stageDomain hvd hvF hTh
  have hfκ : first ≤ κ := le_historyStage Z₀ hv hvw.le
  have hκl : κ ≤ last := historyStage_le_last Z₀ hv hvw.le
  obtain ⟨hac, hmin, hfin⟩ := historyLCurve_minimizer hw Z₀ hZmin
  have hgeo := isHistoryLGeodesicOn_historyLCurve Z₀
  obtain ⟨ch, hn, hli⟩ :=
    exists_family_chain_linearIndependent hfloor hw Z₀ hZmin hZo hv hvw hfκ hκl hvk
  obtain ⟨P, hP⟩ := ch.exists_isAdaptedFrame hn
  have hbound := LFamilyChain.half_trace_le hP hn hv hli (fun V hV hVg hV0 hVv =>
    LWindowChain.historyLIndex_nonneg_of_minimizer hfloor hgeo hac hmin hfin hv hvw.le hfκ hκl hvd
      ch.toLWindowChain V hV hVg hV0 hVv)
  set k := ch.n - 1 with hkdef
  have hk : k < ch.n := Nat.sub_lt hn one_pos
  have hvK : v ∈ ch.K k := ch.mem_K_last hn
  have hvW : v ∈ Ioo (ch.W k).a (ch.W k).b := ch.K_W k ⟨hvK, hv⟩
  have hstage : ch.stage (k + 1) = κ := by rw [hkdef, Nat.sub_add_cancel hn, ch.stage_n]
  have hvpiece : v ∈ Ioo (H.regularizedStageStart T (ch.W k).a (ch.bottom hk).val)
      (H.regularizedStageEnd T (ch.W k).b (ch.bottom hk).val) := by
    refine mem_regularizedStage_Ioo (ch.W _).nonneg hvW ?_
    change T - v ^ 2 ∈ Ioo (H.time (ch.stage (k + 1))) (H.stageEndTime (ch.stage (k + 1)))
    rw [hstage]
    exact hvk
  have hKo : IsOpen (ch.K k ∩ Ioi 0) := (ch.isOpen_K k).inter isOpen_Ioi
  have hβ' := (ch.smooth k).mono (prod_mono subset_rfl (inter_subset_left (t := Ioi (0 : ℝ))))
  have hgeo' : ∀ Z ∈ ch.V k, IsLRegularizedGeodesicOn (ch.W k).S T (fun r => ch.β k (Z, r))
      (ch.K k ∩ Ioi 0) := fun Z hZ s hs => ch.family k Z hZ s hs.1
  have hrep' := fun Z (hZ : Z ∈ ch.V k) (j : H.StageInterval (ch.lo k) (ch.hi k)) r
    (hr : r ∈ (ch.K k ∩ Ioi 0) ∩ Ioo (H.regularizedStageStart T (ch.W k).a j.val)
      (H.regularizedStageEnd T (ch.W k).b j.val)) => ch.rep k Z hZ j r ⟨hr.1.1, hr.2⟩
  have hpos : 0 < (lGram (ch.W k).S T (fun q => ch.β k (Z₀.1, Real.sqrt q))
      (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => ch.β k (Z, Real.sqrt q)) Z₀.1
        (chartModelBasis ThreeSpace i)) (v ^ 2)).det := by
    rw [ch.lGram_last hn hv]
    exact DifferentialGeometry.Geometry.Riemannian.Variation.curveGram_det_pos
      ((ch.W k).S.base.metric (T - v ^ 2)) (fun _ => ch.γ k v) (fun i _ => ch.jacobiField i k v)
      0 hli
  have hτ : Real.sqrt (v ^ 2) ∈ (ch.K k ∩ Ioi 0) ∩ Ioo
      (H.regularizedStageStart T (ch.W k).a (ch.bottom hk).val)
      (H.regularizedStageEnd T (ch.W k).b (ch.bottom hk).val) := by
    rw [Real.sqrt_sq hv.le]
    exact ⟨⟨hvK, hv⟩, hvpiece⟩
  have hder := hasDerivAt_historyLJacobianDensity (hlo := hfκ.trans (ch.first_le k))
    (hhi := ch.le_last k) (Z₀ := Z₀) (ch.isOpen_V k) (ch.mem_V k) (ch.V_sub k) hKo (ch.K_W k)
    hβ' hgeo' hrep' (ch.bottom hk) hτ hpos
  have hLJD := historyLJacobianDensity_eq_lJacobianDensity_sq (hlo := hfκ.trans (ch.first_le k))
    (hhi := ch.le_last k) (Z₀ := Z₀) (ch.isOpen_V k) (ch.mem_V k) (ch.V_sub k) hKo (ch.K_W k)
    hβ' hrep' (ch.bottom hk) (r := v) ⟨⟨hvK, hv⟩, hvpiece⟩
  have hJ : (⟨(ch.bottom hk).val, (hfκ.trans (ch.first_le k)).trans (ch.bottom hk).property.1,
      (ch.bottom hk).property.2.trans (ch.le_last k)⟩ : H.StageInterval first last) =
      ⟨κ, hfκ, hκl⟩ := Subtype.ext hstage
  rw [hJ] at hder hLJD
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * v) v := by simpa using hasDerivAt_pow 2 v
  have hHdd := (HasDerivAt.comp_of_eq v hder hsq rfl).congr_of_eventuallyEq
    (f₁ := fun s => H.historyLJacobianDensity hle T w p Z₀ ⟨κ, hfκ, hκl⟩ s) (by
    filter_upwards [lt_mem_nhds hv] with x hx
    simp only [Function.comp, Real.sqrt_sq hx.le])
  have hmemv := mem_historyLExpDomain_of_le hfκ hκl hv hvw.le hvd Z₀.2
  have hAsum := historyLAction_eq_sum_chain hfloor hw Z₀ hZmin hv hvw.le hfκ hκl hvd ch hn
    ⟨Z₀.1, hmemv⟩ rfl
  have hU : IsOpen {s : ℝ | T - s ^ 2 ∈ (ch.W k).D.regular} :=
    (ch.W k).D.regular_isOpen.preimage (by fun_prop)
  have hvU : v ∈ {s : ℝ | T - s ^ 2 ∈ (ch.W k).D.regular} :=
    (ch.W k).regular v ⟨hvW.1.le, hvW.2.le⟩
  have hLcont : ContinuousOn (lRegularizedLagrangian (ch.W k).S T (ch.γ k))
      {s : ℝ | T - s ^ 2 ∈ (ch.W k).D.regular} := by
    have hc := lRegularizedLagrangian_continuousOn_carrier (ch.W k).S (ch.W k).solution (ch.γ k)
      ((ch.contMDiff k).of_le (by decide))
    have hh := hc.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s (hs : s ∈ {s : ℝ | T - s ^ 2 ∈ (ch.W k).D.regular}) =>
        ((ch.W k).D.regular_subset hs : (T, s).1 - (T, s).2 ^ 2 ∈ (ch.W k).D.carrier))
    exact hh
  have hI : HasDerivAt (fun v' => lRegularizedAction (ch.W k).S T (ch.γ k) v v')
      (lRegularizedLagrangian (ch.W k).S T (ch.γ k) v) v :=
    intervalIntegral.integral_hasDerivAt_right IntervalIntegrable.refl
      (hLcont.stronglyMeasurableAtFilter hU v hvU) (hLcont.continuousAt (hU.mem_nhds hvU))
  have hβc : ∀ r ∈ ch.K k ∩ Ioi 0, ContinuousAt (fun s => ch.β k (Z₀.1, s)) r := fun r hr =>
    ((hβ' (Z₀.1, r) ⟨ch.mem_V k, hr⟩).continuousWithinAt.comp
      (continuous_const.prodMk continuous_id).continuousWithinAt
      (fun s hs => ⟨ch.mem_V k, hs⟩)).continuousAt (hKo.mem_nhds hr)
  have hrepZ := fun (j : H.StageInterval (ch.lo k) (ch.hi k)) r
    (hr : r ∈ (ch.K k ∩ Ioi 0) ∩ Ioo (H.regularizedStageStart T (ch.W k).a j.val)
      (H.regularizedStageEnd T (ch.W k).b j.val)) => ch.rep k Z₀.1 (ch.mem_V k) j r ⟨hr.1.1, hr.2⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hKo v ⟨hvK, hv⟩
  have hcont : Continuous fun s : ℝ => T - s ^ 2 := by fun_prop
  have hrepr : ∀ᶠ v' in 𝓝 v, H.historyReducedJacobianAlong Z₀ v' =
      H.historyLJacobianDensity hle T w p Z₀ ⟨κ, hfκ, hκl⟩ v' / H.historyLSourceDensity T p *
        Real.exp (-(H.historyLAction hκl T v p ⟨Z₀.1, hmemv⟩ +
          lRegularizedAction (ch.W k).S T (ch.γ k) v v') / (2 * v') -
          (3 / 2 : ℝ) * Real.log (v' ^ 2) - (3 / 2 : ℝ) * Real.log (4 * Real.pi)) := by
    filter_upwards [Metric.ball_mem_nhds v hε, gt_mem_nhds hvw,
      hcont.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hvk)] with v' h1 h2 h3
    have hv'K := hball h1
    have hv' : 0 < v' := hv'K.2
    have hv'd : T - v' ^ 2 ∈ H.stageDomain κ := H.mem_stageDomain_of_mem_Ioo h3
    have hmem' := mem_historyLExpDomain_of_le hfκ hκl hv' h2.le hv'd Z₀.2
    rw [historyReducedJacobianAlong_eq Z₀ hv' h2.le hκl hv'd ⟨Z₀.1, hmem'⟩ rfl]
    unfold historyReducedJacobian
    rw [historyLJacobianDensity_domain hw Z₀ hZo hfκ hκl hv' h2.le hv'd ⟨Z₀.1, hmem'⟩ rfl]
    have hsubI : ∀ {a b : ℝ}, a ∈ Metric.ball v ε → b ∈ Metric.ball v ε → Icc a b ⊆
        ch.K k ∩ Ioi 0 := fun ha hb r hr => hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ha hb ⊢
      constructor <;> linarith [hr.1, hr.2, ha.1, ha.2, hb.1, hb.2])
    have hA : H.historyLAction hκl T v' p ⟨Z₀.1, hmem'⟩ =
        H.historyLAction hκl T v p ⟨Z₀.1, hmemv⟩ +
          lRegularizedAction (ch.W k).S T (ch.γ k) v v' := by
      rcases lt_trichotomy v v' with hlt | heq | hgt
      · exact historyLAction_split hfloor hw Z₀ hZmin (hfκ.trans (ch.first_le k)) (ch.le_last k)
          (ch.W k) hKo (ch.K_W k) hβc hrepZ (ch.γ k) (ch.contMDiff k)
          (fun r hr => (ch.curve k r hr.1).symm) hv hlt (hsubI (Metric.mem_ball_self hε) h1) h2
          hκl hκl hvd hv'd ⟨Z₀.1, hmemv⟩ ⟨Z₀.1, hmem'⟩ rfl rfl
      · subst heq
        simp [lRegularizedAction]
      · have h := historyLAction_split hfloor hw Z₀ hZmin (hfκ.trans (ch.first_le k))
          (ch.le_last k) (ch.W k) hKo (ch.K_W k) hβc hrepZ (ch.γ k) (ch.contMDiff k)
          (fun r hr => (ch.curve k r hr.1).symm) hv' hgt (hsubI h1 (Metric.mem_ball_self hε))
          hvw hκl hκl hv'd hvd ⟨Z₀.1, hmem'⟩ ⟨Z₀.1, hmemv⟩ rfl rfl
        rw [h, lRegularizedAction, lRegularizedAction, intervalIntegral.integral_symm]
        ring
    rw [hA]
  have hI0 : lRegularizedAction (ch.W k).S T (ch.γ k) v v = 0 := by
    simp [lRegularizedAction]
  have hq : HasDerivAt (fun v' => -(H.historyLAction hκl T v p ⟨Z₀.1, hmemv⟩ +
      lRegularizedAction (ch.W k).S T (ch.γ k) v v') / (2 * v'))
      (-(lRegularizedLagrangian (ch.W k).S T (ch.γ k) v * (2 * v) -
        (H.historyLAction hκl T v p ⟨Z₀.1, hmemv⟩ + 0) * 2) / (2 * v) ^ 2) v := by
    have h := ((hI.const_add (H.historyLAction hκl T v p ⟨Z₀.1, hmemv⟩)).div
      ((hasDerivAt_id v).const_mul 2) (mul_ne_zero two_ne_zero hv.ne')).neg
    rw [hI0] at h
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    · simp only [id]
      ring
    · simp only [id, Pi.div_apply, Pi.neg_apply]
      ring
  have hlog : HasDerivAt (fun v' : ℝ => Real.log (v' ^ 2)) (2 * v / v ^ 2) v :=
    hsq.log (by positivity)
  have hexp := ((hq.sub (hlog.const_mul (3 / 2 : ℝ))).sub_const
    ((3 / 2 : ℝ) * Real.log (4 * Real.pi))).exp
  have hg := (hHdd.div_const (H.historyLSourceDensity T p)).mul hexp
  refine ⟨_, ?_, hg.congr_of_eventuallyEq hrepr⟩
  have hsum' := hAsum
  simp only [add_zero] at hg ⊢
  refine hasDerivAt_log_bracket_nonpos hv historyLSourceDensity_pos
    (historyLJacobianDensity_nonneg _ _) (Real.exp_pos _) (tr := (1 / 2) * trace
      ((lGram (ch.W k).S T (fun q => ch.β k (Z₀.1, Real.sqrt q))
        (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => ch.β k (Z, Real.sqrt q)) Z₀.1
          (chartModelBasis ThreeSpace i)) (v ^ 2))⁻¹ *
        lGramDeriv (ch.W k).S T (fun q => ch.β k (Z₀.1, Real.sqrt q))
          (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => ch.β k (Z, Real.sqrt q))
            Z₀.1 (chartModelBasis ThreeSpace i)) (v ^ 2))) ?_ ?_
  · rw [hLJD]
  · rw [hsum']
    exact hbound

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
