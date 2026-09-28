import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.AlongGeodesic

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman

open private mem_regularizedStage_Ioo LWindow.mem_range_of_mem_Icc from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.Regularity

open private stageRegularizedLagrangian_congr_of_eventuallyEq from
DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.AlongGeodesic

universe u

variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {T B v : ℝ} {p : (H.stage last).Carrier}

open Classical in
variable (H) in
private def pieceLagrangian (hle : first ≤ last) (T v : ℝ) (p : (H.stage last).Carrier)
    (j : H.StageInterval first last) (Z : ThreeSpace) (r : ℝ) : ℝ :=
  if hZ : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p then
    H.stageRegularizedLagrangian j.val T (H.historyLCurve hle T v p ⟨Z, hZ⟩ j) r
  else 0

private theorem pieceLagrangian_of_mem (j : H.StageInterval first last) {Z : ThreeSpace}
    (hZ : (Z : TangentSpace ThreeModel p) ∈ H.historyLExpDomain hle T v p) (r : ℝ) :
    H.pieceLagrangian hle T v p j Z r =
      H.stageRegularizedLagrangian j.val T (H.historyLCurve hle T v p ⟨Z, hZ⟩ j) r := by
  unfold pieceLagrangian
  exact dite_eq_left hZ

private theorem mem_Ioo_of_mem_regularizedStage_Ioo' {j : Fin (H.eventCount + 1)} {u r : ℝ}
    (hr : r ∈ Ioo (H.regularizedStageStart T u j) (H.regularizedStageEnd T v j)) :
    T - r ^ 2 ∈ Ioo (H.time j) (H.stageEndTime j) := by
  have hr0 : 0 < r := (Real.sqrt_nonneg _).trans_lt hr.1
  have h1 := (Real.sqrt_lt' hr0).1 hr.1
  have h2 := (Real.lt_sqrt hr0.le).1 hr.2
  constructor
  · have := le_max_right (T - v ^ 2) (H.time j)
    linarith
  · have := min_le_right (T - u ^ 2) (H.stageEndTime j)
    linarith

private theorem continuousAt_pieceLagrangian (hv : 0 < v) {Z₀ : ThreeSpace}
    (hZ₀ : (Z₀ : TangentSpace ThreeModel p) ∈ H.historyLExpOpenDomain hle T v p)
    (j : H.StageInterval first last) {r : ℝ}
    (hr : r ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) :
    ContinuousAt (fun Z => H.pieceLagrangian hle T v p j Z r) Z₀ := by
  have hdom₀ := historyLExpOpenDomain_subset_historyLExpDomain hZ₀
  have hupper : T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    obtain ⟨lo₀, -, W₀, -, -, ha₀, -⟩ :=
      hasHistoryLInitialVector_historyLCurve (⟨Z₀, hdom₀⟩ : H.historyLExpDomain hle T v p)
    have h := W₀.upper_mem_Icc
    rwa [ha₀] at h
  have hb := H.regularizedStage_bounds le_rfl hv.le hupper
    (isHistoryLGeodesicOn_historyLCurve (⟨Z₀, hdom₀⟩ : H.historyLExpDomain hle T v p)).1 j
  have hr0v : r ∈ Ioo 0 v := ⟨hb.1.trans_lt hr.1, hr.2.trans_le hb.2.2⟩
  obtain ⟨V, hV, hZ₀V, -, hVdom, lo, hi, hlo, hhi, W, K, hK, hrK, hKW, β, hβ, -, hrep⟩ :=
    exists_contMDiffOn_window_family_historyLCurve hv hZ₀ hr0v
  have hIoo := mem_Ioo_of_mem_regularizedStage_Ioo' hr
  have hjW : lo ≤ j.val ∧ j.val ≤ hi :=
    LWindow.mem_range_of_mem_Icc W (hKW hrK) ⟨hIoo.1.le, hIoo.2.le⟩
  have hopen : IsOpen (V ×ˢ K) := hV.prod hK
  have hG := continuousOn_lRegularizedLagrangian_family_of_contMDiffOn_one W.S W.solution T hV hK
    (hβ.of_le (by decide)) subset_rfl fun s hs => W.mem_carrier (Ioo_subset_Icc_self (hKW hs))
  have hpair : ContinuousAt (fun Z : ThreeSpace => (Z, r)) Z₀ :=
    continuousAt_id.prodMk continuousAt_const
  have hGc : ContinuousAt (fun Z => lRegularizedLagrangian W.S T (fun s => β (Z, s)) r) Z₀ :=
    ContinuousAt.comp (f := fun Z : ThreeSpace => (Z, r))
      ((hG (Z₀, r) ⟨hZ₀V, hrK⟩).continuousAt (hopen.mem_nhds ⟨hZ₀V, hrK⟩)) hpair
  refine hGc.congr ?_
  filter_upwards [hV.mem_nhds hZ₀V] with Z hZ
  have hO : IsOpen (K ∩ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val))
    := hK.inter isOpen_Ioo
  have hev : H.historyLCurve hle T v p ⟨Z, hVdom Z hZ⟩ j =ᶠ[𝓝 r]
      W.f ⟨j.val, hjW⟩ ∘ fun s => β (Z, s) := by
    filter_upwards [hO.mem_nhds ⟨hrK, hr⟩] with s hs
    exact hrep Z hZ ⟨j.val, hjW⟩ s ⟨hs.1, mem_regularizedStage_Ioo W.nonneg (hKW hs.1)
      (mem_Ioo_of_mem_regularizedStage_Ioo' hs.2)⟩
  have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) ThreeModel (fun s => β (Z, s)) r :=
    ((((hβ (Z, r) ⟨hZ, hrK⟩).contMDiffAt (hopen.mem_nhds ⟨hZ, hrK⟩)).comp r
      (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by decide))
  rw [pieceLagrangian_of_mem j (hVdom Z hZ) r, stageRegularizedLagrangian_congr_of_eventuallyEq
    j.val T hev, H.stageRegularizedLagrangian_comp_eq_of_localPullMetric j.val W.S
    (W.f ⟨j.val, hjW⟩) (W.localDiffeomorph _) T hmd
    (W.metric ⟨j.val, hjW⟩ r (mem_regularizedStage_Ioo W.nonneg (hKW hrK) hIoo))]

private theorem neg_le_stageRegularizedLagrangian
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (j : H.StageInterval first last) (β : ℝ → (H.stage j.val).Carrier) {r : ℝ}
    (hr : r ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) :
    -(2 * B * r ^ 2) ≤ H.stageRegularizedLagrangian j.val T β r := by
  have hsc := hfloor j.val _ (H.mapsTo_regularizedStage_Ioo T 0 v j.val hr) (β r)
  have hkin : 0 ≤ (H.stageMetric j.val (T - r ^ 2)).inner (β r) (lVelocity (I := ThreeModel) β r)
      (lVelocity (I := ThreeModel) β r) := by
    by_cases h0 : lVelocity (I := ThreeModel) β r = 0
    · rw [h0]
      simp
    · exact ((H.stageMetric j.val _).pos _ _ h0).le
  unfold stageRegularizedLagrangian
  nlinarith [sq_nonneg r]

private theorem regularizedStage_le_of_mem_historyLExpDomain (hv : 0 < v)
    (Z : H.historyLExpDomain hle T v p) (j : H.StageInterval first last) :
    H.regularizedStageStart T 0 j.val ≤ H.regularizedStageEnd T v j.val := by
  have hupper : T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    obtain ⟨lo₀, -, W₀, -, -, ha₀, -⟩ := hasHistoryLInitialVector_historyLCurve Z
    have h := W₀.upper_mem_Icc
    rwa [ha₀] at h
  exact (H.regularizedStage_bounds le_rfl hv.le hupper
    (isHistoryLGeodesicOn_historyLCurve Z).1 j).2.1

private theorem lowerSemicontinuousAt_integral_pieceLagrangian
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x) (hv : 0 < v) {Z₀ : ThreeSpace}
    (hZ₀ : (Z₀ : TangentSpace ThreeModel p) ∈ H.historyLExpOpenDomain hle T v p)
    (j : H.StageInterval first last) :
    LowerSemicontinuousAt (fun Z => ∫ r in Ioo (H.regularizedStageStart T 0 j.val)
      (H.regularizedStageEnd T v j.val), H.pieceLagrangian hle T v p j Z r) Z₀ := by
  classical
  set I := Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) with hI
  set U : Set ThreeSpace := H.historyLExpOpenDomain hle T v p with hUdef
  have hU : U ∈ 𝓝 Z₀ := (isOpen_historyLExpOpenDomain hv).mem_nhds hZ₀
  have hab := regularizedStage_le_of_mem_historyLExpDomain hv
    (⟨Z₀, historyLExpOpenDomain_subset_historyLExpDomain hZ₀⟩ : H.historyLExpDomain hle T v p) j
  have hint : ∀ Z ∈ U, Integrable (H.pieceLagrangian hle T v p j Z) (volume.restrict I) := by
    intro Z hZ
    have hd := historyLExpOpenDomain_subset_historyLExpDomain hZ
    have h := intervalIntegrable_stageRegularizedLagrangian_historyLCurve hv ⟨Z, hd⟩ j
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab] at h
    exact h.congr_fun (fun r _ => (pieceLagrangian_of_mem j hd r).symm) measurableSet_Ioo
  have h2 : Integrable (fun r : ℝ => 2 * B * r ^ 2) (volume.restrict I) :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioo_subset_Icc_self
  have hnn : ∀ Z ∈ U, ∀ r ∈ I, 0 ≤ H.pieceLagrangian hle T v p j Z r + 2 * B * r ^ 2 := by
    intro Z hZ r hr
    have hd := historyLExpOpenDomain_subset_historyLExpDomain hZ
    rw [pieceLagrangian_of_mem j hd r]
    linarith [neg_le_stageRegularizedLagrangian hfloor j
      (H.historyLCurve hle T v p ⟨Z, hd⟩ j) hr]
  set c := ∫ r in I, 2 * B * r ^ 2 with hc
  set Φ : ThreeSpace → ℝ := fun Z => ∫ r in I, H.pieceLagrangian hle T v p j Z r with hΦ
  have he : ∀ Z ∈ U, Φ Z + c = ∫ r in I, (H.pieceLagrangian hle T v p j Z r + 2 * B * r ^ 2) :=
    fun Z hZ => (integral_add (hint Z hZ) h2).symm
  have hlin : ∀ Z ∈ U, ∫⁻ r in I, ENNReal.ofReal (H.pieceLagrangian hle T v p j Z r +
      2 * B * r ^ 2) = ENNReal.ofReal (Φ Z + c) := by
    intro Z hZ
    rw [he Z hZ, ofReal_integral_eq_lintegral_ofReal
      (f := fun r => H.pieceLagrangian hle T v p j Z r + 2 * B * r ^ 2) ((hint Z hZ).add h2)]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hnn Z hZ r hr
  have hsum : ∀ Z ∈ U, 0 ≤ Φ Z + c := by
    intro Z hZ
    rw [he Z hZ]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hnn Z hZ r hr
  set g : ThreeSpace → ℝ → ℝ≥0∞ := fun Z r =>
    if Z ∈ U then ENNReal.ofReal (H.pieceLagrangian hle T v p j Z r + 2 * B * r ^ 2) else 0
    with hg
  have hmeas : ∀ Z, AEMeasurable (g Z) (volume.restrict I) := by
    intro Z
    by_cases hZ : Z ∈ U
    · simp only [hg, ite_eq_left hZ]
      exact ((hint Z hZ).add h2).aemeasurable.ennreal_ofReal
    · simp only [hg, ite_eq_right hZ]
      exact aemeasurable_const
  have hF := lintegral_liminf_le' (μ := volume.restrict I) (u := 𝓝 Z₀) hmeas
  have hlim : ∀ r ∈ I, liminf (fun Z => g Z r) (𝓝 Z₀) = g Z₀ r := by
    intro r hr
    have hcont := continuousAt_pieceLagrangian hv hZ₀ j hr
    have ht : Tendsto (fun Z => ENNReal.ofReal (H.pieceLagrangian hle T v p j Z r +
        2 * B * r ^ 2)) (𝓝 Z₀) (𝓝 (g Z₀ r)) := by
      have hval : g Z₀ r = ENNReal.ofReal (H.pieceLagrangian hle T v p j Z₀ r + 2 * B * r ^ 2) :=
        ite_eq_left hZ₀
      have hc2 : ContinuousAt (fun Z => ENNReal.ofReal (H.pieceLagrangian hle T v p j Z r +
          2 * B * r ^ 2)) Z₀ :=
        ENNReal.continuous_ofReal.continuousAt.comp (hcont.add continuousAt_const)
      rw [hval]
      exact hc2.tendsto
    refine (ht.congr' ?_).liminf_eq
    filter_upwards [hU] with Z hZ
    simp only [hg, ite_eq_left hZ]
  have hΨ0 : ∫⁻ r in I, g Z₀ r = ∫⁻ r in I, liminf (fun Z => g Z r) (𝓝 Z₀) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact (hlim r hr).symm
  have hgU : ∀ Z ∈ U, ∫⁻ r in I, g Z r = ENNReal.ofReal (Φ Z + c) := fun Z hZ => by
    simp only [hg, ite_eq_left hZ]
    exact hlin Z hZ
  intro a ha
  change a < Φ Z₀ at ha
  by_cases hac : a + c < 0
  · filter_upwards [hU] with Z hZ
    change a < Φ Z
    linarith [hsum Z hZ]
  rw [not_lt] at hac
  have hpos : 0 < Φ Z₀ + c := by linarith
  have h1 : ENNReal.ofReal (a + c) < ∫⁻ r in I, g Z₀ r := by
    rw [hgU Z₀ hZ₀]
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 (by linarith)
  have h3 := eventually_lt_of_lt_liminf (h1.trans_le (hΨ0 ▸ hF))
  filter_upwards [h3, hU] with Z hZ hZU
  rw [hgU Z hZU] at hZ
  change a < Φ Z
  linarith [((ENNReal.ofReal_lt_ofReal_iff').1 hZ).1]

private theorem historyLCurve_last_zero (Z : H.historyLExpDomain hle T v p) :
    H.historyLCurve hle T v p Z ⟨last, hle, le_rfl⟩ 0 = p := by
  obtain ⟨lo, hlo, W, x, Zx, ha0, hx, -, hdom, heqB⟩ := hasHistoryLInitialVector_historyLCurve Z
  obtain ⟨α₁, J, hJo, hJc, h0J, -, hcurve⟩ := hdom
  have hupper : T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    have h := W.upper_mem_Icc
    rwa [ha0] at h
  have h0 : (0 : ℝ) ∈ Icc (H.regularizedStageStart T 0 last) (H.regularizedStageEnd T W.b last) :=
    ⟨(H.regularizedStageStart_eq_of_mem_Icc le_rfl hupper).le, Real.sqrt_nonneg _⟩
  have e := heqB ⟨last, W.le, le_rfl⟩ h0
  have hc : lRegularizedCurve W.S T x Zx 0 = x :=
    (lRegularizedCurve_eqOn W.S W.solution T hJo hJc h0J hcurve h0J).trans hcurve.1
  simp only [Function.comp_apply, hc, hx] at e
  exact e.symm

private theorem measurableSet_historyMinDomain_of_isOpen
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x) (hv : 0 < v) {U : Set ThreeSpace}
    (hU : IsOpen U) (hKU : H.historyMinDomain hle T B v p ⊆ U)
    (hUd : U ⊆ H.historyLExpDomain hle T v p) {f : ThreeSpace → (H.stage first).Carrier}
    (hf : ContinuousOn f U)
    (hfeq : ∀ Z (hZ : Z ∈ H.historyLExpDomain hle T v p), f Z = H.historyLExp hle T v p ⟨Z, hZ⟩)
    {L : ThreeSpace → ℝ} (hL : ∀ Z ∈ U, LowerSemicontinuousAt L Z)
    (hLeq : ∀ Z (hZ : Z ∈ H.historyLExpDomain hle T v p),
      L Z = H.historyLAction hle T v p ⟨Z, hZ⟩) :
    @MeasurableSet ThreeSpace (borel ThreeSpace) (H.historyMinDomain hle T B v p) := by
  set c := H.regularizedCost first last hle T B 0 v p with hcdef
  have hchar : ∀ Z ∈ U, Z ∈ H.historyMinDomain hle T B v p ↔ ((L Z : ℝ) : WithTop ℝ) ≤ c (f Z) := by
    intro Z hZU
    have hd := hUd hZU
    set Zd : H.historyLExpDomain hle T v p := ⟨Z, hd⟩
    constructor
    · intro hK
      rw [hfeq Z hd, hLeq Z hd]
      exact (regularizedCost_historyLExp_eq hfloor hv Zd hK).ge
    · intro hle'
      have hgeo := isHistoryLGeodesicOn_historyLCurve Zd
      have hupper : T - 0 ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
        obtain ⟨lo₀, -, W₀, -, -, ha₀, -⟩ := hasHistoryLInitialVector_historyLCurve Zd
        have h := W₀.upper_mem_Icc
        rwa [ha₀] at h
      have hAC := absolutelyContinuousOnInterval_historyLCurve hv Zd
      have hact := regularizedExtendedAction_historyLCurve_eq_historyLAction_of_mem hfloor hv Zd
      have hmem : H.regularizedExtendedAction first last T B 0 v (H.historyLCurve hle T v p Zd) ∈
          H.regularizedActionValues first last hle T B 0 v p
            (H.historyLCurve hle T v p Zd ⟨first, le_rfl, hle⟩ v) := by
        refine ⟨le_rfl, hv.le, hupper, hgeo.1, _, hAC, historyLCurve_last_zero Zd, rfl,
          fun i hf hl => ?_, rfl⟩
        obtain ⟨z, -, h1, h2⟩ := hgeo.2.1 i hf hl
        exact ⟨z, h1, h2⟩
      have hcle := H.regularizedCost_le_of_competitor first last hle T B 0 v p _ hmem
      have hfZ : f Z = H.historyLCurve hle T v p Zd ⟨first, le_rfl, hle⟩ v := hfeq Z hd
      rw [hfZ, hLeq Z hd, ← hact] at hle'
      refine ⟨H.historyLCurve hle T v p Zd, hgeo, hasHistoryLInitialVector_historyLCurve Zd,
        hAC, historyLCurve_last_zero Zd, le_antisymm hle' hcle, ?_⟩
      rw [hact]
      exact WithTop.coe_ne_top
  set O : Set ThreeSpace := {Z | Z ∈ U ∧ c (f Z) < ((L Z : ℝ) : WithTop ℝ)} with hOdef
  have hKeq : H.historyMinDomain hle T B v p = U \ O := by
    ext Z
    constructor
    · intro hK
      have hZU := hKU hK
      exact ⟨hZU, fun hO => not_lt.2 ((hchar Z hZU).1 hK) hO.2⟩
    · rintro ⟨hZU, hnO⟩
      exact (hchar Z hZU).2 (not_lt.1 fun h => hnO ⟨hZU, h⟩)
  have hO : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    rintro Z₀ ⟨hZ₀U, hlt⟩
    obtain ⟨z, hz1, hz2⟩ := exists_between hlt
    lift z to ℝ using hz2.ne_top with a
    have hcost := (upperSemicontinuous_regularizedCost (hle := hle) (p := p) hv hfloor)
      (f Z₀) (a : WithTop ℝ) hz1
    have hfc : ContinuousAt f Z₀ := (hf Z₀ hZ₀U).continuousAt (hU.mem_nhds hZ₀U)
    filter_upwards [hfc.eventually hcost, hL Z₀ hZ₀U a (WithTop.coe_lt_coe.1 hz2),
      hU.mem_nhds hZ₀U] with Z h1 h2 h3
    exact ⟨h3, h1.trans (WithTop.coe_lt_coe.2 h2)⟩
  rw [hKeq]
  have hUm : @MeasurableSet ThreeSpace (borel ThreeSpace) U :=
    MeasurableSpace.measurableSet_generateFrom hU
  have hOm : @MeasurableSet ThreeSpace (borel ThreeSpace) O :=
    MeasurableSpace.measurableSet_generateFrom hO
  exact @MeasurableSet.diff ThreeSpace (borel ThreeSpace) U O hUm hOm

theorem measurableSet_historyMinDomain_of_mem_Ioo (hv : 0 < v)
    (hend : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x) :
    @MeasurableSet ThreeSpace (borel ThreeSpace) (H.historyMinDomain hle T B v p) := by
  classical
  rcases (H.historyMinDomain hle T B v p).eq_empty_or_nonempty with he | ⟨Z₁, hZ₁⟩
  · rw [he]
    exact @MeasurableSet.empty ThreeSpace (borel ThreeSpace)
  have hsubU := historyMinDomain_subset_historyLExpOpenDomain (hle := hle) (p := p) hv hend hfloor
  obtain ⟨f, hf, hfeq⟩ := exists_contMDiffOn_historyLExp (hle := hle) (p := p) hv
    (H.historyLExp hle T v p ⟨Z₁, historyMinDomain_subset_historyLExpDomain hZ₁⟩)
  set L : ThreeSpace → ℝ := fun Z => ∑ j : H.StageInterval first last,
    ∫ r in Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      H.pieceLagrangian hle T v p j Z r with hLdef
  have hLeq : ∀ Z (hZ : Z ∈ H.historyLExpDomain hle T v p),
      L Z = H.historyLAction hle T v p ⟨Z, hZ⟩ := by
    intro Z hZ
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [stageRegularizedAction, intervalIntegral.integral_of_le
      (regularizedStage_le_of_mem_historyLExpDomain hv ⟨Z, hZ⟩ j), integral_Ioc_eq_integral_Ioo]
    exact setIntegral_congr_fun measurableSet_Ioo fun r _ => pieceLagrangian_of_mem j hZ r
  refine measurableSet_historyMinDomain_of_isOpen hfloor hv (isOpen_historyLExpOpenDomain hv)
    hsubU historyLExpOpenDomain_subset_historyLExpDomain hf.continuousOn hfeq
    (fun Z hZ => lowerSemicontinuousAt_sum fun j _ =>
      lowerSemicontinuousAt_integral_pieceLagrangian hfloor hv hZ j) hLeq

theorem measurableSet_historyMinDomain (hv : 0 < v)
    (hT : T ∈ Ico (H.time last) (H.stageEndTime last))
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x) :
    @MeasurableSet ThreeSpace (borel ThreeSpace) (H.historyMinDomain hle T B v p) := by
  rcases (H.historyMinDomain hle T B v p).eq_empty_or_nonempty with he | ⟨Z₁, hZ₁⟩
  · rw [he]
    exact @MeasurableSet.empty ThreeSpace (borel ThreeSpace)
  obtain ⟨U, hU, hKU, hUd, ⟨f, hf, hfeq⟩, L, hL, hLeq⟩ :=
    exists_isOpen_superset_historyMinDomain_subset_historyLExpDomain (hle := hle) (p := p) hv hT
      hfloor (H.historyLExp hle T v p ⟨Z₁, historyMinDomain_subset_historyLExpDomain hZ₁⟩)
  exact measurableSet_historyMinDomain_of_isOpen hfloor hv hU hKU hUd hf.continuousOn hfeq
    (fun Z hZ => (hL.continuousAt (hU.mem_nhds hZ)).lowerSemicontinuousAt) hLeq

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
