import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSplicePostBC12X

/-!
# Splice, post part (C12X, S16 `hwin` far branch; O-C12X-S16J G4)

`RetainedCoreHistory.exists_splicePost_C12X` (= G4e-post): after the surgery, for standard times
`τ ∈ [0, T_t]`, the survivor pull-in `Ψ` of the deep neck of a far-early window datum reads the
rescaled flow `q · P.gflow (t_j + τ / q)` as a metric `η`-close in `C^r` to the shrinking cylinder
`cylFam τ` (itself as reference) on the band `|z - z_u| ≤ L` around the marked buffer point `u`;
and the scalar curvature at `(y, t)` is `η`-close to that of the cylinder at `T_t`.

Constants as in the Birth lane: the window comparison
`exists_standard_comparison_of_cap_window_trace` (window radius `Dw + L + 3`, order `max r 2`,
accuracy from `exists_far_window_cylinder_close_C12X`), the window model
`window_model_metric_eq_C12X`, then `splicePost_band_points_C12X` and
`splicePost_band_transfer_C12X` (G3) with `metric_post`.
-/

set_option autoImplicit false

noncomputable section

open Set Function TopologicalSpace
open scoped NNReal Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

namespace RetainedCoreHistory

/-- **Splice, post part (G4e-post).**  Far-early window datum `d` (`D₀ + 1 ≤ ‖d.x‖`, standard
time `T_t = q (t - t_j) ≤ θ₀`), deep neck `D`, survivor pull-in `Sv`, package `P`, and the
survivor output `u, ys`: the scalar curvature at `(y, t)` is `η`-close to that of `cylFam T_t`,
and for every `τ ∈ [0, T_t]` and buffer point `w` with `|z_w - z_u| ≤ L`, `w ∈ Sv.U` and the
rescaled package metric pulled back by `Ψ` is `η`-close in `C^r` to `cylFam τ` (own reference). -/
theorem exists_splicePost_C12X {θ₀ : ℝ} (hθ₀ : θ₀ < 1) (r : ℕ) {η : ℝ}
    (hη : 0 < η) {L : ℝ} (hL : 0 ≤ L) :
    ∃ D₀ : ℝ, 0 < D₀ ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (Ctime : ℝ≥0) (Dw θw : ℝ), 0 < Dw → θw < 1 →
    ∃ (Rw : ℝ) (mw : ℕ), Dw + 1 < Rw ∧
    ∀ qcan : ℝ, 0 < qcan →
    ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Rw ≤ p₀.modelRadius → mw ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ H : RetainedCoreHistory.{u}, Nonempty (InitialIdentification P₀ g₀ H.toHistory) →
      p₀.recenterConstant * δbound ≤ 1 / 2 →
    ∀ (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      (∀ i b, ((records i).static b).witness.HasRadialCoordinates) →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative Ctime qcan k → Gk.DerivativeBoundBefore Ctime qcan s →
    ∀ (y : (H.stage k).Carrier) (t : ℝ), t ∈ Ioo (H.time k) s →
    ∀ d : H.WindowDatum_C12X records k y t Dw θw, D₀ + 1 ≤ ‖d.x.val‖ →
      t - H.time d.j.succ ≤ θ₀ * d.scale⁻¹ →
    ∀ {θ : ℝ} (D : IncomingBackwardNeckDeep_C12X H.toHistory d.j ((records d.j).neck d.b.1.1)
        ((records d.j).nominalRadius ⟨d.b.1.1⟩) θ)
      (Sv : H.toHistory.SpliceSurvivor_C12X D k d.hl)
      (P : H.toHistory.SurvivorNeckPackage_C12X k Gk Sv.first Sv.hle) (u : Sv.U)
      (ys : neckBuffer ((records d.j).static d.b).delta)
      (hys : 0 < ys.1.2 ∧ ys.1.2 < (((records d.j).static d.b).delta)⁻¹),
      ((records d.j).static d.b).witness.window d.x =
        ((records d.j).static d.b).witness.retained ⟨ys.1, hys.1.le, hys.2⟩ →
      u.1 = ⟨(ys.1.1, (if d.b.1.2 then 1 else -1) * (1 + ys.1.2)),
        (records d.j).recenter_in_buffer d.b ys⟩ →
      |(d.scale)⁻¹ * Gk.flow.scalar t y - (1 - d.scale * (t - H.time d.j.succ))⁻¹| ≤ η ∧
      ∀ τ ∈ Icc 0 (d.scale * (t - H.time d.j.succ)),
      ∀ w : neckBuffer ((records d.j).delta d.b.1.1), |w.1.2 - u.1.1.2| ≤ L →
        ∃ hw : w ∈ Sv.U, ∀ q ≤ r,
          metricDerivNorm q (localPullMetric (scaleMetric d.scale d.scale_pos
              (P.gflow (H.time d.j.succ + τ / d.scale))) Sv.Ψ Sv.Ψ_diffeo)
            (((cylFam_C12X τ).restrictOpen
              (neckBuffer ((records d.j).delta d.b.1.1))).restrictOpen Sv.U)
            (((cylFam_C12X τ).restrictOpen
              (neckBuffer ((records d.j).delta d.b.1.1))).restrictOpen Sv.U)
            ⟨w, hw⟩ < η := by
  set Θ := max θ₀ 0 with hΘdef
  have hΘ0 : 0 ≤ Θ := le_max_right _ _
  have hΘ1 : Θ < 1 := max_lt hθ₀ one_pos
  obtain ⟨εc, hεc, D₁, hD₁, hcore⟩ :=
    exists_far_window_cylinder_close_C12X hΘ0 hΘ1 r (half_pos hη) hL
  have hTE := StandardCap.transitionEnd_pos
  have hLcap : standardCapL = StandardCap.transitionEnd := standardCapL_eq_transitionEnd
  refine ⟨max D₁ (standardCapL + L + 2), lt_of_lt_of_le hD₁ (le_max_left _ _), ?_⟩
  intro P₀ g₀ Ctime Dw θw hDw hθw
  obtain ⟨a₀, ha₀, hHI⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P₀ g₀
  set Θc := max θw (1 / 2) with hΘcdef
  have hΘc1 : Θc < 1 := max_lt hθw (by norm_num)
  have hΘc0 : 0 < Θc := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  obtain ⟨Pb, Creset, Cb, -, -, hCb, hbridge⟩ :=
    exists_standard_comparison_of_cap_window_trace.{u} Θc Ctime hΘc0 hΘc1
  have hDc : 0 < Dw + L + 3 := by linarith
  obtain ⟨R, hR, m, -, ζ, δ₀, hζ, -, hδ₀, hbr⟩ :=
    hbridge (Dw + L + 3) εc 1 hDc hεc one_pos (max r 2)
  refine ⟨R, m, by linarith, fun qcan hqcan => ?_⟩
  set ρmax := min (Real.sqrt (Cb / (4 * qcan))) (Real.sqrt (a₀ / 2)) with hρdef
  have hρmax : 0 < ρmax := lt_min (Real.sqrt_pos.mpr (by positivity))
    (Real.sqrt_pos.mpr (by positivity))
  have hρ₁ : ρmax ^ 2 ≤ Cb / (4 * qcan) := by
    have h := pow_le_pow_left₀ hρmax.le (min_le_left _ _) 2
    rwa [Real.sq_sqrt (by positivity)] at h
  have hρ₂ : ρmax ^ 2 ≤ a₀ / 2 := by
    have h := pow_le_pow_left₀ hρmax.le (min_le_right _ _) 2
    rwa [Real.sq_sqrt (by positivity)] at h
  refine ⟨δ₀, ρmax, ζ, hδ₀, hρmax, hζ, ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδb hρb H hId hΛδ p records hrec hradial k s Gk hGk
    hderiv hderG y t ht d hfar hT θ D Sv P u ys hys hwin hu
  obtain ⟨hkt, hts⟩ := ht
  have hcur := Gk.derivativeBoundBefore_mono hts.le hderG
  obtain ⟨hHI1, hHI2⟩ := hHI H.toHistory hId.some
  have hq : 0 < d.scale := d.scale_pos
  obtain ⟨hbirth, haq⟩ := hrec.birth_scale_bounds hΛδ d.j d.b hqcan hCb ha₀ hρb hρ₁ hρ₂
  have hbirth1 : qcan ≤ Cb * d.scale := by
    change qcan ≤ Cb * ((records d.j).static d.b).neck.scale
    linarith
  have hθΘ : θw ≤ Θc := le_max_left _ _
  have hxD' : ‖d.x.val‖ < Dw + L + 3 + 1 := by linarith [d.hnorm]
  obtain ⟨G, L', hG, -, hL', -, -, -, -, -, -, hDD, z, hzx, hy, Ξ, -, hΞwin, hΞmark, hΞ, gflow,
      S, hS1, hS2, -, -, hS5, -, -, Q, -, hclose⟩ :=
    hbr H p₀ δbound ρbound records hrec hδb hrad hord hacc qcan a₀ θw hqcan hθΘ hHI1 hHI2 k s
      Gk hGk hderiv t hkt hts hcur d.j d.hl y d.A d.b d.x d.hx d.htime hxD' hbirth1 haq
  set q := d.scale with hqdef
  have hjk : H.time d.j.succ ≤ H.time k := H.time_strictMono.monotone d.hl
  set T := q * (t - H.time d.j.succ) with hTdef
  have hT0 : 0 ≤ T := mul_nonneg hq.le (by linarith)
  have hTθ : T ≤ θ₀ := by
    have h1 := mul_le_mul_of_nonneg_left hT hq.le
    rwa [mul_comm θ₀, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] at h1
  have hTΘ : T ≤ Θ := hTθ.trans (le_max_left _ _)
  have hTmem : T ∈ Icc 0 T := ⟨hT0, le_rfl⟩
  have htT : H.time d.j.succ + T / q = t := by
    rw [hTdef, mul_div_cancel_left₀ _ hq.ne']
    ring
  have hxD₁ : D₁ ≤ ‖d.x.val‖ := by linarith [le_max_left D₁ (standardCapL + L + 2)]
  have hxbig : standardCapL + L + 2 + 1 ≤ ‖d.x.val‖ := by
    linarith [le_max_right D₁ (standardCapL + L + 2)]
  have hfit : ‖d.x.val‖ + L + 1 ≤ Dw + L + 3 + 1 := by linarith [d.hnorm]
  have hΞ' := H.isLocalDiffeomorph_incoming_val_C12X d.hl hΞ
  obtain ⟨P'⟩ := H.toHistory.nonempty_survivorNeckPackage_C12X Gk d.j.succ d.hl hGk
  have hSw : ∀ τ ∈ Icc 0 T, S.base.metric τ = localPullMetric (scaleMetric q hq
      (P'.gflow (H.time d.j.succ + τ / q))) (fun w => (Ξ w).val) hΞ' := fun τ hτ => by
    rw [hS5 τ]
    exact H.window_model_metric_eq_C12X Gk d.hl P' hts hG hL' hΞ hS1 hS2 hq hτ.1 hτ.2
  -- the scalar clause
  have hscal : |q⁻¹ * Gk.flow.scalar t y - (1 - T)⁻¹| ≤ η := by
    obtain ⟨f, hf, -, hcl⟩ := hcore Q T ⟨hT0, hTΘ⟩ d.x.val hxD₁ (Dw + L + 3) hfit
    have hxw : d.x.val ∈ standardCapWindow (Dw + L + 3) := hxD'
    have h2 := (hcl (S.base.metric T) fun i hi v => (hclose T hTmem).1 i hi v).2 hxw
    have hz : (⟨d.x.val, hxw⟩ : standardCapWindow (Dw + L + 3)) = z := Subtype.ext hzx.symm
    have hST := H.capWindow_flow_metric_eq Gk d.hl hΞ hq hG hL' hS2 hS5 T hTmem
      (by rw [htT]; linarith)
    rw [htT] at hST
    have hyz : (Ξ z).val.val = y := congrArg Subtype.val hΞmark
    have hRS : metricScalarAt (S.base.metric T) z = q⁻¹ * Gk.flow.scalar t y := by
      rw [hST, metricScalarAt_localPullMetric_scaleMetric, hyz]
      rfl
    rw [hz, hRS] at h2
    linarith
  refine ⟨hscal, fun τ hτ w hw => ?_⟩
  have hσ2 : (if d.b.1.2 then (1 : ℝ) else -1) ^ 2 = 1 := by split_ifs <;> norm_num
  have hσabs : |(if d.b.1.2 then (1 : ℝ) else -1)| = 1 := by split_ifs <;> norm_num
  have hmod : ‖d.x.val‖ + L + 1 ≤ p.modelRadius + 1 := by
    linarith only [hR, hrad, d.hnorm, hrec.2.1]
  have hpts := splicePost_band_points_C12X d hL (hrec.2.2.2.2.2.1 d.j d.b) (hradial d.j d.b) hxbig
    hfit hmod Ξ
    _ hΞwin Sv u ys hys hwin hu
  have hwb : |w.1.2 - u.1.1.2| < L + 1 := by linarith only [hw]
  have hwU := (hpts w hwb).snd.fst
  refine ⟨hwU, fun q' hq' => ?_⟩
  have hτΘ : τ ∈ Icc 0 Θ := ⟨hτ.1, hτ.2.trans hTΘ⟩
  have hτ1 : τ < 1 := hτΘ.2.trans_lt hΘ1
  obtain ⟨f, hf, hform, hcl⟩ := hcore Q τ hτΘ d.x.val hxD₁ (Dw + L + 3) hfit
  have hcl1 := (hcl (S.base.metric τ) fun i hi v => (hclose τ hτ).1 i hi v).1
  rw [hSw τ hτ] at hcl1
  have hτ' : H.time d.j.succ + τ / q ∈ Ico (H.time d.j.succ) s := by
    have h0 : 0 ≤ τ / q := div_nonneg hτ.1 hq.le
    have h1 : τ / q ≤ t - H.time d.j.succ := by
      rw [div_le_iff₀ hq]
      have h2 : τ ≤ q * (t - H.time d.j.succ) := hτ.2
      linarith only [h2]
    exact ⟨by linarith only [h0], by linarith only [h1, hts]⟩
  have key := splicePost_band_transfer_C12X r hq hτ1 hσ2 hσabs
    (StandardCap.pointedInitialRotation d.x.val)
    Sv.Ψ Sv.Ψ_diffeo _ (H.toHistory.backwardSurvivorDomain_inclusion_isLocalDiffeomorph
      (hfirst := Sv.hle) (hnext := d.hl) (Sv.first_le.trans d.j.castSucc_lt_succ.le))
    (fun v => (Ξ v).val) hΞ' _ _ (Sv.metric_post P P' hτ') f hf hform hcl1
    (fun w' hw' => ⟨(hpts w'.1 hw').fst, Subtype.ext (hpts w'.1 hw').snd.snd⟩)
    ⟨w, hwU⟩ hwb q' hq'
  exact lt_of_le_of_lt key (by linarith only [hη])

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
