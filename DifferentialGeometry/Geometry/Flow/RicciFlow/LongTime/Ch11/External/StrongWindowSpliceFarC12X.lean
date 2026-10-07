import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSpliceTwoFrameC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSurviveMetricC12X
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullbackScaling

/-!
# Splice at a far-early window point (C12X, S16 `hwin` far branch; O-C12X-S16H G4e4)

* `NormalizedNeck.scalar_normalized_eq_C12X`: the scalar curvature of the normalized neck metric
  at a chart point is `scale⁻¹ · R(chart x)`.
* `IncomingBackwardNeckDeep_C12X.abs_scalar_ratio_sub_le_C12X`: for a deep backward neck of
  accuracy `η` and any chart point `x` of the closed test region,
  `|R(chart x) · r² - 1| ≤ 3 ((720 η + η / 2) / (1 - η))` (scalar control at `v = 0`); applied
  at the recentred static center this gives `|q r² - 1|` small, independently of the
  recentring constant.
* `RetainedCoreHistory.far_full_of_splice_C12X` (**point lemma**): at a far-early window point
  `(y, t)` (`q (t - t_i) ≤ θ₀ < 1`), the Survive data `(Sv, P, u, ys)`, the deep neck of depth
  `θ > 1`, and the post-surgery `C^p` closeness on the band `|z - z_u| ≤ 2 (ε⁻¹ + 1)` with the
  scalar clause give `HistoryStrongNeckFull_C12X k Gk ε y t` (via
  `exists_strongNeck_of_two_frames_C12X`, pre-frame from `SpliceSurvivor_C12X.metric_pre`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private local instance s16h_sphereDim7 : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) :=
  ⟨by simp [ThreeSpace]⟩

universe u

private local instance s16h_terminalSecondCountable (H : ObservedHistory.{u})
    (i : Fin H.eventCount) :
    SecondCountableTopology (H.event i).incoming.terminalRegularOpen := by
  let : SecondCountableTopology (H.stage i.castSucc).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (H.stage i.castSucc).Carrier
  infer_instance

private local instance s16h_terminalLocallyCompact (H : ObservedHistory.{u})
    (i : Fin H.eventCount) :
    LocallyCompactSpace (H.event i).incoming.terminalRegularOpen :=
  ChartedSpace.locallyCompactSpace ThreeSpace (H.event i).incoming.terminalRegularOpen

/-- The neck chart is a local diffeomorphism. -/
theorem NormalizedNeck.chart_isLocalDiffeomorph_C12X {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ} (N : NormalizedNeck h δ k) :
    IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ N.chart :=
  DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv N.chart
    N.chart_smooth.contMDiff
    (fun x => immersionAt_mfderiv_injective (N.chart_smooth.isImmersion.isImmersionAt x))
    (by simp [Module.finrank_prod, ThreeSpace])

/-- The normalized neck metric is the rescaled pullback of the ambient metric. -/
theorem NormalizedNeck.normalizedMetric_eq_C12X {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M]
    {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ} (N : NormalizedNeck h δ k) :
    N.normalizedMetric = localPullMetric (scaleMetric N.scale N.scale_pos h) N.chart
      N.chart_isLocalDiffeomorph_C12X := by
  apply SmoothRiemannianMetric.ext_inner
  intro x V W
  rw [N.normalized_inner, localPullMetric_inner, scaleMetric_inner]

/-- Scalar curvature of the normalized neck metric at a chart point. -/
theorem NormalizedNeck.scalar_normalized_eq_C12X {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ} (N : NormalizedNeck h δ k)
    (x : neckBuffer δ) :
    metricScalarAt N.normalizedMetric x = N.scale⁻¹ * metricScalarAt h (N.chart x) := by
  rw [N.normalizedMetric_eq_C12X, metricScalarAt_localPullMetric_scaleMetric]

/-- **Scalar ratio on a deep backward neck.**  At every chart point `x` of the closed test region,
`R(chart x) · r²` is within `3 ((720 δ + δ / 2) / (1 - δ))` of `1` (`δ ≤ 1/2`). -/
theorem IncomingBackwardNeckDeep_C12X.abs_scalar_ratio_sub_le_C12X {H : ObservedHistory.{u}}
    {i : Fin H.eventCount} {δ : ℝ} {k : ℕ}
    {neck : NormalizedNeck (H.event i).terminal.metric δ k} {r θ : ℝ}
    (D : IncomingBackwardNeckDeep_C12X H i neck r θ) (hk : 2 ≤ k) (hδ : δ ≤ 1 / 2)
    (hscale : neck.scale = (r ^ 2)⁻¹) (x : neckBuffer δ) (hx : x ∈ neckClosedTest δ) :
    |metricScalarAt (H.event i).terminal.metric (neck.chart x) * r ^ 2 - 1| ≤
      3 * ((240 * 3 * δ + δ * (2 * (1 - 0))⁻¹) / (1 - δ)) := by
  obtain ⟨η, hηδ, hb⟩ := D.derivNorm_le_C12X
  have hθ : -θ ≤ 0 := by linarith [D.one_le_depth]
  have hsmall : ∀ m : ℕ, m ≤ 2 → metricDerivNorm m (D.metric 0)
      ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) 0).restrictOpen (neckBuffer δ))
      ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) 0).restrictOpen (neckBuffer δ))
        x ≤ η :=
    fun m hm => hb 0 ⟨hθ, le_rfl⟩ x hx m (hm.trans hk)
  have hη0 : 0 ≤ η := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have h := abs_scalar_sub_le_of_cylFam_close_C12X (v := 0) (by norm_num) (neckBuffer δ)
    (D.metric 0) x (by linarith) hsmall
  rw [D.terminal_metric, neck.scalar_normalized_eq_C12X, hscale, inv_inv] at h
  have hr : metricScalarAt (H.event i).terminal.metric (neck.chart x) * r ^ 2 - 1 =
      r ^ 2 * metricScalarAt (H.event i).terminal.metric (neck.chart x) - (1 - 0)⁻¹ := by
    norm_num [mul_comm]
  rw [hr]
  refine h.trans ?_
  have hd1 : 0 < 1 - δ := by linarith
  have hη1 : 0 < 1 - η := by linarith
  have hmono : (240 * 3 * η + η * (2 * (1 - 0))⁻¹) / (1 - η) ≤
      (240 * 3 * δ + δ * (2 * (1 - 0))⁻¹) / (1 - δ) := by
    rw [div_le_div_iff₀ hη1 hd1]
    norm_num
    nlinarith
  linarith

/-- `|q r² - 1|` is small: `q` is the scalar curvature at the recentred static center, which is
the neck chart point at axial position `±1`. -/
theorem GeometricCutoffRecord.abs_static_scale_mul_sub_le_C12X {H : ObservedHistory.{u}}
    {i : Fin H.eventCount} {p : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) {θ : ℝ}
    (D : IncomingBackwardNeckDeep_C12X H i (R.neck b.1.1) (R.nominalRadius ⟨b.1.1⟩) θ)
    (hk : 2 ≤ R.order b.1.1) (hδ : R.delta b.1.1 ≤ 1 / 2) :
    |(R.static b).neck.scale * (R.nominalRadius ⟨b.1.1⟩) ^ 2 - 1| ≤
      3 * ((240 * 3 * R.delta b.1.1 + R.delta b.1.1 * (2 * (1 - 0))⁻¹) /
        (1 - R.delta b.1.1)) := by
  set m := (R.static b).neck.sphereMark
  have hδs : 0 < (R.static b).delta := (R.static b).neck.delta_pos
  let x0 : neckBuffer (R.static b).delta := ⟨(m, 0), by
    have := inv_pos.mpr hδs
    constructor <;> linarith⟩
  have hmark : (R.static b).neck.chart x0 = (R.static b).neck.center := (R.static b).neck.marked
  have hx1 := R.recenter_in_buffer b x0
  have hchart := R.recenter_chart b x0 hx1
  let x1 : neckBuffer (R.delta b.1.1) :=
    ⟨(x0.1.1, (if b.1.2 then 1 else -1) * (1 + x0.1.2)), hx1⟩
  have hδ0 : 0 < R.delta b.1.1 := R.delta_pos b.1.1
  have hx1c : x1 ∈ neckClosedTest (R.delta b.1.1) := by
    have hinv : 1 ≤ (R.delta b.1.1)⁻¹ := one_le_inv₀ hδ0 |>.mpr (by linarith)
    change -(R.delta b.1.1)⁻¹ ≤ (if b.1.2 then 1 else -1) * (1 + (0 : ℝ)) ∧
      (if b.1.2 then 1 else -1) * (1 + (0 : ℝ)) ≤ (R.delta b.1.1)⁻¹
    split_ifs <;> constructor <;> linarith
  have h := D.abs_scalar_ratio_sub_le_C12X hk hδ (R.scale_eq b.1.1) x1 hx1c
  have hq : (R.static b).neck.scale =
      metricScalarAt (H.event i).terminal.metric ((R.neck b.1.1).chart x1) := by
    rw [(R.static b).neck.scale_scalar, ← hmark, hchart]
  rw [hq]
  exact h

/-- The scalar-control error is `≤ η` once `δ ≤ η / 5000`, `η ≤ 1 / 8`. -/
private theorem s16h_err_le {η δ : ℝ} (hη8 : η ≤ 1 / 8) (hδ : 0 < δ) (hδη : δ ≤ η / 5000) :
    3 * ((240 * 3 * δ + δ * (2 * (1 - 0))⁻¹) / (1 - δ)) ≤ η := by
  have h1 : (0 : ℝ) < 1 - δ := by linarith
  have h2 : (240 * 3 * δ + δ * (2 * (1 - 0))⁻¹) / (1 - δ) ≤ η / 3 := by
    rw [div_le_iff₀ h1]
    have h3 : η * δ ≤ η * (1 / 2) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    norm_num
    nlinarith
  linarith

/-- Window arithmetic: from `|q r² - 1| ≤ η`, `|q⁻¹ R - (1 - τ)⁻¹| ≤ η` (`τ = q (t - t_i)`)
and the survivor start `t_f ≤ t_i - θ r²`, the window `[t - (1 + μ) R⁻¹, t]` fits. -/
private theorem s16h_window {θ η ϑ θ₀ ti tf t r q R : ℝ} (hθ : 1 < θ)
    (hϑθ : (θ + 1) / 2 ≤ θ * (1 - ϑ) ^ 2) (hϑ1 : ϑ ≤ 1) (hηϑ : η ≤ ϑ) (hη8 : η ≤ 1 / 8)
    (hq : 0 < q) (hθ₀ : θ₀ < 1) (hτ : q * (t - ti) ∈ Icc 0 θ₀) (htf : tf ≤ ti - θ * r ^ 2)
    (hti : ti ≤ t) (hqr : |q * r ^ 2 - 1| ≤ η)
    (hsc : |q⁻¹ * R - (1 - q * (t - ti))⁻¹| ≤ η) :
    0 < R ∧ ti - θ * r ^ 2 ≤ t - (1 + (θ - 1) / 2) * R⁻¹ ∧ ti - θ * r ^ 2 ≤ t - R⁻¹ ∧
      tf ≤ t - (1 + (θ - 1) / 2) * R⁻¹ ∧ tf ≤ t - R⁻¹ := by
  have h1τ : 0 < 1 - q * (t - ti) := by linarith [hτ.2]
  have hinv : 1 ≤ (1 - q * (t - ti))⁻¹ := one_le_inv₀ h1τ |>.mpr (by linarith [hτ.1])
  have hκ : 1 - η ≤ q⁻¹ * R := by linarith [(abs_le.mp hsc).1]
  have hRe : R = q * (q⁻¹ * R) := by field_simp
  have hR : 0 < R := by rw [hRe]; exact mul_pos hq (by linarith)
  have hqr2 : 1 - η ≤ q * r ^ 2 := by linarith [(abs_le.mp hqr).1]
  have hprod : (1 - η) * (1 - η) ≤ (q * r ^ 2) * (q⁻¹ * R) :=
    mul_le_mul hqr2 hκ (by linarith) (by linarith)
  have heq : (q * r ^ 2) * (q⁻¹ * R) = r ^ 2 * R := by field_simp
  have hϑ2 : (1 - ϑ) ^ 2 ≤ (1 - η) * (1 - η) := by
    rw [sq]; exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have hmain : (θ + 1) / 2 ≤ θ * (r ^ 2 * R) :=
    hϑθ.trans (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
  have hw : (1 + (θ - 1) / 2) * R⁻¹ ≤ θ * r ^ 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hR]; nlinarith
  have hRi : R⁻¹ ≤ (1 + (θ - 1) / 2) * R⁻¹ :=
    le_mul_of_one_le_left (inv_pos.mpr hR).le (by linarith)
  refine ⟨hR, by linarith, by linarith, by linarith, by linarith⟩

/-- **Splice at a far-early window point.**  Given the Survive data `(Sv, P, u, ys)` of a window
datum (`exists_spliceSurvivor_C12X`) and the post-surgery closeness + scalar clause of
`exists_splicePost_C12X` (with band `2 (ε⁻¹ + 1)`), a deep backward neck of depth `θ > 1` gives
the full history neck at `(y, t)`. -/
theorem RetainedCoreHistory.far_full_of_splice_C12X {ε : ℝ} (hε : 0 < ε) (hε11 : ε < 1 / 11)
    {θ : ℝ} (hθ : 1 < θ) {θ₀ : ℝ} (hθ₀ : θ₀ < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ p : ℕ, ∃ δ₁ : ℝ, 0 < δ₁ ∧
    ∀ {H : RetainedCoreHistory.{u}} {p₀ pp : CutoffParameters} {δbound ρbound : ℝ}
      {records : ∀ i, GeometricCutoffRecord H.toHistory i pp},
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records → δbound ≤ δ₁ →
      p ≤ p₀.modelOrder →
    ∀ {k : Fin (H.eventCount + 1)} {s : ℝ} (Gk : (H.stage k).IncomingSlab (H.time k) s)
      {y : (H.stage k).Carrier} {t Dw θw : ℝ}, t ∈ Ioo (H.time k) s →
    ∀ (d : H.WindowDatum_C12X records k y t Dw θw), t - H.time d.j.succ ≤ θ₀ * d.scale⁻¹ →
    ∀ (D : IncomingBackwardNeckDeep_C12X H.toHistory d.j ((records d.j).neck d.b.1.1)
        ((records d.j).nominalRadius ⟨d.b.1.1⟩) θ)
      (Sv : H.toHistory.SpliceSurvivor_C12X D k d.hl)
      (P : H.toHistory.SurvivorNeckPackage_C12X k Gk Sv.first Sv.hle) (u : Sv.U)
      (ys : neckBuffer ((records d.j).static d.b).delta),
      0 < ys.1.2 ∧ ys.1.2 < (((records d.j).static d.b).delta)⁻¹ →
      (Sv.Ψ u).val = y →
      u.1 = ⟨(ys.1.1, (if d.b.1.2 then 1 else -1) * (1 + ys.1.2)),
        (records d.j).recenter_in_buffer d.b ys⟩ →
      |(d.scale)⁻¹ * Gk.flow.scalar t y - (1 - d.scale * (t - H.time d.j.succ))⁻¹| ≤ η →
      (∀ τ ∈ Icc 0 (d.scale * (t - H.time d.j.succ)),
        ∀ w : neckBuffer ((records d.j).delta d.b.1.1), |w.1.2 - u.1.1.2| ≤ 2 * (ε⁻¹ + 1) →
        ∃ hw : w ∈ Sv.U, ∀ q ≤ p,
          metricDerivNorm q (localPullMetric (scaleMetric d.scale d.scale_pos
              (P.gflow (H.time d.j.succ + τ / d.scale))) Sv.Ψ Sv.Ψ_diffeo)
            (((cylFam_C12X τ).restrictOpen (neckBuffer ((records d.j).delta d.b.1.1))).restrictOpen
              Sv.U)
            (((cylFam_C12X τ).restrictOpen (neckBuffer ((records d.j).delta d.b.1.1))).restrictOpen
              Sv.U) ⟨w, hw⟩ < η) →
      H.toHistory.HistoryStrongNeckFull_C12X k Gk ε y t := by
  have hμ : 0 < (θ - 1) / 2 := by linarith
  obtain ⟨η₂, hη₂, p₂, hTF⟩ := exists_strongNeck_of_two_frames_C12X.{u} hε hε11 hμ hθ₀
  have hθ0 : 0 < θ := by linarith
  set ϑ : ℝ := (θ - 1) / (4 * θ) with hϑdef
  have hϑ0 : 0 < ϑ := div_pos (by linarith) (by linarith)
  have hϑθ : (θ + 1) / 2 ≤ θ * (1 - ϑ) ^ 2 := by
    have h1 : 1 - 2 * ϑ ≤ (1 - ϑ) ^ 2 := by nlinarith [sq_nonneg ϑ]
    have h2 : θ * (1 - 2 * ϑ) = (θ + 1) / 2 := by rw [hϑdef]; field_simp; ring
    nlinarith
  set η : ℝ := min η₂ (min ϑ (1 / 8)) with hηdef
  have hη : 0 < η := lt_min hη₂ (lt_min hϑ0 (by norm_num))
  have hηη₂ : η ≤ η₂ := min_le_left _ _
  have hηϑ : η ≤ ϑ := (min_le_right _ _).trans (min_le_left _ _)
  have hη8 : η ≤ 1 / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hε0 : 0 < ε⁻¹ := inv_pos.mpr hε
  set δ₁ : ℝ := min (η / 5000) (1 / (4 * (3 + 2 * ε⁻¹))) with hδ₁def
  have hδ₁ : 0 < δ₁ := lt_min (by positivity) (by positivity)
  refine ⟨η, hη, max p₂ 2, δ₁, hδ₁, ?_⟩
  intro H p₀ pp δbound ρbound records hrec hδb hp k s Gk y t Dw θw ht d hT D Sv P u ys hys hyu
    hu hscal hpost
  have : SigmaCompactSpace (H.toHistory.backwardSurvivorDomain Sv.first k Sv.hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen
      ThreeModel (H.toHistory.backwardSurvivorDomain Sv.first k Sv.hle).isOpen)
  obtain ⟨-, -, hord, -, -, -, hδfam, -⟩ := hrec
  have hδα0 : 0 < (records d.j).delta d.b.1.1 := (records d.j).delta_pos _
  have hδα1 : (records d.j).delta d.b.1.1 ≤ δ₁ :=
    ((records d.j).delta_le _).trans ((hδfam d.j).trans hδb)
  have hδαη : (records d.j).delta d.b.1.1 ≤ η / 5000 := hδα1.trans (min_le_left _ _)
  have hδαinv : 4 * (3 + 2 * ε⁻¹) ≤ ((records d.j).delta d.b.1.1)⁻¹ := by
    rw [le_inv_comm₀ (by positivity) hδα0]
    simpa [one_div] using hδα1.trans (min_le_right _ _)
  have hk2 : max p₂ 2 + 6 ≤ (records d.j).order d.b.1.1 := by
    have h1 := (records d.j).order_lower d.b.1.1
    have h2 : max p₂ 2 ≤ pp.modelOrder := hord ▸ hp
    omega
  have hqr : |d.scale * ((records d.j).nominalRadius ⟨d.b.1.1⟩) ^ 2 - 1| ≤ η :=
    ((records d.j).abs_static_scale_mul_sub_le_C12X d.b D (by omega) (by linarith)).trans
      (s16h_err_le hη8 hδα0 hδαη)
  have hq0 : 0 < d.scale := d.scale_pos
  have hτt : d.scale * (t - H.time d.j.succ) ∈ Icc 0 θ₀ := by
    have hjk : H.time d.j.succ ≤ H.time k := H.time_strictMono.monotone d.hl
    refine ⟨mul_nonneg hq0.le (by linarith [ht.1]), ?_⟩
    have h1 := mul_le_mul_of_nonneg_left hT hq0.le
    rwa [mul_comm θ₀, ← mul_assoc, mul_inv_cancel₀ hq0.ne', one_mul] at h1
  have htt : H.time d.j.succ + d.scale * (t - H.time d.j.succ) / d.scale = t := by
    field_simp; ring
  have hRS : P.flow.scalar t (Sv.Ψ u) = Gk.flow.scalar t y := by
    rw [P.scalar_eq ⟨ht.1.le, ht.2⟩, hyu]
  have hϑ1 : ϑ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  obtain ⟨hR, hw1, hw2, hw3, hw4⟩ := s16h_window (tf := H.time Sv.first) hθ hϑθ
    hϑ1 hηϑ hη8 hq0 hθ₀ hτt Sv.time_first
    (H.time_strictMono.monotone d.hl |>.trans ht.1.le) hqr hscal
  -- band geometry
  have huc : |((u : neckBuffer ((records d.j).delta d.b.1.1)) : NeckCylinder).2| ≤
      1 + ((records d.j).delta d.b.1.1)⁻¹ / 4 := by
    have hΛ : 4 ≤ pp.recenterConstant := pp.recenterConstant_ge_four
    have hys2 : ys.1.2 < ((records d.j).delta d.b.1.1)⁻¹ / 4 := by
      have h1 : ys.1.2 < (pp.recenterConstant * (records d.j).delta d.b.1.1)⁻¹ :=
        lt_of_lt_of_eq hys.2 (by rw [(records d.j).recenter_delta d.b])
      rw [mul_inv] at h1
      have h2 : pp.recenterConstant⁻¹ ≤ 1 / 4 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; norm_num; linarith
      nlinarith [inv_pos.mpr hδα0]
    rw [hu]
    change |(if d.b.1.2 then 1 else -1) * (1 + ys.1.2)| ≤ _
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith [hys.1]
  have hbandc : ∀ x : NeckCylinder,
      |x.2 - ((u : neckBuffer ((records d.j).delta d.b.1.1)) : NeckCylinder).2| ≤
        2 * (ε⁻¹ + 1) → |x.2| ≤ ((records d.j).delta d.b.1.1)⁻¹ := by
    intro x hx
    have h1 := abs_sub_abs_le_abs_sub x.2
      ((u : neckBuffer ((records d.j).delta d.b.1.1)) : NeckCylinder).2
    linarith
  obtain ⟨ηD, hηD, hDcl⟩ := D.derivNorm_le_C12X
  refine (hTF P.flow P.sol Sv.U Sv.Ψ Sv.Ψ_diffeo Sv.Ψ_injective (H.time d.j.succ)
    ((records d.j).nominalRadius ⟨d.b.1.1⟩) d.scale (d.scale * (t - H.time d.j.succ)) θ
    D.radius_pos hq0 u hτt (hqr.trans hηη₂) ?band ?pre ?post (by rw [htt, hRS]; exact hR)
    (by rw [htt, hRS]; exact hscal.trans hηη₂) ?car ?reg (by rw [htt, hRS]; exact hw2)).elim
    fun nk => ?fin
  case fin => exact P.full_of_strongNeck (Sv.Ψ u) hyu ht.1.le hw4 (nk.castTime htt)
  case band =>
    intro x hx
    have hxb : x ∈ neckBuffer ((records d.j).delta d.b.1.1) := by
      have h := abs_le.mp (hbandc x hx)
      constructor <;> linarith
    obtain ⟨hw, -⟩ := hpost 0 ⟨le_rfl, hτt.1⟩ ⟨x, hxb⟩ hx
    exact ⟨hxb, hw⟩
  case pre =>
    intro v hv m hm w hw
    have hmp := Sv.metric_pre ((records d.j).scale_eq d.b.1.1) P hv
    change metricDerivNorm m (localPullMetric (scaleMetric _ _ (P.gflow _)) Sv.Ψ Sv.Ψ_diffeo)
      _ _ w ≤ _
    rw [hmp, HGI.metricDerivNorm_restrictOpen]
    have hwc : (w : neckBuffer ((records d.j).delta d.b.1.1)) ∈
        neckClosedTest ((records d.j).delta d.b.1.1) := abs_le.mp (hbandc _ hw)
    have := hDcl v hv _ hwc m (by omega)
    have hηDη : ηD ≤ η₂ := by linarith
    exact this.trans hηDη
  case post =>
    intro τ hτ m hm w hw
    obtain ⟨hw', h⟩ := hpost τ hτ w.1 hw
    exact (h m (by omega)).le.trans hηη₂
  case car =>
    rw [htt, hRS]
    intro σ hσ
    exact ⟨by linarith [hσ.1], lt_of_le_of_lt hσ.2 ht.2⟩
  case reg =>
    rw [htt, hRS]
    intro σ hσ
    exact ⟨by linarith [hσ.1], lt_trans hσ.2 ht.2⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
