import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionOrCapWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.CapWindowStdCompLate_P6LL

/-!
# cap window 标量下界 / age bound 的 late-records + hybrid 形（O-CH11-P6LATE G1，后缀 `_P6LL`）

`TracedRegionOrCapWindow:31`（`exists_scalar_lower_bound_of_cap_window_trace`）与 `:111`
（`exists_capWindow_age_bound_of_scalar_le_along_trace`）的局部化副本：records 改 late 形
（`∀ i, T₀ ≤ H.time i.succ → …`），cap event `j` 带 `hj : T₀ ≤ H.time j.succ`；`p₀` 去掉（参数界直接在
`p` 上）；底座 standard comparison 换成 `exists_standard_comparison_of_cap_window_trace_late_P6LL`
（WindowPersistence 吃 full family `recordsF` 的 late delta 界）。证明逐字。
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
  BackwardPointTrace.apply_point_eq_of_stage_eq
  RetainedCoreHistory.exists_window_point_of_edist_le from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceDistortion

namespace RetainedCoreHistory

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

/-- **`_P6LL`**：`TracedRegionOrCapWindow:31` 的 late-records + hybrid 副本（底座换成
`exists_standard_comparison_of_cap_window_trace_late_P6LL`）。 -/
theorem exists_scalar_lower_bound_of_cap_window_trace_late_P6LL :
    ∃ c : ℝ, 0 < c ∧ ∀ Θ : ℝ, 0 < Θ → Θ < 1 → ∀ C : ℝ≥0, ∃ Cbirth : ℝ, 0 < Cbirth ∧
    ∀ D : ℝ, 0 < D →
    ∃ R : ℝ, D + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
    ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters} {T₀ : ℝ}
      (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        GeometricCutoffRecord H.toHistory i p),
      (∀ i hi b, ((records i hi).static b).hasCanonicalWindow) →
      R ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
    ∀ {pF : CutoffParameters}, (∀ i, GeometricCutoffRecord H.toHistory i pF) →
    ∀ δbound : ℝ, (∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        pF.delta (H.time i.succ) ≤ δbound) →
      δbound ≤ δ₀ →
    ∀ (qcan a₀ θcap : ℝ), 0 < qcan → θcap ≤ Θ →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative C qcan k →
    ∀ t : ℝ, H.time k < t → t < s → Gk.DerivativeBoundBefore C qcan t →
    ∀ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ k)
      (y : (H.stage k).Carrier)
      (A : BackwardPointTrace H.toHistory j.succ k hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hj).static b).window x →
      t - H.time j.succ ≤ θcap * (((records j hj).static b).neck.scale)⁻¹ →
      ‖x.val‖ < D + 1 →
      qcan ≤ Cbirth * ((records j hj).static b).neck.scale →
      1 ≤ a₀ * ((records j hj).static b).neck.scale →
    c * ((records j hj).static b).neck.scale ≤
      (1 - ((records j hj).static b).neck.scale * (t - H.time j.succ)) * Gk.flow.scalar t y := by
  obtain ⟨c₀, hc₀, hscalar₀⟩ := exists_standard_scalar_lower_bound
  refine ⟨c₀ / 2, by positivity, fun Θ hΘ hΘ1 C => ?_⟩
  obtain ⟨eta, heta, hlower⟩ := exists_uniform_standard_metric_scalar_lower_comparison Θ hΘ.le hΘ1
  obtain ⟨P, Creset, Cbirth, -, -, hCbirth, hbridge⟩ :=
    exists_standard_comparison_of_cap_window_trace_late_P6LL.{u} Θ C hΘ hΘ1
  refine ⟨Cbirth, hCbirth, fun D hD => ?_⟩
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hwindow⟩ := hbridge D eta eta hD heta heta 2
  refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro H p T₀ records hcan hRp hmp hζp pF recordsF δbound hdelta hδb qcan a₀ θcap hqcan hθ hHI
    hlow k s Gk hGk hderiv t hkt hts hcur j hj hl y A b x hanchor hage hxD hbirth haq
  obtain ⟨G, L, -, -, hL, -, -, -, -, -, -, -, z, -, hy, Ξ, -, -, hΞmark, hΞ, gflow, S, -, hS2,
      -, -, hS5, -, -, Q, -, hclose⟩ :=
    hwindow H records hcan hRp hmp hζp recordsF δbound hdelta hδb qcan a₀ θcap hqcan hθ hHI
      hlow k s Gk hGk hderiv t hkt hts hcur j hj hl y A b x hanchor hage hxD hbirth haq
  set q := ((records j hj).static b).neck.scale with hqdef
  have hq : 0 < q := ((records j hj).static b).neck.scale_pos
  have hjt : H.time j.succ < t := (H.time_strictMono.monotone hl).trans_lt hkt
  set T := q * (t - H.time j.succ) with hTdef
  have hT0 : 0 ≤ T := mul_nonneg hq.le (sub_nonneg.mpr hjt.le)
  have hTΘ : T ≤ Θ := by
    have h1 : q * (t - H.time j.succ) ≤ q * (θcap * q⁻¹) := mul_le_mul_of_nonneg_left hage hq.le
    have h2 : q * (θcap * q⁻¹) = θcap := by field_simp
    linarith only [h1, h2, hTdef, hθ]
  have hTmem : T ∈ Icc 0 Θ := ⟨hT0, hTΘ⟩
  have hclT := (hclose T ⟨hT0, le_rfl⟩).2
  have hRS : c₀ / (1 - T) / 2 ≤ metricScalarAt (S.base.metric T) z := by
    have h := (hlower Q (standardCapWindow D) (S.base.metric T) T hTmem z
      (fun i hi => (hclT i hi z).le)).2
    rw [metricScalarAt_restrictOpen] at h
    have hQ := hscalar₀ Q z.val T ⟨hT0, hTΘ.trans_lt hΘ1⟩
    linarith only [h, hQ]
  have htimeT : H.time j.succ + T / q = t := by
    rw [hTdef, mul_div_cancel_left₀ _ hq.ne']
    ring
  have hST : S.base.metric T = localPullMetric (scaleMetric q hq (gflow t)) Ξ hΞ := by
    have h := hS5 T
    rwa [htimeT] at h
  have hgt : gflow t = H.toHistory.backwardSurvivorIncomingMetric j.succ k hl G L t :=
    hS2 t ⟨hkt.le, le_rfl⟩
  have hpoint : (Ξ z).val.val = y := congrArg Subtype.val hΞmark
  have hscalarT : metricScalarAt (S.base.metric T) z = q⁻¹ * Gk.flow.scalar t y := by
    rw [hST, metricScalarAt_localPullMetric_scaleMetric, hgt,
      ObservedHistory.metricScalarAt_backwardSurvivorIncomingMetric_terminal _ _ _ _ _ _
        (Gk.flow.base.metric t) hL, hpoint]
    rfl
  have h1T : 0 < 1 - T := by linarith only [hTΘ, hΘ1]
  have hG : Gk.flow.scalar t y = q * metricScalarAt (S.base.metric T) z := by
    rw [hscalarT, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
  have hdiv : c₀ / (1 - T) / 2 * (1 - T) = c₀ / 2 := by field_simp
  rw [hG]
  have h3 := mul_le_mul_of_nonneg_left hRS (mul_nonneg hq.le h1T.le)
  nlinarith only [h3, hdiv, hq]

/-- **`_P6LL`**：`TracedRegionOrCapWindow:111`（cap window age bound）的 late-records + hybrid 副本。 -/
theorem exists_capWindow_age_bound_of_scalar_le_along_trace_late_P6LL :
    ∃ c : ℝ, 0 < c ∧ ∀ Θ : ℝ, 0 < Θ → Θ < 1 → ∀ C : ℝ≥0, ∃ Cbirth : ℝ, 0 < Cbirth ∧
    ∀ D : ℝ, 0 < D →
    ∃ R : ℝ, D + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
    ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters} {T₀ : ℝ}
      (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        GeometricCutoffRecord H.toHistory i p),
      (∀ i hi b, ((records i hi).static b).hasCanonicalWindow) →
      R ≤ p.modelRadius → m₀ ≤ p.modelOrder → p.modelAccuracy ≤ ζ₀ →
    ∀ {pF : CutoffParameters}, (∀ i, GeometricCutoffRecord H.toHistory i pF) →
    ∀ δbound : ℝ, (∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
        pF.delta (H.time i.succ) ≤ δbound) →
      δbound ≤ δ₀ →
    ∀ (qcan a₀ : ℝ), 0 < qcan →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
    ∀ (u t : Icc (0 : ℝ) H.toHistory.horizon), u ≤ t →
      H.EventSlabsDerivative C qcan (H.toHistory.activeStage t) →
      (∀ i : Fin H.eventCount, i.castSucc = H.toHistory.activeStage t →
        (H.toHistory.event i).incoming.DerivativeBoundBefore C qcan t) →
      (∀ h : H.time (Fin.last H.eventCount) < H.horizon,
        H.toHistory.activeStage t = Fin.last H.eventCount →
        ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore C qcan t) →
    ∀ (j : Fin H.eventCount) (hj : T₀ ≤ H.time j.succ) (hl : j.succ ≤ H.toHistory.activeStage t)
      (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
      (A : BackwardPointTrace H.toHistory j.succ (H.toHistory.activeStage t) hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j hj).static b).window x → ‖x.val‖ < D + 1 →
      qcan ≤ Cbirth * ((records j hj).static b).neck.scale →
      1 ≤ a₀ * ((records j hj).static b).neck.scale →
      (u : ℝ) ≤ H.time j.succ →
    ∀ M θcap : ℝ, 0 < θcap → θcap < Θ →
      (∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (hjv : j.succ ≤ H.toHistory.activeStage v)
          (hvt : v ≤ t),
        metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
          (A.point (H.toHistory.activeStage v) hjv (H.toHistory.activeStage_mono hvt)) ≤ M) →
      M * ((t : ℝ) - u) * (1 - θcap) ≤ c * θcap →
      (t : ℝ) - H.time j.succ ≤ θcap * (((records j hj).static b).neck.scale)⁻¹ := by
  obtain ⟨c, hc, hB⟩ := exists_scalar_lower_bound_of_cap_window_trace_late_P6LL.{u}
  refine ⟨c, hc, fun Θ hΘ hΘ1 C => ?_⟩
  obtain ⟨Cbirth, hCb, hB⟩ := hB Θ hΘ hΘ1 C
  refine ⟨Cbirth, hCb, fun D hD => ?_⟩
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζh, hδ₀, hB⟩ := hB D hD
  refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζh, hδ₀, ?_⟩
  intro H p T₀ records hcan hRp hmp hζp pF recordsF δbound hdelta hδb qcan a₀ hqcan hHI hlow u t
    hut hslabs hcurrent hfinal j hj hl y A b x hmark hxD hbirth haq huj M θcap hθ0 hθΘ hscal hMθ
  set q := ((records j hj).static b).neck.scale with hqdef
  have hq : 0 < q := ((records j hj).static b).neck.scale_pos
  set Tj := H.time j.succ with hTj
  by_contra hcon
  have hage : θcap < q * ((t : ℝ) - Tj) := by
    have h1 := mul_lt_mul_of_pos_left (lt_of_not_ge hcon) hq
    rwa [show q * (θcap * q⁻¹) = θcap by field_simp] at h1
  have hinf : (Ioo θcap (min (q * ((t : ℝ) - Tj)) Θ)).Infinite :=
    Set.Ioo_infinite (lt_min hage hθΘ)
  obtain ⟨τ, hτ, hτE⟩ :=
    hinf.exists_notMem_finset (Finset.univ.image fun k => q * (H.time k - Tj))
  have hτ0 : 0 < τ := hθ0.trans hτ.1
  have hτage : τ < q * ((t : ℝ) - Tj) := hτ.2.trans_le (min_le_left _ _)
  have hτΘ : τ < Θ := hτ.2.trans_le (min_le_right _ _)
  set t' := Tj + τ / q with ht'
  have hτq : 0 < τ / q := div_pos hτ0 hq
  have hTjt' : Tj < t' := by linarith
  have ht't : t' < t := by
    have h1 : τ / q < (t : ℝ) - Tj := by rw [div_lt_iff₀ hq]; linarith
    linarith
  have hτeq : q * (t' - Tj) = τ := by rw [ht']; field_simp; ring
  have ht'ne : ∀ k, H.time k ≠ t' := by
    intro k hk
    apply hτE
    refine Finset.mem_image.mpr ⟨k, Finset.mem_univ _, ?_⟩
    rw [hk, hτeq]
  let v : Icc (0 : ℝ) H.toHistory.horizon :=
    ⟨t', (H.toHistory.time_nonneg _).trans hTjt'.le, ht't.le.trans t.2.2⟩
  have hjv : j.succ ≤ H.toHistory.activeStage v := H.toHistory.le_activeStage v j.succ hTjt'.le
  have hvt : v ≤ t := ht't.le
  have hkt := H.toHistory.activeStage_mono hvt
  have hkv : H.time (H.toHistory.activeStage v) < t' :=
    lt_of_le_of_ne (H.toHistory.activeStage_time_le v) (ht'ne _)
  have hage' : t' - Tj ≤ τ * q⁻¹ := le_of_eq (by rw [ht']; ring)
  have hkey : c * q ≤ (1 - τ) *
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
        (A.point (H.toHistory.activeStage v) hjv hkt) := by
    by_cases hk : H.toHistory.activeStage v = Fin.last H.eventCount
    · have hlt : H.time (Fin.last H.eventCount) < H.horizon := by
        have h1 := hkv
        rw [hk] at h1
        exact h1.trans (ht't.trans_le t.2.2)
      have htl : H.toHistory.activeStage t = Fin.last H.eventCount :=
        le_antisymm (Fin.le_last _) (hk ▸ hkt)
      have hji : j.succ ≤ Fin.last H.eventCount := hk ▸ hjv
      have hit : Fin.last H.eventCount ≤ H.toHistory.activeStage t := htl.ge
      have hder : H.EventSlabsDerivative C qcan (Fin.last H.eventCount) := htl ▸ hslabs
      have hdbb : ((H.finalSlab hlt).restrictIncoming le_rfl hlt le_rfl).DerivativeBoundBefore
          C qcan t' :=
        ((H.finalSlab hlt).restrictIncoming le_rfl hlt le_rfl).derivativeBoundBefore_mono
          ht't.le (hfinal hlt htl)
      have hk' : H.time (Fin.last H.eventCount) < t' := hk ▸ hkv
      have hb := hB H records hcan hRp hmp hζp recordsF δbound hdelta hδb qcan a₀ τ hqcan hτΘ.le
        hHI hlow (Fin.last H.eventCount) H.horizon
        ((H.finalSlab hlt).restrictIncoming le_rfl hlt le_rfl) (H.final_initial hlt) hder t' hk'
        (ht't.trans_le t.2.2) hdbb j hj hji (A.point (Fin.last H.eventCount) hji hit)
        (A.restrictLast hji hit) b x hmark hage' hxD hbirth haq
      rw [hτeq] at hb
      have heq := BackwardPointTrace.apply_point_eq_of_stage_eq A
        (fun m p => metricScalarAt (H.toHistory.stageMetric m t') p) hk.symm hji hit hjv hkt
      have hsl : metricScalarAt (H.toHistory.stageMetric (Fin.last H.eventCount) t')
          (A.point (Fin.last H.eventCount) hji hit) =
          ((H.finalSlab hlt).restrictIncoming le_rfl hlt le_rfl).flow.scalar t'
            (A.point (Fin.last H.eventCount) hji hit) := by
        rw [ObservedHistory.stageMetric_last_of_lt (h := hlt)]
        rfl
      change c * q ≤ (1 - τ) * metricScalarAt (H.toHistory.stageMetric _ t') _
      rw [← heq, hsl]
      exact hb
    · obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hk
      have hti : t' < H.time i.succ :=
        ObservedHistory.time_lt_succ_of_activeStage_eq_castSucc H.toHistory v i hi.symm
      have hji : j.succ ≤ i.castSucc := hi ▸ hjv
      have hit : i.castSucc ≤ H.toHistory.activeStage t := hi ▸ hkt
      have hder : H.EventSlabsDerivative C qcan i.castSucc :=
        fun j' hj' => hslabs j' (hj'.trans_le hit)
      have hdbb : (H.toHistory.event i).incoming.DerivativeBoundBefore C qcan t' := by
        rcases eq_or_lt_of_le hit with heq | hlt
        · exact (H.toHistory.event i).incoming.derivativeBoundBefore_mono ht't.le
            (hcurrent i heq)
        · exact (H.toHistory.event i).incoming.derivativeBoundBefore_mono hti.le (hslabs i hlt)
      have hk' : H.time i.castSucc < t' := hi ▸ hkv
      have hb := hB H records hcan hRp hmp hζp recordsF δbound hdelta hδb qcan a₀ τ hqcan hτΘ.le
        hHI hlow i.castSucc (H.time i.succ) (H.toHistory.event i).incoming (H.event_initial i)
        hder t' hk' hti hdbb j hj hji (A.point i.castSucc hji hit) (A.restrictLast hji hit) b x
        hmark hage' hxD hbirth haq
      rw [hτeq] at hb
      have heq := BackwardPointTrace.apply_point_eq_of_stage_eq A
        (fun m p => metricScalarAt (H.toHistory.stageMetric m t') p) hi hji hit hjv hkt
      have hsl : metricScalarAt (H.toHistory.stageMetric i.castSucc t')
          (A.point i.castSucc hji hit) =
          (H.toHistory.event i).incoming.flow.scalar t' (A.point i.castSucc hji hit) := by
        rw [ObservedHistory.stageMetric_castSucc_apply]
        rfl
      change c * q ≤ (1 - τ) * metricScalarAt (H.toHistory.stageMetric _ t') _
      rw [← heq, hsl]
      exact hb
  have hMs := hscal v hjv hvt
  have h1τ : 0 < 1 - τ := by linarith
  have hM0 : 0 < M := by
    by_contra hM
    have h2 := mul_le_mul_of_nonneg_left (hMs.trans (not_lt.mp hM)) h1τ.le
    nlinarith
  have htu : (0 : ℝ) ≤ (t : ℝ) - u := sub_nonneg.mpr hut
  have hqtu : τ ≤ q * ((t : ℝ) - u) := by nlinarith
  have hcq : c * q ≤ (1 - τ) * M := hkey.trans (mul_le_mul_of_nonneg_left hMs h1τ.le)
  have h3 : c * τ ≤ (1 - τ) * M * ((t : ℝ) - u) := by
    calc c * τ ≤ c * (q * ((t : ℝ) - u)) := mul_le_mul_of_nonneg_left hqtu hc.le
      _ = c * q * ((t : ℝ) - u) := by ring
      _ ≤ (1 - τ) * M * ((t : ℝ) - u) := mul_le_mul_of_nonneg_right hcq htu
  have h4 : (1 - τ) * M * ((t : ℝ) - u) ≤ (1 - θcap) * M * ((t : ℝ) - u) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith [hτ.1]) hM0.le) htu
  have h5 : c * θcap < c * τ := mul_lt_mul_of_pos_left hτ.1 hc
  nlinarith

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
