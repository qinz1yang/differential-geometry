import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedGoodPointBounds

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

theorem exists_standard_time_le_of_close_scalar_mul_lt :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ τ : ℝ, 0 ≤ τ →
    ∀ (Q : StandardSolution) (x : EuclideanSpace ℝ (Fin 3)) (T R : ℝ),
      0 ≤ T → T < 1 → |R - metricScalarAt (Q.val.metric T) x| < 1 → T * R < τ →
        T ≤ (τ + 1) / (τ + 1 + c₀) := by
  obtain ⟨c₀, hc₀, hlow⟩ := exists_standard_scalar_lower_bound
  refine ⟨c₀, hc₀, fun τ hτ Q x T R hT0 hT1 hclose hage => ?_⟩
  set u := c₀ / (1 - T) with hudef
  have hu : T * u * (1 - T) = T * c₀ := by
    rw [mul_assoc, hudef, div_mul_cancel₀ _ (sub_pos.mpr hT1).ne']
  have hQ : u ≤ metricScalarAt (Q.val.metric T) x := hlow Q x T ⟨hT0, hT1⟩
  have hR : u - 1 ≤ R := by linarith [(abs_lt.mp hclose).1]
  have h1 : T * (u - 1) ≤ T * R := mul_le_mul_of_nonneg_left hR hT0
  have h2 : (T * u - T) * (1 - T) ≤ τ * (1 - T) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  rw [le_div_iff₀ (by linarith)]
  nlinarith [h2, hu, sq_nonneg (1 - T)]

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage.IncomingSlab

theorem exists_scalar_derivative_bounds_of_windowedModelWitness :
    ∃ Cw : ℝ, 0 < Cw ∧
      ∀ {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) {eps kappa : ℝ}
        {y : P.Carrier} {t : ℝ}, WindowedModelWitness eps kappa G.flow y t → eps ≤ 1 / 4 →
        Ioo (t - (eps * G.flow.scalar t y)⁻¹) t ⊆ Ioo a s →
      ∀ Ctime Cgrad : ℝ≥0, Cw ≤ Ctime → 2 * Cw ≤ Cgrad →
        |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2 ∧
        ∀ v : TangentSpace I3 y,
          |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t y v| ≤
            Cgrad * G.flow.scalar t y * Real.sqrt (G.flow.scalar t y) *
              Real.sqrt ((G.flow.base.metric t).inner y v v) := by
  obtain ⟨Cw, hCw, hW⟩ := exists_windowedModelWitness_scalar_derivative_bounds.{u}
  refine ⟨Cw, hCw, ?_⟩
  intro P a s G eps kappa y t W heps hwin Ctime Cgrad hCt hCg
  have hreg : Ioo (t - (eps * G.flow.scalar t y)⁻¹) t ⊆
      (RealTimeInterval.closedOpen a s G.lt).regular := hwin
  obtain ⟨hg, hd⟩ := hW G.equation W heps hreg
  have hR : 0 ≤ G.flow.scalar t y := W.scalar_pos.le
  refine ⟨hd.trans (mul_le_mul_of_nonneg_right hCt (sq_nonneg _)), fun v => (hg v).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCg hR) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end OrientedThreeStage.IncomingSlab

namespace RetainedCoreHistory

theorem exists_uniform_derivative_gradient_bounds_of_cap_window_trace
    (Θ : ℝ) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ c C' : ℝ, 0 < c ∧ 0 < C' ∧ ∀ C : ℝ≥0, ∃ Cbirth : ℝ, 0 < Cbirth ∧
    ∀ (D : ℝ), 0 < D →
    ∃ R : ℝ, D + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
    ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ (H : RetainedCoreHistory.{u}) (p₀ : CutoffParameters)
      (δbound ρbound : ℝ) {p : CutoffParameters}
      (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      δbound ≤ δ₀ → R ≤ p₀.modelRadius → m₀ ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀ →
    ∀ (qcan a₀ θcap : ℝ), 0 < qcan → θcap ≤ Θ →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative C qcan k →
    ∀ t : ℝ, H.time k < t → t < s → Gk.DerivativeBoundBefore C qcan t →
    ∀ (j : Fin H.eventCount) (hl : j.succ ≤ k) (y : (H.stage k).Carrier)
      (A : BackwardPointTrace H.toHistory j.succ k hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j).static b).window x →
      t - H.time j.succ ≤ θcap * (((records j).static b).neck.scale)⁻¹ →
      ‖x.val‖ < D + 1 →
      qcan ≤ Cbirth * ((records j).static b).neck.scale →
      1 ≤ a₀ * ((records j).static b).neck.scale →
    c * ((records j).static b).neck.scale ≤ Gk.flow.scalar t y ∧
      |derivWithin (fun v => Gk.flow.scalar v y) (Iic t) t| ≤ C' * Gk.flow.scalar t y ^ 2 ∧
      ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential Gk.flow t y v| ≤
          C' * Gk.flow.scalar t y * Real.sqrt (Gk.flow.scalar t y) *
            Real.sqrt ((Gk.flow.base.metric t).inner y v v) := by
  obtain ⟨ε₀, A₀, hε₀, hA₀, hjet₀⟩ :=
    StandardCap.exists_uniform_curvature_derivative_bound_of_standard_metric_close_on_opens
      Θ hΘ.le hΘ1 0
  obtain ⟨ε₁, A₁, hε₁, hA₁, hjet₁⟩ :=
    StandardCap.exists_uniform_curvature_derivative_bound_of_standard_metric_close_on_opens
      Θ hΘ.le hΘ1 1
  obtain ⟨ε₂, A₂, hε₂, hA₂, hjet₂⟩ :=
    StandardCap.exists_uniform_curvature_derivative_bound_of_standard_metric_close_on_opens
      Θ hΘ.le hΘ1 2
  obtain ⟨eta, heta, hlower⟩ := exists_uniform_standard_metric_scalar_lower_comparison Θ hΘ.le hΘ1
  obtain ⟨c₀, hc₀, hscalar₀⟩ := exists_standard_scalar_lower_bound
  set B : ℝ := A₀ + A₁ + A₂ with hBdef
  have hB : 0 ≤ B := by positivity
  set c : ℝ := c₀ / 2 with hcdef
  have hc : 0 < c := by positivity
  set ε : ℝ := min (min ε₀ ε₁) (min ε₂ eta) with hεdef
  have hε : 0 < ε := lt_min (lt_min hε₀ hε₁) (lt_min hε₂ heta)
  refine ⟨c, ((Module.finrank ℝ ThreeSpace : ℝ) ^ 6 * Real.sqrt B +
    2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 4 * B) / c ^ 2 +
    (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt B / (c * Real.sqrt c) + 1, hc,
    by positivity, fun C => ?_⟩
  obtain ⟨P, Creset, Cbirth, -, -, hCbirth, hbridge⟩ :=
    exists_standard_comparison_of_cap_window_trace.{u} Θ C hΘ hΘ1
  refine ⟨Cbirth, hCbirth, ?_⟩
  intro D hD
  obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hwindow⟩ := hbridge D ε ε hD hε hε 4
  refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
  intro H p₀ δbound ρbound p records hfam hδb hRp hmp hζp qcan a₀ θcap hqcan hθ hHI hlow
    k s Gk hGk hderiv t hkt hts hcur j hl y A b x hanchor hage hxD hbirth haq
  obtain ⟨G, L, -, -, hL, -, -, -, -, -, -, -, z, -, hy, Ξ, -, -, hΞmark, hΞ, gflow, S, -, hS2,
      -, -, hS5, -, -, Q, -, hclose⟩ :=
    hwindow H p₀ δbound ρbound records hfam hδb hRp hmp hζp qcan a₀ θcap hqcan hθ hHI hlow
      k s Gk hGk hderiv t hkt hts hcur j hl y A b x hanchor hage hxD hbirth haq
  set q := ((records j).static b).neck.scale with hqdef
  have hq : 0 < q := ((records j).static b).neck.scale_pos
  have hjt : H.time j.succ < t := (H.time_strictMono.monotone hl).trans_lt hkt
  set T := q * (t - H.time j.succ) with hTdef
  have hT0 : 0 ≤ T := mul_nonneg hq.le (sub_nonneg.mpr hjt.le)
  have hTΘ : T ≤ Θ := by
    have h1 : q * (t - H.time j.succ) ≤ q * (θcap * q⁻¹) := mul_le_mul_of_nonneg_left hage hq.le
    have h2 : q * (θcap * q⁻¹) = θcap := by field_simp
    linarith only [h1, h2, hTdef, hθ]
  have hTmem : T ∈ Icc 0 Θ := ⟨hT0, hTΘ⟩
  have hclT := (hclose T ⟨hT0, le_rfl⟩).1
  have hsmall : ∀ i ≤ 4, metricDerivNorm i (S.base.metric T)
      ((Q.val.metric T).restrictOpen (standardCapWindow D))
      (StandardCap.metric.restrictOpen (standardCapWindow D)) z ≤ ε :=
    fun i hi => (hclT i hi z).le
  have hjS : ∀ i ≤ 2, curvDerivNormSq i (S.base.metric T) z ≤ B := by
    intro i hi
    interval_cases i
    · have h := hjet₀ _ (S.base.metric T) Q T hTmem z (fun i hi => (hsmall i (by omega)).trans
        ((min_le_left _ _).trans (min_le_left _ _)))
      linarith only [h, hBdef, hA₁, hA₂]
    · have h := hjet₁ _ (S.base.metric T) Q T hTmem z (fun i hi => (hsmall i (by omega)).trans
        ((min_le_left _ _).trans (min_le_right _ _)))
      linarith only [h, hBdef, hA₀, hA₂]
    · have h := hjet₂ _ (S.base.metric T) Q T hTmem z (fun i hi => (hsmall i (by omega)).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
      linarith only [h, hBdef, hA₀, hA₁]
  have hRS : c ≤ metricScalarAt (S.base.metric T) z := by
    have h := (hlower Q (standardCapWindow D) (S.base.metric T) T hTmem z (fun i hi =>
      (hsmall i (by omega)).trans ((min_le_right _ _).trans (min_le_right _ _)))).2
    rw [metricScalarAt_restrictOpen] at h
    have hQ := hscalar₀ Q z.val T ⟨hT0, hTΘ.trans_lt hΘ1⟩
    have hdiv : c₀ ≤ c₀ / (1 - T) := by
      rw [le_div_iff₀ (by linarith only [hTΘ, hΘ1])]
      nlinarith only [mul_nonneg hc₀.le hT0]
    rw [hcdef]
    linarith only [h, hQ, hdiv]
  have htimeT : H.time j.succ + T / q = t := by
    rw [hTdef, mul_div_cancel_left₀ _ hq.ne']
    ring
  have hST : S.base.metric T = localPullMetric (scaleMetric q hq (gflow t)) Ξ hΞ := by
    have h := hS5 T
    rwa [htimeT] at h
  have hgt : gflow t = H.toHistory.backwardSurvivorIncomingMetric j.succ k hl G L t :=
    hS2 t ⟨hkt.le, le_rfl⟩
  have hpoint : (Ξ z).val.val = y :=
    congrArg Subtype.val hΞmark
  have hscalarT : metricScalarAt (S.base.metric T) z = q⁻¹ * Gk.flow.scalar t y := by
    rw [hST, metricScalarAt_localPullMetric_scaleMetric, hgt,
      ObservedHistory.metricScalarAt_backwardSurvivorIncomingMetric_terminal _ _ _ _ _ _
        (Gk.flow.base.metric t) hL, hpoint]
    rfl
  have hjG : ∀ i ≤ 2, curvDerivNormSq i (Gk.flow.base.metric t) y ≤ q ^ (i + 2) * B := by
    intro i hi
    have h := curvDerivNormSq_localPullMetric_scaleMetric (gflow t) Ξ hΞ hq i z
    rw [← hST, hgt, ObservedHistory.curvDerivNormSq_backwardSurvivorIncomingMetric_terminal
      _ _ _ _ _ _ (Gk.flow.base.metric t) hL, hpoint] at h
    have h' : curvDerivNormSq i (Gk.flow.base.metric t) y =
        q ^ (i + 2) * curvDerivNormSq i (S.base.metric T) z := by
      rw [h, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hq.ne', one_pow, one_mul]
    rw [h']
    exact mul_le_mul_of_nonneg_left (hjS i hi) (pow_nonneg hq.le _)
  have hRG : c * q ≤ Gk.flow.scalar t y := by
    have h : Gk.flow.scalar t y = q * metricScalarAt (S.base.metric T) z := by
      rw [hscalarT, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
    rw [h, mul_comm c q]
    exact mul_le_mul_of_nonneg_left hRS hq.le
  have hreg : t ∈ (RealTimeInterval.closedOpen (H.time k) s Gk.lt).regular := ⟨hkt, hts⟩
  obtain ⟨hd, hg⟩ := abs_scalar_derivatives_le_of_scaled_curvature_jets Gk.flow Gk.equation hreg
    hq hB hc y hjG hRG
  exact ⟨hRG, hd, hg⟩

theorem exists_cap_window_scalar_derivative_gradient_constants (τQ : ℝ) (hτQ : 0 ≤ τQ) :
    ∃ (Θ₂ : ℝ) (Ctime₀ Cgrad₀ : ℝ≥0), 0 < Θ₂ ∧ Θ₂ < 1 ∧
    (∀ (Q : StandardSolution) (x : EuclideanSpace ℝ (Fin 3)) (T R : ℝ), 0 ≤ T → T < 1 →
      |R - metricScalarAt (Q.val.metric T) x| < 1 → T * R < τQ → T ≤ Θ₂) ∧
    (∀ {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) {eps kappa : ℝ}
      {y : P.Carrier} {t : ℝ}, WindowedModelWitness eps kappa G.flow y t → eps ≤ 1 / 4 →
      Ioo (t - (eps * G.flow.scalar t y)⁻¹) t ⊆ Ioo a s →
    ∀ Ctime Cgrad : ℝ≥0, Ctime₀ ≤ Ctime → Cgrad₀ ≤ Cgrad →
      |derivWithin (fun v => G.flow.scalar v y) (Iic t) t| ≤ Ctime * G.flow.scalar t y ^ 2 ∧
      ∀ v : TangentSpace I3 y,
        |Perelman.CanonicalNeighborhood.scalarDifferential G.flow t y v| ≤
          Cgrad * G.flow.scalar t y * Real.sqrt (G.flow.scalar t y) *
            Real.sqrt ((G.flow.base.metric t).inner y v v)) ∧
    ∀ C : ℝ≥0, ∃ Cbirth : ℝ, 0 < Cbirth ∧
    ∀ (D : ℝ), 0 < D →
    ∃ R : ℝ, D + 1 < R ∧ ∃ m₀ : ℕ, 4 ≤ m₀ ∧
    ∃ ζ₀ δ₀ : ℝ, 0 < ζ₀ ∧ ζ₀ ≤ 1 / 2 ∧ 0 < δ₀ ∧
    ∀ (H : RetainedCoreHistory.{u}) (p₀ : CutoffParameters)
      (δbound ρbound : ℝ) {p : CutoffParameters}
      (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      δbound ≤ δ₀ → R ≤ p₀.modelRadius → m₀ ≤ p₀.modelOrder → p₀.modelAccuracy ≤ ζ₀ →
    ∀ (qcan a₀ : ℝ), 0 < qcan →
      (∀ x, InFixedHamiltonIveyRegion (H.initialMetric 0) a₀ x) →
      (∀ x, -3 / a₀ ≤ metricScalarAt (H.initialMetric 0) x) →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative C qcan k →
    ∀ t : ℝ, H.time k < t → t < s → Gk.DerivativeBoundBefore C qcan t →
    ∀ (j : Fin H.eventCount) (hl : j.succ ≤ k) (y : (H.stage k).Carrier)
      (A : BackwardPointTrace H.toHistory j.succ k hl y)
      (b : (H.toHistory.event j).RetainedBoundaryIndex) (x : standardCapWindow p.modelRadius),
      A.point j.succ le_rfl hl = ((records j).static b).window x →
      t - H.time j.succ ≤ Θ₂ * (((records j).static b).neck.scale)⁻¹ →
      ‖x.val‖ < D + 1 →
      qcan ≤ Cbirth * ((records j).static b).neck.scale →
      1 ≤ a₀ * ((records j).static b).neck.scale →
    ∀ Ctime Cgrad : ℝ≥0, Ctime₀ ≤ Ctime → Cgrad₀ ≤ Cgrad →
      |derivWithin (fun v => Gk.flow.scalar v y) (Iic t) t| ≤ Ctime * Gk.flow.scalar t y ^ 2 ∧
      ∀ v : TangentSpace I3 y,
        |Perelman.CanonicalNeighborhood.scalarDifferential Gk.flow t y v| ≤
          Cgrad * Gk.flow.scalar t y * Real.sqrt (Gk.flow.scalar t y) *
            Real.sqrt ((Gk.flow.base.metric t).inner y v v) := by
  obtain ⟨Cw, hCw, hW⟩ :=
    OrientedThreeStage.IncomingSlab.exists_scalar_derivative_bounds_of_windowedModelWitness.{u}
  obtain ⟨c₀, hc₀, hage⟩ := exists_standard_time_le_of_close_scalar_mul_lt
  set Θ₂ : ℝ := (τQ + 1) / (τQ + 1 + c₀) with hΘ₂
  have hΘ₂0 : 0 < Θ₂ := by positivity
  have hΘ₂1 : Θ₂ < 1 := by rw [hΘ₂, div_lt_one (by positivity)]; linarith
  obtain ⟨c, C', hc, hC', hD2⟩ :=
    exists_uniform_derivative_gradient_bounds_of_cap_window_trace.{u} Θ₂ hΘ₂0 hΘ₂1
  refine ⟨Θ₂, ⟨max Cw C', le_max_of_le_left hCw.le⟩,
    ⟨max (2 * Cw) C', le_max_of_le_left (by positivity)⟩, hΘ₂0, hΘ₂1,
    fun Q x T R hT0 hT1 hclose hTR => hage τQ hτQ Q x T R hT0 hT1 hclose hTR, ?_, ?_⟩
  · intro P a s G eps kappa y t W heps hwin Ctime Cgrad hCt hCg
    have hCt' : max Cw C' ≤ (Ctime : ℝ) := NNReal.coe_le_coe.mpr hCt
    have hCg' : max (2 * Cw) C' ≤ (Cgrad : ℝ) := NNReal.coe_le_coe.mpr hCg
    exact hW G W heps hwin Ctime Cgrad ((le_max_left _ _).trans hCt')
      ((le_max_left _ _).trans hCg')
  · intro C
    obtain ⟨Cbirth, hCbirth, hC⟩ := hD2 C
    refine ⟨Cbirth, hCbirth, fun D hD => ?_⟩
    obtain ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, hbound⟩ := hC D hD
    refine ⟨R, hDR, m₀, hm₀, ζ₀, δ₀, hζ₀, hζhalf, hδ₀, ?_⟩
    intro H p₀ δbound ρbound p records hfam hδb hRp hmp hζp qcan a₀ hqcan hHI hlow
      k s Gk hGk hderiv t hkt hts hcur j hl y A b x hanchor hTage hxD hbirth haq
      Ctime Cgrad hCt hCg
    obtain ⟨hRG, hd, hg⟩ := hbound H p₀ δbound ρbound records hfam hδb hRp hmp hζp qcan a₀ Θ₂
      hqcan le_rfl hHI hlow k s Gk hGk hderiv t hkt hts hcur j hl y A b x hanchor hTage hxD
      hbirth haq
    have hCt' : C' ≤ (Ctime : ℝ) := (le_max_right _ _).trans (NNReal.coe_le_coe.mpr hCt)
    have hCg' : C' ≤ (Cgrad : ℝ) := (le_max_right _ _).trans (NNReal.coe_le_coe.mpr hCg)
    have hR : 0 ≤ Gk.flow.scalar t y :=
      le_trans (mul_nonneg hc.le ((records j).static b).neck.scale_pos.le) hRG
    refine ⟨hd.trans (mul_le_mul_of_nonneg_right hCt' (sq_nonneg _)), fun v => (hg v).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCg' hR) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
