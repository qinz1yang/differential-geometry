import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowStandardComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardActionComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardTerminalBlowup
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullbackScaling

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)

private theorem sq_le_div_sq_of_mul_le {c q R : ℝ} (hc : 0 < c) (hq : 0 ≤ q)
    (hR : c * q ≤ R) : q ^ 2 ≤ R ^ 2 / c ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  have h := pow_le_pow_left₀ (mul_nonneg hc.le hq) hR 2
  nlinarith [h]

theorem abs_derivWithin_scalar_le_of_scaled_curvature_jets
    (hS : IsSolutionOn S) {t q B c : ℝ} (ht : t ∈ D.regular) (hq : 0 < q) (hB : 0 ≤ B)
    (hc : 0 < c) (x : M)
    (hjets : ∀ j ≤ 2, curvDerivNormSq j (S.base.metric t) x ≤ q ^ (j + 2) * B)
    (hR : c * q ≤ S.scalar t x) :
    |derivWithin (fun s => S.scalar s x) (Iic t) t| ≤
      ((Module.finrank ℝ E : ℝ) ^ 6 * Real.sqrt B + 2 * (Module.finrank ℝ E : ℝ) ^ 4 * B) /
        c ^ 2 * S.scalar t x ^ 2 := by
  have hdiff : DifferentiableAt ℝ (fun s => S.scalar s x) t :=
    (hS.scalarTime (D.regular_subset ht) (fun _ h => h) x).differentiableAt
      (D.regular_mem_nhds ht)
  rw [hdiff.derivWithin (uniqueDiffWithinAt_Iic t)]
  have h0 : curvDerivNormSq 0 (S.base.metric t) x ≤ q ^ 2 * B := hjets 0 (by norm_num)
  have h2 : curvDerivNormSq 2 (S.base.metric t) x ≤ (q ^ 2) ^ 2 * B := by
    have h := hjets 2 le_rfl
    rwa [show q ^ (2 + 2) = (q ^ 2) ^ 2 by ring] at h
  have hb := abs_deriv_scalar_le_of_curvature_jets S hS ht x h0 h2
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)] at hb
  set n := (Module.finrank ℝ E : ℝ)
  have hT : 0 ≤ n ^ 6 * Real.sqrt B + 2 * n ^ 4 * B := by positivity
  have hq2 := sq_le_div_sq_of_mul_le hc hq.le hR
  calc |deriv (fun s => S.scalar s x) t|
      ≤ q ^ 2 * (n ^ 6 * Real.sqrt B + 2 * n ^ 4 * B) := by linarith
    _ ≤ S.scalar t x ^ 2 / c ^ 2 * (n ^ 6 * Real.sqrt B + 2 * n ^ 4 * B) :=
        mul_le_mul_of_nonneg_right hq2 hT
    _ = (n ^ 6 * Real.sqrt B + 2 * n ^ 4 * B) / c ^ 2 * S.scalar t x ^ 2 := by ring

omit [I.Boundaryless] in
theorem abs_scalarDifferential_le_of_scaled_curvature_jet
    {t q B c : ℝ} (hq : 0 < q) (hc : 0 < c) (x : M)
    (hfirst : curvDerivNormSq 1 (S.base.metric t) x ≤ q ^ 3 * B)
    (hR : c * q ≤ S.scalar t x) (v : TangentSpace I x) :
    |Perelman.CanonicalNeighborhood.scalarDifferential S t x v| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt B / (c * Real.sqrt c) * S.scalar t x *
        Real.sqrt (S.scalar t x) * Real.sqrt ((S.base.metric t).inner x v v) := by
  have hb := abs_scalarDifferential_le_of_curvature_jet S x hfirst v
  have hsq : Real.sqrt (q ^ 3 * B) = q * Real.sqrt q * Real.sqrt B := by
    rw [Real.sqrt_mul (by positivity), show q ^ 3 = q ^ 2 * q by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hq.le]
  rw [hsq] at hb
  set R := S.scalar t x
  have hqR : q ≤ R / c := by rw [le_div_iff₀ hc]; linarith
  have hsqrt : Real.sqrt q ≤ Real.sqrt R / Real.sqrt c := by
    rw [← Real.sqrt_div' _ hc.le]
    exact Real.sqrt_le_sqrt hqR
  have hRc : 0 ≤ R / c := div_nonneg (by nlinarith) hc.le
  have hprod : q * Real.sqrt q ≤ R * Real.sqrt R / (c * Real.sqrt c) := by
    have h := mul_le_mul hqR hsqrt (Real.sqrt_nonneg q) hRc
    rwa [div_mul_div_comm] at h
  set n := (Module.finrank ℝ E : ℝ)
  have hg := Real.sqrt_nonneg ((S.base.metric t).inner x v v)
  have hsB := Real.sqrt_nonneg B
  calc |Perelman.CanonicalNeighborhood.scalarDifferential S t x v|
      ≤ n ^ 2 * (q * Real.sqrt q * Real.sqrt B) *
          Real.sqrt ((S.base.metric t).inner x v v) := hb
    _ = n ^ 2 * Real.sqrt B * (q * Real.sqrt q) *
          Real.sqrt ((S.base.metric t).inner x v v) := by ring
    _ ≤ n ^ 2 * Real.sqrt B * (R * Real.sqrt R / (c * Real.sqrt c)) *
          Real.sqrt ((S.base.metric t).inner x v v) := by gcongr
    _ = n ^ 2 * Real.sqrt B / (c * Real.sqrt c) * R * Real.sqrt R *
          Real.sqrt ((S.base.metric t).inner x v v) := by ring

theorem abs_scalar_derivatives_le_of_scaled_curvature_jets
    (hS : IsSolutionOn S) {t q B c : ℝ} (ht : t ∈ D.regular) (hq : 0 < q) (hB : 0 ≤ B)
    (hc : 0 < c) (x : M)
    (hjets : ∀ j ≤ 2, curvDerivNormSq j (S.base.metric t) x ≤ q ^ (j + 2) * B)
    (hR : c * q ≤ S.scalar t x) :
    |derivWithin (fun s => S.scalar s x) (Iic t) t| ≤
      (((Module.finrank ℝ E : ℝ) ^ 6 * Real.sqrt B + 2 * (Module.finrank ℝ E : ℝ) ^ 4 * B) /
        c ^ 2 + (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt B / (c * Real.sqrt c) + 1) *
        S.scalar t x ^ 2 ∧
    ∀ v : TangentSpace I x,
      |Perelman.CanonicalNeighborhood.scalarDifferential S t x v| ≤
        (((Module.finrank ℝ E : ℝ) ^ 6 * Real.sqrt B + 2 * (Module.finrank ℝ E : ℝ) ^ 4 * B) /
          c ^ 2 + (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt B / (c * Real.sqrt c) + 1) *
          S.scalar t x * Real.sqrt (S.scalar t x) * Real.sqrt ((S.base.metric t).inner x v v) := by
  have hd : 0 ≤ ((Module.finrank ℝ E : ℝ) ^ 6 * Real.sqrt B +
      2 * (Module.finrank ℝ E : ℝ) ^ 4 * B) / c ^ 2 := by positivity
  have hg : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt B / (c * Real.sqrt c) := by positivity
  have hR0 : 0 ≤ S.scalar t x := le_trans (by positivity) hR
  refine ⟨(abs_derivWithin_scalar_le_of_scaled_curvature_jets S hS ht hq hB hc x hjets hR).trans
    (mul_le_mul_of_nonneg_right (by linarith only [hg]) (sq_nonneg _)), fun v => ?_⟩
  refine (abs_scalarDifferential_le_of_scaled_curvature_jet S hq hc x (hjets 1 (by norm_num)) hR
    v).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by linarith only [hd]) hR0) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)

theorem metricScalarAt_backwardSurvivorIncomingMetric_terminal
    (g : SmoothRiemannianMetric ThreeModel (H.stage last).Carrier)
    (hL : L.metric = g.restrictOpen G.terminalRegularOpen)
    (x : H.backwardSurvivorIncomingDomain first last hle G) :
    metricScalarAt (H.backwardSurvivorIncomingMetric first last hle G L s) x =
      metricScalarAt g x.val.val := by
  rw [backwardSurvivorIncomingMetric_terminal, metricScalarAt_localPull, hL,
    metricScalarAt_restrictOpen]
  rfl

theorem curvDerivNormSq_backwardSurvivorIncomingMetric_terminal
    (g : SmoothRiemannianMetric ThreeModel (H.stage last).Carrier)
    (hL : L.metric = g.restrictOpen G.terminalRegularOpen) (j : ℕ)
    (x : H.backwardSurvivorIncomingDomain first last hle G) :
    curvDerivNormSq j (H.backwardSurvivorIncomingMetric first last hle G L s) x =
      curvDerivNormSq j g x.val.val := by
  rw [backwardSurvivorIncomingMetric_terminal, curvDerivNormSq_localPullMetric, hL,
    ← localPullMetric_subtype_val, curvDerivNormSq_localPullMetric]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

theorem exists_derivative_gradient_bounds_of_cap_window_trace
    (Θ : ℝ) (C : ℝ≥0) (hΘ : 0 < Θ) (hΘ1 : Θ < 1) :
    ∃ Cbirth c C' : ℝ, 0 < Cbirth ∧ 0 < c ∧ 0 < C' ∧
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
  obtain ⟨P, Creset, Cbirth, -, -, hCbirth, hbridge⟩ :=
    exists_standard_comparison_of_cap_window_trace.{u} Θ C hΘ hΘ1
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
  refine ⟨Cbirth, c, ((Module.finrank ℝ ThreeSpace : ℝ) ^ 6 * Real.sqrt B +
    2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 4 * B) / c ^ 2 +
    (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt B / (c * Real.sqrt c) + 1, hCbirth, hc,
    by positivity, ?_⟩
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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory
