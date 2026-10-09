import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornFineCutNecks
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornSeparationFrontierScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceConstants
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsingToSlab
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalNeckNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarBall

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.ofReal_lt_riemannianEDistOf_of_gradientBoundBefore
    (L : G.TerminalLimitMetric) {Cgrad : ℝ≥0} {q M A : ℝ} (hqM : q ≤ M) (hM : 0 < M)
    (hA : 0 < A) (hgrad : G.GradientBoundBefore Cgrad q s) (x w : G.terminalRegularOpen)
    (hw : metricScalarAt L.metric w ≤ M) (hx7 : 7 * M ≤ metricScalarAt L.metric x)
    (hx : 18 * A ^ 2 * M ≤ localPropagationRadius Cgrad ^ 2 * metricScalarAt L.metric x) :
    ENNReal.ofReal (2 * A / Real.sqrt (metricScalarAt L.metric x)) <
      riemannianEDistOf L.metric x w := by
  set R := metricScalarAt L.metric x with hRdef
  have hR : 0 < R := by linarith
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hρ0 : 0 < localPropagationRadius Cgrad := localPropagationRadius_pos Cgrad.coe_nonneg
  have h2M : 0 < 2 * M := by linarith
  have hs2M : 0 < Real.sqrt (2 * M) := Real.sqrt_pos.mpr h2M
  have hrad : 3 * A / Real.sqrt R ≤ localPropagationRadius Cgrad / Real.sqrt (2 * M) := by
    rw [div_le_div_iff₀ hsR hs2M]
    have hsq : (3 * A * Real.sqrt (2 * M)) ^ 2 ≤
        (localPropagationRadius Cgrad * Real.sqrt R) ^ 2 := by
      simp only [mul_pow, Real.sq_sqrt h2M.le, Real.sq_sqrt hR.le]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  by_contra hle
  push Not at hle
  have hlt : riemannianEDistOf L.metric x w < ENNReal.ofReal (3 * A / Real.sqrt R) :=
    hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (div_lt_div_of_pos_right (by linarith) hsR))
  have hwlim := (L.tendsto_metricScalarAt w).eventually_lt_const
    (show metricScalarAt L.metric w < 2 * M by linarith)
  have hxlim := (L.tendsto_metricScalarAt x).eventually_const_lt (show 6 * M < R by linarith)
  have hev : ∀ᶠ t in 𝓝[<] s, False := by
    filter_upwards [Ioo_mem_nhdsLT G.lt, hwlim, hxlim, L.eventually_riemannianEDistOf_lt x w hlt]
      with t ht hwt hxt hd
    have hgrad' : ∀ z : P.Carrier, 2 * (2 * M) ≤ G.flow.scalar t z →
        ∀ v : TangentSpace ThreeModel z, |scalarDifferential G.flow t z v| ≤
          2 * (Cgrad : ℝ) * (G.flow.scalar t z * Real.sqrt (G.flow.scalar t z)) *
            Real.sqrt ((G.flow.base.metric t).inner z v v) := by
      intro z hz v
      have hb := hgrad z t ht (by linarith) v
      have hz0 : 0 ≤ G.flow.scalar t z := by linarith
      have hnn : 0 ≤ (Cgrad : ℝ) * G.flow.scalar t z * Real.sqrt (G.flow.scalar t z) *
          Real.sqrt ((G.flow.base.metric t).inner z v v) :=
        mul_nonneg (mul_nonneg (mul_nonneg Cgrad.coe_nonneg hz0) (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _)
      have heq : 2 * (Cgrad : ℝ) * (G.flow.scalar t z * Real.sqrt (G.flow.scalar t z)) *
          Real.sqrt ((G.flow.base.metric t).inner z v v) =
        2 * ((Cgrad : ℝ) * G.flow.scalar t z * Real.sqrt (G.flow.scalar t z) *
          Real.sqrt ((G.flow.base.metric t).inner z v v)) := by ring
      rw [heq]
      linarith
    have hball : (x : P.Carrier) ∈ riemannianClosedBallOf (G.flow.base.metric t) (w : P.Carrier)
        (localPropagationRadius Cgrad / Real.sqrt (2 * M)) := by
      change riemannianEDistOf (G.flow.base.metric t) (w : P.Carrier) (x : P.Carrier) ≤ _
      rw [riemannianEDistOf_comm]
      exact hd.le.trans (ENNReal.ofReal_le_ofReal hrad)
    have hwt' : G.flow.scalar t (w : P.Carrier) ≤ 2 * M := hwt.le
    have h3 := scalar_le_on_ball_of_gradient_bound G.flow Cgrad.coe_nonneg h2M hgrad' hwt' hball
    have hxt' : 6 * M < G.flow.scalar t (x : P.Carrier) := hxt
    linarith
  obtain ⟨t, ht⟩ := hev.exists
  exact ht

theorem TerminalLimitMetric.exists_normalizedNeck_of_eventually_strongNeck
    (L : G.TerminalLimitMetric) {Ctime : ℝ≥0} {q : ℝ} (hq : 0 < q)
    (hderiv : G.DerivativeBoundBefore Ctime q s) {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi)
    (hpinch : Perelman.PhiAlmostNonnegative G.flow (Ico a s) phi)
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x) {εc : ℝ} (hεc : 0 < εc)
    (hεc2 : εc < 1 / 2)
    (hev : ∀ᶠ τ in 𝓝[<] s, Nonempty (FiniteHorn.StrongNeck G.flow (εc / 8) x.1 τ)) :
    ∃ N : NormalizedNeck L.metric εc (⌊εc⁻¹⌋₊ + 1), N.center = x := by
  obtain ⟨τs, hτs⟩ := (𝓝[<] s).exists_seq_tendsto
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hτs.eventually hev)
  have hτ' : Tendsto (fun n => τs (n + n₀)) atTop (𝓝[<] s) :=
    hτs.comp (tendsto_add_atTop_nat n₀)
  have hinv2 : 2 < εc⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) hεc]
    linarith
  have hinv : (εc / 8)⁻¹ = 8 * εc⁻¹ := by
    rw [inv_div, div_eq_mul_inv]
  have hfit : εc⁻¹ + 1 ≤ (εc / 8)⁻¹ := by
    rw [hinv]
    linarith
  have hk : ⌊εc⁻¹⌋₊ + 1 ≤ ⌈(εc / 8)⁻¹⌉₊ := by
    have h1 : ((⌊εc⁻¹⌋₊ : ℕ) : ℝ) + 1 ≤ ((⌈(εc / 8)⁻¹⌉₊ : ℕ) : ℝ) := by
      have hf := Nat.floor_le (inv_nonneg.mpr hεc.le)
      have hc' := Nat.le_ceil ((εc / 8)⁻¹)
      linarith
    exact_mod_cast h1
  obtain ⟨n, N, hN, -, -⟩ := (L.eventually_normalizedNeck_of_strongNecks_of_scalar_control hτ'
    hq (fun y t ht hy => hderiv y t ht hy) hphi hpinch x hx hεc (by linarith) (by linarith)
    hfit _ hk (fun n => (hn₀ (n + n₀) (by omega)).some)).exists
  exact ⟨N, hN⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

theorem exists_terminal_scalar_bound_on_ball_of_final_slab :
    ∃ εcone : ℝ, 0 < εcone ∧ ∀ (κ C1 C2 : ℝ), 0 < κ → ∀ (Ctime Cgrad : ℝ≥0) {phi : ℝ → ℝ},
      Perelman.AdmissiblePinchingFunction phi → ∀ ε : ℝ, ε ≤ εcone → ∀ A : ℝ, 0 < A →
      ∃ Q Λ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ (H : RetainedCoreHistory.{u})
        (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (L : G.TerminalLimitMetric)
        (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount)) {q ρ : ℝ}, 1 ≤ q → 0 < ρ →
        H.EventSlabsDerivative Ctime q (Fin.last H.eventCount) →
        G.DerivativeBoundBefore Ctime q s → G.GradientBoundBefore Cgrad q s →
        H.EventSlabsPinched phi →
        Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
        G.SpatiallyCanonicalBefore ε C1 C2 q s →
        (∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
          H.TerminalNoncollapsedBefore hend G hG κ ρ t₀) →
        ∀ x : G.terminalRegularOpen, 2 * Λ * q ≤ metricScalarAt L.metric x →
          2 * Λ ^ 2 ≤ ρ ^ 2 * metricScalarAt L.metric x →
          2 * Λ < metricScalarAt L.metric x * (s - H.time (Fin.last H.eventCount)) →
          ∀ z ∈ riemannianBallOf L.metric x (5 * A / Real.sqrt (metricScalarAt L.metric x)),
            metricScalarAt L.metric z ≤ 2 * Q * metricScalarAt L.metric x := by
  refine ⟨coneAccuracy, coneAccuracy_pos, fun κ C1 C2 hκ Ctime Cgrad phi hphi ε hε A hA => ?_⟩
  obtain ⟨Q, Λ, hQ1, hΛ1, hQ⟩ :=
    exists_scalar_bound_at_distance_of_final_slab_window_of_le_coneAccuracy.{u} hε κ C1 C2 hκ
      Ctime Cgrad hphi (6 * A) (by positivity)
  refine ⟨Q, Λ, hQ1, hΛ1, ?_⟩
  intro H hend s G L hG q ρ hq1 hρ hderivH hderivG hgradG hpinchH hpinchG hcan hnc x hxq
    hxρ hxwin z hz
  set R := metricScalarAt L.metric x with hRdef
  have hR : 0 < R := by nlinarith
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hgap : 2 * Λ / R < s - H.time (Fin.last H.eventCount) :=
    (div_lt_iff₀ hR).mpr (by linarith)
  have hscal := Metric.tendsto_nhds.mp (L.tendsto_metricScalarAt x) (R / 10) (by positivity)
  apply le_of_tendsto (L.tendsto_metricScalarAt z)
  filter_upwards [hscal, L.eventually_riemannianEDistOf_lt x z hz,
    Ioo_mem_nhdsLT (show H.time (Fin.last H.eventCount) + 2 * Λ / R < s by linarith)]
    with t ht hdt hlate
  rw [Real.dist_eq] at ht
  have hts : t < s := hlate.2
  have hΛR : 0 < 2 * Λ / R := by positivity
  have hT : H.time (Fin.last H.eventCount) < t := by linarith [hlate.1]
  have hRt1 := abs_lt.mp ht
  set Rt := metricScalarAt (G.flow.base.metric t) (x : (H.stage (Fin.last H.eventCount)).Carrier)
    with hRt
  have hRtlo : 9 / 10 * R ≤ Rt := by linarith [hRt1.1]
  have hRthi : Rt ≤ 11 / 10 * R := by linarith [hRt1.2]
  have hRtpos : 0 < Rt := by linarith
  let S := G.closedPrefix t hT hts
  have hΛq : Λ * q < S.flow.scalar t x.1 := by
    change Λ * q < Rt
    linarith
  have hwin : H.time (Fin.last H.eventCount) ≤ t - Λ / S.flow.scalar t x.1 := by
    change H.time (Fin.last H.eventCount) ≤ t - Λ / Rt
    have hdiv : Λ / Rt ≤ 2 * Λ / R := by
      rw [div_le_div_iff₀ hRtpos hR]
      nlinarith
    linarith [hlate.1]
  have hρt : Λ ≤ ρ * Real.sqrt (S.flow.scalar t x.1) := by
    change Λ ≤ ρ * Real.sqrt Rt
    have hsq : Λ ^ 2 ≤ (ρ * Real.sqrt Rt) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hRtpos.le]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  have hzball : z.1 ∈ riemannianBallOf (S.flow.base.metric t) x.1
      (6 * A / Real.sqrt (S.flow.scalar t x.1)) := by
    change riemannianEDistOf (G.flow.base.metric t) x.1 z.1 <
      ENNReal.ofReal (6 * A / Real.sqrt Rt)
    have hsRt : 0 < Real.sqrt Rt := Real.sqrt_pos.mpr hRtpos
    have hsqrt : Real.sqrt Rt ≤ 6 / 5 * Real.sqrt R := by
      have hsq : Real.sqrt Rt ^ 2 ≤ (6 / 5 * Real.sqrt R) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hRtpos.le, Real.sq_sqrt hR.le]
        nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
    have hrad : 5 * A / Real.sqrt R ≤ 6 * A / Real.sqrt Rt := by
      rw [div_le_div_iff₀ hsR hsRt]
      nlinarith
    exact hdt.trans_le (ENNReal.ofReal_le_ofReal hrad)
  have hball := hQ H hend S hG x.1 q ρ hq1 hΛq hwin
    (fun y hy => hcan y t ⟨hT, hts⟩ hy) hderivH
    (fun y t' ht' hy => hderivG y t' ⟨ht'.1, ht'.2.trans hts⟩ hy)
    (fun y t' ht' hy => hgradG y t' ⟨ht'.1, ht'.2.trans hts⟩ hy) hpinchH
    (fun t' ht' => hpinchG t' ⟨ht'.1, ht'.2.trans hts⟩)
    (fun T hT' hTs hTle => hnc t ⟨hT, hts⟩ T hT' (hTs.trans hts) hTle) hρt z.1 hzball
  change metricScalarAt (G.flow.base.metric t) z.1 ≤ Q * Rt at hball
  change metricScalarAt (G.flow.base.metric t) z.1 ≤ 2 * Q * R
  nlinarith

theorem eventually_strongNeck_of_terminal_window
    (H : RetainedCoreHistory.{u}) (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (L : G.TerminalLimitMetric)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) {κ ρ δ Q₀ θ : ℝ} (hκ : 0 < κ) {phi : ℝ → ℝ}
    (hpinch : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi)
    (hnc : ∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
      H.TerminalNoncollapsedBefore hend G hG κ ρ t₀)
    (x : G.terminalRegularOpen) (hθ : 0 < θ) (hR : 0 < metricScalarAt L.metric x)
    (hQ₀ : 2 * Q₀ ≤ metricScalarAt L.metric x)
    (hlong : 4 * θ ≤ metricScalarAt L.metric x * (s - H.time (Fin.last H.eventCount)))
    (hev : ∀ᶠ τ in 𝓝[<] s, Q₀ ≤ G.flow.scalar τ x.1 →
      H.time (Fin.last H.eventCount) ≤ τ - θ / G.flow.scalar τ x.1 →
      Perelman.PhiAlmostNonnegative G.flow (Icc (τ - θ / G.flow.scalar τ x.1) τ) phi →
      (∀ (τ' : (RealTimeInterval.closedOpen _ s G.lt).FlowTime)
        (B : Perelman.FlowMetricBall G.flow τ'),
        τ - θ / G.flow.scalar τ x.1 ≤ τ' → (τ' : ℝ) ≤ τ → B.radius ≤ ρ →
          B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed κ) →
      Nonempty (FiniteHorn.StrongNeck G.flow δ x.1 τ)) :
    ∀ᶠ τ in 𝓝[<] s, Nonempty (FiniteHorn.StrongNeck G.flow δ x.1 τ) := by
  set R := metricScalarAt L.metric x with hRdef
  have hlate : H.time (Fin.last H.eventCount) + 2 * θ / R < s := by
    have h : 2 * θ / R < s - H.time (Fin.last H.eventCount) := by
      rw [div_lt_iff₀ hR]
      linarith
    linarith
  have hscal := Metric.tendsto_nhds.mp (L.tendsto_metricScalarAt x) (R / 10) (by positivity)
  filter_upwards [hev, hscal, Ioo_mem_nhdsLT hlate] with τ h hτ hl
  rw [Real.dist_eq] at hτ
  have hτ1 := abs_lt.mp hτ
  have hRτlo : 9 / 10 * R ≤ G.flow.scalar τ x.1 := by
    change 9 / 10 * R ≤ metricScalarAt (G.flow.base.metric τ) x.1
    linarith [hτ1.1]
  have hRτpos : 0 < G.flow.scalar τ x.1 := by linarith
  have hθ' : θ / G.flow.scalar τ x.1 ≤ 2 * θ / R := by
    rw [div_le_div_iff₀ hRτpos hR]
    nlinarith
  have hwin : H.time (Fin.last H.eventCount) ≤ τ - θ / G.flow.scalar τ x.1 := by
    linarith [hl.1]
  have hat : H.time (Fin.last H.eventCount) < τ :=
    lt_of_le_of_lt hwin (sub_lt_self _ (div_pos hθ hRτpos))
  exact h (by linarith) hwin (fun t ht => hpinch t ⟨hwin.trans ht.1, ht.2.trans_lt hl.2⟩)
    (fun τ' B _ hτ' hr hB => H.isKappaNoncollapsed_of_terminalNoncollapsedBefore hend G hG hκ
      (hnc τ ⟨hat, hl.2⟩) τ' B hτ' hr hB)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

private theorem long_slab_threshold_bounds {Λb Q₀ A ρ ρ0 θB M R Qc T : ℝ} (hΛb : 1 ≤ Λb)
    (hQ₀ : 0 < Q₀) (hρ : 0 < ρ) (hρ0 : 0 < ρ0) (hM1 : 1 ≤ M) (hT : 0 < T)
    (hK : (16 + 2 * Λb + 2 * Λb ^ 2 / ρ ^ 2 + 2 * Q₀ + 18 * A ^ 2 / ρ0 ^ 2) * M ≤ Qc)
    (hQR : Qc ≤ R) (hlong : 2 * (2 * (Λb + θB)) ≤ Qc * T) :
    16 * M ≤ R ∧ 2 * Λb * M ≤ R ∧ 2 * Λb ^ 2 ≤ ρ ^ 2 * R ∧ 2 * Q₀ ≤ R ∧
      18 * A ^ 2 * M ≤ ρ0 ^ 2 * R ∧ 4 * (Λb + θB) ≤ R * T := by
  have hM0 : 0 ≤ M := by linarith
  have hX : 0 ≤ 2 * Λb ^ 2 / ρ ^ 2 := by positivity
  have hY : 0 ≤ 18 * A ^ 2 / ρ0 ^ 2 := by positivity
  have hexp : (16 + 2 * Λb + 2 * Λb ^ 2 / ρ ^ 2 + 2 * Q₀ + 18 * A ^ 2 / ρ0 ^ 2) * M =
      16 * M + 2 * Λb * M + 2 * Λb ^ 2 / ρ ^ 2 * M + 2 * Q₀ * M + 18 * A ^ 2 / ρ0 ^ 2 * M := by
    ring
  rw [hexp] at hK
  have hXM : 2 * Λb ^ 2 / ρ ^ 2 ≤ 2 * Λb ^ 2 / ρ ^ 2 * M := le_mul_of_one_le_right hX hM1
  have hYM : 0 ≤ 18 * A ^ 2 / ρ0 ^ 2 * M := mul_nonneg hY hM0
  have hΛM : 0 ≤ 2 * Λb * M := mul_nonneg (by linarith) hM0
  have hQM : 2 * Q₀ ≤ 2 * Q₀ * M := le_mul_of_one_le_right (by linarith) hM1
  refine ⟨by linarith, by linarith, ?_, by linarith, ?_, ?_⟩
  · have h : 2 * Λb ^ 2 / ρ ^ 2 ≤ R := by linarith
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  · have h : 18 * A ^ 2 / ρ0 ^ 2 * M ≤ R := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h
    linarith
  · have h := mul_le_mul_of_nonneg_right hQR hT.le
    linarith

theorem exists_fineCutNecks_of_long_terminal_slab :
    ∃ eta εcone : ℝ, 0 < eta ∧ 0 < εcone ∧
    ∀ {κ ρ : ℝ}, 0 < κ → 0 < ρ → ∀ (C1 C2 : ℝ) (Ctime Cgrad : ℝ≥0) {phi : ℝ → ℝ},
      Perelman.AdmissiblePinchingFunction phi → ∀ εbar : ℝ, εbar ≤ εcone →
    ∀ {εc : ℝ}, 0 < εc → εc < 1 / 2 →
    ∃ K θ : ℝ, 1 ≤ K ∧ 0 < θ ∧
    ∀ (H : RetainedCoreHistory.{u})
      (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (L : G.TerminalLimitMetric) (hsing : G.SingularEndpoint) (parameters : CutoffParameters)
      (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
        H.initialMetric (Fin.last H.eventCount)) (q : ℝ),
      H.EventSlabsDerivative Ctime q (Fin.last H.eventCount) →
      G.DerivativeBoundBefore Ctime q s → G.GradientBoundBefore Cgrad q s →
      H.EventSlabsPinched phi →
      Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
      G.SpatiallyCanonicalBefore εbar C1 C2 q s →
      (∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
        H.TerminalNoncollapsedBefore hend G hG κ ρ t₀) →
      ∀ {ε Λ : ℝ} (P : TerminalCorePresentation
        { stage := H.stage (Fin.last H.eventCount)
          startTime := H.time (Fin.last H.eventCount)
          endTime := s
          startTime_nonneg := H.toHistory.time_nonneg (Fin.last H.eventCount)
          startTime_lt_endTime := G.lt
          slab := G
          terminal := L
          singular := hsing
          parameters := parameters } ε Λ), ε ≤ eta →
      ∀ Qc : ℝ, K * max (Λ * (P.coreRadius ^ 2)⁻¹) (max q 1) ≤ Qc →
        2 * θ ≤ Qc * (s - H.time (Fin.last H.eventCount)) → P.FineCutNecks εc Qc := by
  obtain ⟨eta, heta, hthr⟩ :=
    exists_strongNeck_threshold_of_horn_point_at_slice_of_frontier_scalar_lt.{u}
  obtain ⟨εcone, hεcone, hballs⟩ :=
    RetainedCoreHistory.exists_terminal_scalar_bound_on_ball_of_final_slab.{u}
  refine ⟨eta, εcone, heta, hεcone, ?_⟩
  intro κ ρ hκ hρ C1 C2 Ctime Cgrad phi hphi εbar hεbar εc hεc hεc2
  obtain ⟨A, Q₀, θB, hA, hQ₀, hθB, hstrong⟩ :=
    hthr (delta := εc / 8) (by positivity) (by linarith) hκ hρ hphi
  obtain ⟨Qb, Λb, hQb, hΛb, hballH⟩ := hballs κ C1 C2 hκ Ctime Cgrad hphi εbar hεbar A hA
  have hρ0 : 0 < localPropagationRadius Cgrad := localPropagationRadius_pos Cgrad.coe_nonneg
  have hX : 0 ≤ 2 * Λb ^ 2 / ρ ^ 2 := by positivity
  have hY : 0 ≤ 18 * A ^ 2 / localPropagationRadius Cgrad ^ 2 := by positivity
  refine ⟨16 + 2 * Λb + 2 * Λb ^ 2 / ρ ^ 2 + 2 * Q₀ + 18 * A ^ 2 / localPropagationRadius Cgrad ^ 2,
    2 * (Λb + θB), by linarith, by positivity, ?_⟩
  intro H hend s G L hsing parameters hG q hderivH hderivG hgradG hpinchH hpinchG hcan hnc
    ε Λ P hε Qc hQc hlong c e x hx hQx
  have hQx' : Qc ≤ metricScalarAt L.metric x := hQx
  have hq1M : max q 1 ≤ max (Λ * (P.coreRadius ^ 2)⁻¹) (max q 1) := le_max_right _ _
  have hM1 : 1 ≤ max (Λ * (P.coreRadius ^ 2)⁻¹) (max q 1) := (le_max_right q 1).trans hq1M
  have hΛM : Λ * (P.coreRadius ^ 2)⁻¹ ≤ max (Λ * (P.coreRadius ^ 2)⁻¹) (max q 1) :=
    le_max_left _ _
  have hmono : q ≤ max q 1 := le_max_left q 1
  obtain ⟨h16, hΛbM, hΛρ, hQ₀R, hAR, hlongR⟩ := long_slab_threshold_bounds hΛb hQ₀ hρ hρ0 hM1
    (sub_pos.mpr G.lt) hQc hQx' hlong
  have hc : c ∈ P.component := by
    by_contra h
    exact (P.hornIndex_empty c h).false e
  obtain ⟨δN, kN, N, hNx, hδN, hkN⟩ := P.horn_spatial_neck c e x hx
  subst hNx
  have hR : 0 < metricScalarAt L.metric N.center := by linarith only [h16, hM1]
  have hscale : N.scale = metricScalarAt L.metric N.center := N.scale_scalar
  have hfs : ∀ w ∈ frontier (P.core c), 2 * metricScalarAt L.metric w < N.scale := by
    intro w hw
    have h : metricScalarAt L.metric w ≤ Λ * (P.coreRadius ^ 2)⁻¹ := P.frontier_scalar_le c hc hw
    rw [hscale]
    linarith only [h, hΛM, h16, hM1]
  have hfd : ∀ w ∈ frontier (P.core c), ENNReal.ofReal
      (2 * A / Real.sqrt (metricScalarAt L.metric N.center)) <
        riemannianEDistOf L.metric N.center w := by
    intro w hw
    have h : metricScalarAt L.metric w ≤ Λ * (P.coreRadius ^ 2)⁻¹ := P.frontier_scalar_le c hc hw
    exact L.ofReal_lt_riemannianEDistOf_of_gradientBoundBefore
      ((le_max_left q 1).trans hq1M) (by linarith only [hM1]) hA hgradG N.center w
      (h.trans hΛM) (by linarith only [h16, hM1]) hAR
  have hΛq : 2 * Λb * max q 1 ≤ metricScalarAt L.metric N.center :=
    (mul_le_mul_of_nonneg_left hq1M (by linarith only [hΛb])).trans hΛbM
  have hbd := hballH H hend G L hG (q := max q 1) (le_max_right _ _) hρ
    (fun j hj y t ht hy => hderivH j hj y t ht (hmono.trans_lt hy))
    (fun y t ht hy => hderivG y t ht (hmono.trans_lt hy))
    (fun y t ht hy => hgradG y t ht (hmono.trans_lt hy)) hpinchH hpinchG
    (fun y t ht hy => hcan y t ht (hmono.trans_lt hy)) hnc N.center hΛq hΛρ
    (by linarith only [hlongR, hθB, hΛb])
  have hev := hstrong P hε c hc e N hδN hkN (interior_subset hx) hfs hfd hbd
  have hev2 := H.eventually_strongNeck_of_terminal_window hend G L hG hκ hpinchG hnc N.center hθB
    hR hQ₀R (by linarith only [hlongR, hΛb]) hev
  obtain ⟨Nf, hNf⟩ := L.exists_normalizedNeck_of_eventually_strongNeck
    (lt_of_lt_of_le one_pos (le_max_right q 1))
    (fun y t ht hy => hderivG y t ht (hmono.trans_lt hy)) hphi hpinchG N.center hR hεc hεc2 hev2
  exact ⟨εc, _, Nf, hNf, le_rfl, le_rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
