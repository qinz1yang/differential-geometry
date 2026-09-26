import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceConstants
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryExtendAt
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  (SpatialCanonicalWitness)
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private exists_riemannianEDistOf_lt_of_mem_Icc_scalar from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceConstants

universe u

namespace RetainedCoreHistory

theorem exists_scalar_bounds_at_distance_of_final_slab_window_of_le_coneAccuracy
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) (κ C1 C2 : ℝ) (hκ : 0 < κ) (Ctime Cgrad : ℝ≥0)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) :
    ∀ A : ℝ, 0 < A →
      ∃ Q Λ : ℝ, 1 ≤ Q ∧ 1 ≤ Λ ∧
      ∀ (P₀ : OrientedThreeStage.{u}) (H : RetainedCoreHistory P₀)
        (hend : H.time (Fin.last H.eventCount) = H.horizon) {t : ℝ}
        (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) t)
        (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
          H.initialMetric (Fin.last H.eventCount))
        (y : (H.stage (Fin.last H.eventCount)).Carrier) (q ρ : ℝ),
        1 ≤ q → Λ * q < S.flow.scalar t y →
        H.time (Fin.last H.eventCount) ≤ t - Λ / S.flow.scalar t y →
        (∀ x, q < S.flow.scalar t x →
          ∃ W : SpatialCanonicalWitness (S.flow.base.metric t) ε C1 C2 x,
            W.capTubeHasNeckChart ε) →
        H.EventSlabsDerivative Ctime q (Fin.last H.eventCount) →
        (S.restrictIncoming le_rfl S.lt le_rfl).DerivativeBoundBefore Ctime q t →
        (S.restrictIncoming le_rfl S.lt le_rfl).GradientBoundBefore Cgrad q t →
        H.EventSlabsPinched phi →
        Perelman.PhiAlmostNonnegative (S.restrictIncoming le_rfl S.lt le_rfl).flow
          (Ico (H.time (Fin.last H.eventCount)) t) phi →
        H.TerminalNoncollapsedBefore hend (S.restrictIncoming le_rfl S.lt le_rfl) hS κ ρ t →
        Λ ≤ ρ * Real.sqrt (S.flow.scalar t y) →
        ∀ z ∈ riemannianBallOf (S.flow.base.metric t) y (A / Real.sqrt (S.flow.scalar t y)),
          Q⁻¹ * S.flow.scalar t y ≤ S.flow.scalar t z ∧
            S.flow.scalar t z ≤ Q * S.flow.scalar t y := by
  intro A hA
  obtain ⟨Q₁, Λ₁, hQ₁, hΛ₁, hcone⟩ :=
    exists_scalar_bound_at_distance_of_final_slab_window_of_le_coneAccuracy hεle κ C1 C2 hκ
      Ctime Cgrad hphi A hA
  refine ⟨2 * Q₁, 2 * Q₁ * Λ₁, by linarith, by nlinarith, ?_⟩
  intro P₀ H hend t S hS y q ρ hq1 hΛq hwin hW hderiv hfinal hgrad hpinch hpinchF hnc hρ z hz
  have hRy : 0 < S.flow.scalar t y :=
    (mul_pos (mul_pos (by linarith : (0 : ℝ) < 2 * Q₁) (by linarith : (0 : ℝ) < Λ₁))
      (by linarith : (0 : ℝ) < q)).trans hΛq
  have hΛle : Λ₁ ≤ 2 * Q₁ * Λ₁ := by nlinarith
  have hup := hcone P₀ H hend S hS y q ρ hq1 (by nlinarith)
    (hwin.trans (sub_le_sub_left (div_le_div_of_nonneg_right hΛle hRy.le) _)) hW hderiv hfinal
    hgrad hpinch hpinchF hnc (hΛle.trans hρ) z hz
  refine ⟨?_, hup.trans (by nlinarith)⟩
  by_contra hlow
  rw [not_le] at hlow
  have hQ0 : 0 < 2 * Q₁ := by linarith
  set c := (2 * Q₁)⁻¹ * S.flow.scalar t y with hcdef
  have hc0 : 0 < c := by positivity
  have hcle : c ≤ S.flow.scalar t y := by
    rw [hcdef]
    have : (2 * Q₁)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    nlinarith
  have hcont : Continuous (S.flow.scalar t) :=
    (metricScalar_smooth (S.flow.base.metric t)).continuous
  have hzy : riemannianEDistOf (S.flow.base.metric t) z y <
      ENNReal.ofReal (A / Real.sqrt (S.flow.scalar t y)) := by
    rw [riemannianEDistOf_comm]
    exact hz
  obtain ⟨w, hw, hwy⟩ := exists_riemannianEDistOf_lt_of_mem_Icc_scalar (S.flow.base.metric t)
    hcont hzy ⟨hlow.le, hcle⟩
  have hρ0 : 0 < ρ := by
    by_contra hρn
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hρn) (Real.sqrt_nonneg (S.flow.scalar t y))
    nlinarith
  have hsq : Real.sqrt (S.flow.scalar t y) / (2 * Q₁) ≤ Real.sqrt c := by
    rw [← Real.sqrt_sq hQ0.le, ← Real.sqrt_div' _ (sq_nonneg _)]
    · apply Real.sqrt_le_sqrt
      rw [hcdef, div_le_iff₀ (by positivity)]
      have : (2 * Q₁)⁻¹ * (2 * Q₁) ^ 2 = 2 * Q₁ := by field_simp
      nlinarith
  have hΛw : Λ₁ ≤ ρ * Real.sqrt (S.flow.scalar t w) := by
    rw [hw]
    calc Λ₁ = 2 * Q₁ * Λ₁ / (2 * Q₁) := by field_simp
      _ ≤ ρ * Real.sqrt (S.flow.scalar t y) / (2 * Q₁) :=
          div_le_div_of_nonneg_right hρ hQ0.le
      _ = ρ * (Real.sqrt (S.flow.scalar t y) / (2 * Q₁)) := by ring
      _ ≤ ρ * Real.sqrt c := mul_le_mul_of_nonneg_left hsq hρ0.le
  have hqw : Λ₁ * q < S.flow.scalar t w := by
    rw [hw, hcdef, lt_inv_mul_iff₀ hQ0]
    nlinarith
  have hwinw : H.time (Fin.last H.eventCount) ≤ t - Λ₁ / S.flow.scalar t w := by
    rw [hw, hcdef]
    have : Λ₁ / ((2 * Q₁)⁻¹ * S.flow.scalar t y) = 2 * Q₁ * Λ₁ / S.flow.scalar t y := by
      field_simp
    rw [this]
    exact hwin
  have hyw : y ∈ riemannianBallOf (S.flow.base.metric t) w
      (A / Real.sqrt (S.flow.scalar t w)) := by
    change riemannianEDistOf (S.flow.base.metric t) w y < _
    rw [hw]
    refine hwy.trans_le (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_left hA.le (Real.sqrt_pos.mpr hc0) (Real.sqrt_le_sqrt hcle)
  have hback := hcone P₀ H hend S hS w q ρ hq1 hqw hwinw hW hderiv hfinal hgrad hpinch hpinchF
    hnc hΛw y hyw
  rw [hw, hcdef] at hback
  have : Q₁ * ((2 * Q₁)⁻¹ * S.flow.scalar t y) = S.flow.scalar t y / 2 := by
    field_simp
  linarith

theorem eventually_scalar_bounds_at_distance_extendAt_of_le_coneAccuracy
    {ε : ℝ} (hεle : ε ≤ coneAccuracy) {κ C1 C2 ρ qcan : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ)
    {Ctime Cgrad : ℝ≥0} {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi)
    {P₀ : ℕ → OrientedThreeStage.{u}} (H Hext : ∀ n, RetainedCoreHistory (P₀ n))
    (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon) {s τ : ℕ → ℝ}
    (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
      ((H n).time (Fin.last (H n).eventCount)) (s n))
    (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
      (H n).initialMetric (Fin.last (H n).eventCount))
    (hat : ∀ n, (H n).time (Fin.last (H n).eventCount) < τ n) (hτs : ∀ n, τ n < s n)
    (hext : ∀ n, Hext n = (H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n))
    (t : ∀ n, Icc (0 : ℝ) (Hext n).toHistory.horizon) (ht : ∀ n, (t n : ℝ) = τ n)
    (y : ∀ n, ((Hext n).toHistory.stageAt (t n)).Carrier) (R : ℕ → ℝ)
    (hscal : ∀ n, metricScalarAt
      ((Hext n).toHistory.stageMetric ((Hext n).toHistory.activeStage (t n)) (t n)) (y n) = R n)
    (hRlim : Tendsto R atTop atTop)
    (hage : Tendsto (fun n => R n * (τ n - (H n).time (Fin.last (H n).eventCount))) atTop atTop)
    (hwit : ∀ n, (G n).SpatiallyCanonicalBefore ε C1 C2 qcan (s n))
    (hderiv : ∀ n, (H n).EventSlabsDerivative Ctime qcan (Fin.last (H n).eventCount))
    (hderivG : ∀ n, (G n).DerivativeBoundBefore Ctime qcan (s n))
    (hgradG : ∀ n, (G n).GradientBoundBefore Cgrad qcan (s n))
    (hpinch : ∀ n, (H n).EventSlabsPinched phi)
    (hpinchG : ∀ n, Perelman.PhiAlmostNonnegative (G n).flow
      (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi)
    (hncG : ∀ n, (H n).TerminalNoncollapsedBefore (hend n) (G n) (hG n) κ ρ (τ n)) :
    ∀ A : ℝ, 0 < A → ∃ Qlow Qup : ℝ, 0 < Qlow ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          ((Hext n).toHistory.stageMetric ((Hext n).toHistory.activeStage (t n)) (t n)) (y n)
          (A / Real.sqrt (R n)),
        Qlow * R n ≤ metricScalarAt
            ((Hext n).toHistory.stageMetric ((Hext n).toHistory.activeStage (t n)) (t n)) x ∧
          metricScalarAt
            ((Hext n).toHistory.stageMetric ((Hext n).toHistory.activeStage (t n)) (t n)) x ≤
              Qup * R n := by
  intro A hA
  obtain ⟨Q, Λ, hQ1, hΛ1, hcone⟩ :=
    exists_scalar_bounds_at_distance_of_final_slab_window_of_le_coneAccuracy hεle κ C1 C2 hκ
      Ctime Cgrad hphi A hA
  refine ⟨Q⁻¹, Q, by positivity, ?_⟩
  obtain rfl : Hext = fun n => (H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n) :=
    funext hext
  have hsqrt : Tendsto (fun n => Real.sqrt (R n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hRlim
  filter_upwards [hRlim.eventually_gt_atTop (Λ * max qcan 1), hage.eventually_ge_atTop Λ,
    hsqrt.eventually_ge_atTop (Λ / ρ)] with n hn1 hn2 hn3
  have hk : ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage (t n) =
      Fin.last (H n).eventCount :=
    (H n).activeStage_extendHorizon_eq_last _ _ _ (t n) (by rw [ht n]; exact (hat n).le)
  have hsc := hscal n
  revert hsc
  generalize y n = y0
  dsimp only [ObservedHistory.stageAt] at y0 ⊢
  revert y0
  generalize ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.activeStage (t n) =
    k at hk ⊢
  subst hk
  have hm : ((H n).extendAt (hend n) (G n) (hG n) (hat n) (hτs n)).toHistory.stageMetric
      (Fin.last (H n).eventCount) (t n) = (G n).flow.base.metric (t n) :=
    (H n).stageMetric_extendHorizon_last _ _ _ (hat n) (t n)
  rw [hm, ht n]
  intro y0 hy0
  rw [← hy0]
  have hR0 : 0 < R n := lt_of_le_of_lt (by positivity) hn1
  have hq1 : (1 : ℝ) ≤ max qcan 1 := le_max_right _ _
  have hy0' : ((G n).closedPrefix (τ n) (hat n) (hτs n)).flow.scalar (τ n) y0 = R n := hy0
  exact hcone (P₀ n) (H n) (hend n) ((G n).closedPrefix (τ n) (hat n) (hτs n)) (hG n) y0
    (max qcan 1) ρ hq1 (by rw [hy0']; exact hn1)
    (by
      rw [hy0', le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hR0]
      linarith)
    (fun x hx => hwit n x (τ n) ⟨hat n, hτs n⟩ ((le_max_left _ _).trans_lt hx))
    (fun j hj x v hv hx => hderiv n j hj x v hv ((le_max_left _ _).trans_lt hx))
    (fun x v hv hx => hderivG n x v ⟨hv.1, hv.2.trans (hτs n)⟩ ((le_max_left _ _).trans_lt hx))
    (fun x v hv hx => hgradG n x v ⟨hv.1, hv.2.trans (hτs n)⟩ ((le_max_left _ _).trans_lt hx))
    (hpinch n) (fun v hv x => hpinchG n v ⟨hv.1, hv.2.trans (hτs n)⟩ x)
    (fun T hT hTs hTτ => hncG n T hT (hTs.trans (hτs n)) hTτ)
    (by
      rw [hy0']
      have := (div_le_iff₀' hρ).mp hn3
      linarith)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
