import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.ReducedVolume.Monotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.ReducedVolume.LocalUpperBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ReducedVolumeTruncation

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier

private local instance (P : OrientedThreeStage.{u}) : BorelSpace P.Carrier := ⟨rfl⟩

private theorem exp_density_mul_clock_volume_eq {v C κ₀ : ℝ} (hv : 0 < v) :
    Real.exp (-C - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi)) * (κ₀ * v ^ 3) =
      κ₀ * Real.exp (-C) * (4 * Real.pi) ^ (-(3 / 2 : ℝ)) := by
  rw [Real.exp_sub, Real.exp_sub]
  have h4 : (0 : ℝ) < 4 * Real.pi := by positivity
  have hpow : v ^ 3 = Real.exp ((3 / 2 : ℝ) * Real.log (v ^ 2)) := by
    calc
      v ^ 3 = (Real.exp (Real.log v)) ^ 3 := by rw [Real.exp_log hv]
      _ = Real.exp ((3 : ℝ) * Real.log v) := (Real.exp_nat_mul _ 3).symm
      _ = Real.exp ((3 / 2 : ℝ) * Real.log (v ^ 2)) := by
        rw [Real.log_pow]
        congr 1
        ring
  have hpow4 : (4 * Real.pi) ^ (-(3 / 2 : ℝ)) =
      (Real.exp ((3 / 2 : ℝ) * Real.log (4 * Real.pi)))⁻¹ := by
    rw [Real.rpow_def_of_pos h4, ← Real.exp_neg]
    ring_nf
  rw [hpow, hpow4]
  have he1 := (Real.exp_pos ((3 / 2 : ℝ) * Real.log (v ^ 2))).ne'
  have he2 := (Real.exp_pos ((3 / 2 : ℝ) * Real.log (4 * Real.pi))).ne'
  field_simp

theorem exists_test_volume_lower_of_regular_endpoint_block
    (κ₀ C : ℝ) (hκ₀ : 0 < κ₀) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (H : RetainedCoreHistory.{u}) (Bf : ℝ),
        (∀ (j : Fin (H.eventCount + 1)), ∀ s ∈ H.toHistory.stageDomain j,
          ∀ y : (H.stage j).Carrier,
            -Bf ≤ metricScalarAt (H.toHistory.stageMetric j s) y) →
      ∀ (t : Icc (0 : ℝ) H.toHistory.horizon)
        (x : (H.toHistory.stageAt t).Carrier) (ρ v : ℝ),
        0 < v → v ^ 2 ≤ (t : ℝ) → ρ ≤ 2 * v →
        H.toHistory.isParabolicallyRmControlledBall t x ρ →
      let a := projIcc 0 H.horizon H.horizon_nonneg ((t : ℝ) - v ^ 2)
      let first := H.toHistory.activeStage a
      let last := H.toHistory.activeStage t
      ∀ (hle : first ≤ last) (U : Set (H.stage first).Carrier),
        IsOpen U →
        ENNReal.ofReal (κ₀ * v ^ 3) ≤
          riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
            (H.toHistory.stageMetric first ((t : ℝ) - v ^ 2)) U →
        (∀ q ∈ U,
          q ∈ H.toHistory.regularMinimizerEndpoints first last hle t Bf v x ∧
          H.toHistory.regularizedCost first last hle t Bf 0 v x q ≤
            ((2 * C * v : ℝ) : WithTop ℝ)) →
        ENNReal.ofReal (κ * ρ ^ 3) ≤
          riemannianVolumeMeasure ThreeModel (H.toHistory.stageAt t).Carrier
            (H.toHistory.stageMetric last t)
            (riemannianBallOf (H.toHistory.stageMetric last t) x ρ) := by
  classical
  let c : ℝ := κ₀ * Real.exp (-C) * (4 * Real.pi) ^ (-(3 / 2 : ℝ))
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨C₀, hC₀, hupper⟩ := historyReducedVolumeLocalUpperBound_holds.{u}
  obtain ⟨θ, hθ, hθ1, hupperθ⟩ := hupper (c / 2) (half_pos hc)
  refine ⟨c * θ ^ 3 / (16 * C₀), by positivity, ?_⟩
  intro H Bf hfloor t x ρ v hv hvT hρv hball a first last hle U hU hvol hblock
  have hRV : ENNReal.ofReal c ≤ H.reducedVolume last x t v := by
    rw [RetainedCoreHistory.reducedVolume_eq_of_scalar_lower_bound_le hfloor
      last x t v le_rfl hle]
    let μ := riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
      (H.toHistory.stageMetric first ((t : ℝ) - v ^ 2))
    set densityLower := ENNReal.ofReal (Real.exp
      (-C - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi))) with hdensityLower
    have hdens : ∀ q ∈ U, densityLower ≤
        H.toHistory.regularizedDensity first last hle t Bf v x q := by
      intro q hq
      have hcost := (hblock q hq).2
      have hne : H.toHistory.regularizedCost first last hle t Bf 0 v x q ≠ ⊤ :=
        ne_top_of_le_ne_top WithTop.coe_ne_top hcost
      obtain ⟨A, hA⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [H.toHistory.regularizedDensity_eq_exp_of_regularizedCost_eq
        first last hle t Bf hv x q hA.symm, hdensityLower]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hAle : A ≤ 2 * C * v := by
        rw [← hA] at hcost
        exact WithTop.coe_le_coe.mp hcost
      have hdiv : A / (2 * v) ≤ C := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      have hneg : -A / (2 * v) = -(A / (2 * v)) := neg_div _ _
      linarith
    have hsub : U ⊆ H.toHistory.regularMinimizerEndpoints first last hle t Bf v x :=
      fun q hq => (hblock q hq).1
    calc
      ENNReal.ofReal c = densityLower * ENNReal.ofReal (κ₀ * v ^ 3) := by
        rw [hdensityLower, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
          exp_density_mul_clock_volume_eq hv]
      _ ≤ densityLower * μ U := mul_le_mul' le_rfl hvol
      _ = ∫⁻ _ in U, densityLower ∂μ := (setLIntegral_const U densityLower).symm
      _ ≤ ∫⁻ q in U, H.toHistory.regularizedDensity first last hle t Bf v x q ∂μ :=
        lintegral_mono_ae ((ae_restrict_mem hU.measurableSet).mono fun q hq => hdens q hq)
      _ ≤ _ := lintegral_mono_set hsub
  have hρ : 0 < ρ := hball.1
  have hhalfBall := hball.mono_radius H.toHistory (half_pos hρ) (by linarith : ρ / 2 ≤ ρ)
  have hθρ : 0 < θ * (ρ / 2) := mul_pos hθ (half_pos hρ)
  have hθρv : θ * (ρ / 2) ≤ v :=
    (mul_le_of_le_one_left (half_pos hρ).le hθ1).trans (by linarith only [hρv])
  have hmon := historyReducedVolumeMonotone_holds H last x t (θ * (ρ / 2)) v
    (H.toHistory.activeStage_mem t) hθρ hθρv hvT
  have hchain := (hRV.trans hmon).trans (hupperθ H t x (ρ / 2) hhalfBall)
  let V := riemannianVolumeMeasure ThreeModel (H.toHistory.stageAt t).Carrier
    (H.toHistory.stageMetric last t)
    (riemannianBallOf (H.toHistory.stageMetric last t) x (ρ / 2))
  have hsplit : ENNReal.ofReal c = ENNReal.ofReal (c / 2) + ENNReal.ofReal (c / 2) := by
    rw [← ENNReal.ofReal_add (half_pos hc).le (half_pos hc).le]
    congr 1
    ring
  rw [hsplit] at hchain
  have hhalf : ENNReal.ofReal (c / 2) ≤ ENNReal.ofReal (C₀ / (θ * (ρ / 2)) ^ 3) * V :=
    (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hchain
  have hC₀ne : C₀ ≠ 0 := hC₀.ne'
  have hθρ3 : 0 < (θ * (ρ / 2)) ^ 3 := pow_pos hθρ 3
  have hθρ3ne : (θ * (ρ / 2)) ^ 3 ≠ 0 := hθρ3.ne'
  have hreal : c * θ ^ 3 / (16 * C₀) * ρ ^ 3 =
      c / 2 * ((θ * (ρ / 2)) ^ 3 / C₀) := by
    field_simp <;> ring
  have hone : C₀ / (θ * (ρ / 2)) ^ 3 * ((θ * (ρ / 2)) ^ 3 / C₀) = 1 := by
    field_simp
  calc
    ENNReal.ofReal (c * θ ^ 3 / (16 * C₀) * ρ ^ 3) =
        ENNReal.ofReal (c / 2) * ENNReal.ofReal ((θ * (ρ / 2)) ^ 3 / C₀) := by
      rw [hreal, ENNReal.ofReal_mul (half_pos hc).le]
    _ ≤ ENNReal.ofReal (C₀ / (θ * (ρ / 2)) ^ 3) * V *
        ENNReal.ofReal ((θ * (ρ / 2)) ^ 3 / C₀) := mul_le_mul_left hhalf _
    _ = V := by
      rw [mul_comm (ENNReal.ofReal (C₀ / (θ * (ρ / 2)) ^ 3)) V, mul_assoc,
        ← ENNReal.ofReal_mul (div_pos hC₀ hθρ3).le, hone, ENNReal.ofReal_one, mul_one]
    _ ≤ _ := measure_mono (riemannianBallOf_mono _ _ (by linarith : ρ / 2 ≤ ρ))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
