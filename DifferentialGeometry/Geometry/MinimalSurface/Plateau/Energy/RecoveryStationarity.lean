import DifferentialGeometry.Analysis.Integration.Integral.Recovery
import DifferentialGeometry.Analysis.Integration.Integral.ExhaustingBalls
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.RadialStationarity

section

noncomputable section

open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private def radialStress (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (ψ : ℝ → ℝ) (z : ℂ) : ℝ :=
  deriv ψ (Complex.arg z / (2 * Real.pi)) *
    (diskMapDirectionalEnergyDensity g U (fun z => radialDirection z) z -
      diskMapDirectionalEnergyDensity g U
        (fun z => Complex.I * (radialDirection z : ℂ)) z) / 2

private theorem norm_radialStress_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : LipschitzWith C ψ) (z : ℂ) :
    ‖radialStress g U ψ z‖ ≤ (C : ℝ) * diskMapEnergyDensity g U z := by
  let A := diskMapDirectionalEnergyDensity g U (fun z => radialDirection z) z
  let B := diskMapDirectionalEnergyDensity g U (fun z => Complex.I * (radialDirection z : ℂ)) z
  have hA : 0 ≤ A := diskMapDirectionalEnergyDensity_nonneg g U _ z
  have hB : 0 ≤ B := diskMapDirectionalEnergyDensity_nonneg g U _ z
  have hsub : |A - B| ≤ A + B := by rw [abs_le]; constructor <;> linarith
  have hd : |deriv ψ (Complex.arg z / (2 * Real.pi))| ≤ (C : ℝ) :=
    norm_deriv_le_of_lipschitz hψ
  have hb := mul_le_mul hd hsub (abs_nonneg (A - B)) C.coe_nonneg
  rw [diskMapEnergyDensity_eq_radial_add_tangential]
  change ‖deriv ψ _ * (A - B) / 2‖ ≤ (C : ℝ) * ((A + B) / 2)
  rw [Real.norm_eq_abs, abs_div, abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

variable [FiniteDimensional ℝ E]

private theorem integrable_radialStress
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} (hU : Continuous U)
    {μ : Measure ℂ} (hE : Integrable (diskMapEnergyDensity g U) μ)
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : LipschitzWith C ψ) :
    Integrable (radialStress g U ψ) μ := by
  have hA := measurable_diskMapDirectionalEnergyDensity g hU measurable_coe_radialDirection
  have hB := measurable_diskMapDirectionalEnergyDensity g hU
    (measurable_coe_radialDirection.const_mul Complex.I)
  have hd := (measurable_deriv ψ).comp (Complex.measurable_arg.div_const (2 * Real.pi))
  exact (hE.const_mul (C : ℝ)).mono' ((hd.mul (hA.sub hB)).div_const 2).aestronglyMeasurable
    (Eventually.of_forall fun z => norm_radialStress_le g U hψ z)

theorem tendsto_radialDiskEnergyFirstVariation_of_eqOn_exhausting_closedBall
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (q : C(closedDisk, M)) (qn : ℕ → C(closedDisk, M))
    {a : ℕ → ℝ} (ha : ∀ n, a n ≤ 1) (halim : Tendsto a atTop (𝓝 1))
    (hcore : ∀ n, EqOn (diskExtension (qn n)) (diskExtension q) (Metric.closedBall 0 (a n)))
    (hE : IntegrableOn (diskMapEnergyDensity g (diskExtension q)) (Metric.closedBall (0 : ℂ) 1))
    (hEn : ∀ n, IntegrableOn (diskMapEnergyDensity g (diskExtension (qn n)))
      (Metric.closedBall (0 : ℂ) 1))
    (henergy : Tendsto (fun n => riemannianDiskEnergy g (qn n)) atTop
      (𝓝 (riemannianDiskEnergy g q)))
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : LipschitzWith C ψ) :
    Tendsto (fun n => radialDiskEnergyFirstVariation g (qn n) ψ) atTop
      (𝓝 (radialDiskEnergyFirstVariation g q ψ)) := by
  let μ := volume.restrict (Metric.closedBall (0 : ℂ) 1)
  let T := fun n => Metric.closedBall (0 : ℂ) (a n)
  have hrestrict (n : ℕ) : μ.restrict (T n) = volume.restrict (T n) := by
    rw [Measure.restrict_restrict measurableSet_closedBall,
      inter_eq_left.mpr (Metric.closedBall_subset_closedBall (ha n))]
  have hgerm (n : ℕ) : ∀ᵐ z ∂μ.restrict (T n),
      diskExtension (qn n) =ᶠ[𝓝 z] diskExtension q := by
    rw [hrestrict]
    filter_upwards [ae_mem_ball_of_measure_sphere_eq_zero
      (Measure.addHaar_sphere volume (0 : ℂ) (a n))] with z hz
    filter_upwards [Metric.closedBall_mem_nhds_of_mem hz] with w hw
    exact hcore n hw
  have hcoreE (n : ℕ) : diskMapEnergyDensity g (diskExtension (qn n)) =ᵐ[μ.restrict (T n)]
      diskMapEnergyDensity g (diskExtension q) := by
    filter_upwards [hgerm n] with z hz
    unfold diskMapEnergyDensity diskMapPartial
    rw [hz.mfderiv_eq, hz.eq_of_nhds]
    rfl
  have hcoreS (n : ℕ) : radialStress g (diskExtension (qn n)) ψ =ᵐ[μ.restrict (T n)]
      radialStress g (diskExtension q) ψ := by
    filter_upwards [hgerm n] with z hz
    unfold radialStress diskMapDirectionalEnergyDensity
    rw [hz.mfderiv_eq, hz.eq_of_nhds]
    rfl
  have htail : Tendsto (fun n => ∫ z in (T n)ᶜ,
      diskMapEnergyDensity g (diskExtension q) z ∂μ) atTop (𝓝 0) := by
    have hh := tendsto_integral_closedBall_sdiff_of_tendsto_radius hE
      (Measure.addHaar_sphere volume (0 : ℂ) 1) halim
    convert hh using 1
    funext n
    rw [Measure.restrict_restrict measurableSet_closedBall.compl]
    congr 2
    exact inter_comm _ _
  exact tendsto_integral_of_eq_on_core_of_integral_tendsto
    (fun _ => measurableSet_closedBall) hE hEn
    (integrable_radialStress g (q.continuous.comp diskRetraction_lipschitz.continuous) hE hψ)
    (fun n => integrable_radialStress g
      ((qn n).continuous.comp diskRetraction_lipschitz.continuous) (hEn n) hψ)
    (Eventually.of_forall fun z => norm_radialStress_le g _ hψ z)
    (fun n => Eventually.of_forall fun z => norm_radialStress_le g _ hψ z)
    hcoreE hcoreS henergy htail

variable [T3Space M]

theorem radialDiskEnergyFirstVariation_eq_zero_of_exhausting_recovery
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : freeLoop M}
    (q : C(closedDisk, M)) (qn : ℕ → C(closedDisk, M))
    (hqn : ∀ n, qn n ∈ weaklyMonotoneDiskCompetitors g γ)
    {a : ℕ → ℝ} (ha : ∀ n, a n ≤ 1) (halim : Tendsto a atTop (𝓝 1))
    (hcore : ∀ n, EqOn (diskExtension (qn n)) (diskExtension q) (Metric.closedBall 0 (a n)))
    (hE : IntegrableOn (diskMapEnergyDensity g (diskExtension q)) (Metric.closedBall (0 : ℂ) 1))
    (henergy : Tendsto (fun n => riemannianDiskEnergy g (qn n)) atTop
      (𝓝 (riemannianDiskEnergy g q)))
    (hmin : riemannianDiskEnergy g q = sInf
      ((fun u : C(closedDisk, M) => riemannianDiskEnergy g u) '' weaklyMonotoneDiskCompetitors g γ))
    {ψ : ℝ → ℝ} {C : ℝ≥0} (hψ : Differentiable ℝ ψ)
    (hψLip : LipschitzWith C ψ) (hper : Function.Periodic ψ 1) :
    radialDiskEnergyFirstVariation g q ψ = 0 := by
  have hEn (n : ℕ) : IntegrableOn (diskMapEnergyDensity g (diskExtension (qn n)))
      (Metric.closedBall (0 : ℂ) 1) := by
    obtain ⟨L, hL⟩ := (hqn n).2
    exact integrable_diskMapEnergyDensity g hL
  have htransfer := tendsto_radialDiskEnergyFirstVariation_of_eqOn_exhausting_closedBall
    g q qn ha halim hcore hE hEn henergy hψLip
  have hseq := tendsto_radialDiskEnergyFirstVariation_of_minimizing_sequence
    g hqn (by rwa [← hmin]) hψ hψLip hper
  exact tendsto_nhds_unique htransfer hseq

end DifferentialGeometry.Geometry

end

end
