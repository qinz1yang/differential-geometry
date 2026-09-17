import DifferentialGeometry.Analysis.Integration.Measure.LocalRestriction
import DifferentialGeometry.Analysis.Integration.LpNorm

noncomputable section

open MeasureTheory Set Manifold
open scoped ENNReal ContDiff Manifold

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ E)) → ℝ)

theorem exists_integral_sq_chartDensity_mul_chartInverse_le
    (q : SmoothRiemannianMetric I M) (α : M) {Ω : Set EuStd}
    (hΩ : MeasurableSet Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := E) '' (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ F : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) q),
        let x := fun z => (extChartAt I α).symm ((toEuclidean (E := E)).symm z)
        MemLp (fun z => chartDensity q α (x z) * F (x z)) 2 (volume.restrict Ω) ∧
          (∫ z in Ω, (chartDensity q α (x z) * F (x z)) ^ 2) ≤ C * ‖F‖ ^ 2 := by
  let e := toEuclidean (E := E)
  let x := fun z => (extChartAt I α).symm (e.symm z)
  let ρ := fun z => chartDensity q α (x z)
  have ht {z : EuStd} (hz : z ∈ closure Ω) : e.symm z ∈ (extChartAt I α).target := by
    obtain ⟨y, hy, rfl⟩ := hΩs hz
    simpa only [e, ContinuousLinearEquiv.symm_apply_apply] using hy
  have hxc : ContinuousOn x (closure Ω) :=
    (continuousOn_extChartAt_symm (I := I) α).comp e.symm.continuous.continuousOn
      (fun _ hz => ht hz)
  have hρ : ContinuousOn ρ (closure Ω) := by
    apply (chartDensity_continuousOn q α).comp hxc
    intro z hz
    rw [trivializationAt_baseSet_eq_chartAt_source]
    simpa only [x, extChartAt_source] using (extChartAt I α).map_target (ht hz)
  obtain ⟨B, hB⟩ := hΩc.exists_bound_of_continuousOn hρ
  let A : ℝ := max B 0
  have hρb {z : EuStd} (hz : z ∈ Ω) : ‖ρ z‖ ≤ A :=
    (hB z (subset_closure hz)).trans (le_max_left _ _)
  let R := chartRestrictionLp q α hΩ hΩc hΩs 2
  refine ⟨A ^ 2 * ‖R‖ ^ 2, mul_nonneg (sq_nonneg _) (sq_nonneg _), ?_⟩
  intro F
  dsimp only
  let U := fun z => F (x z)
  have hR : (R F : EuStd → ℝ) =ᵐ[volume.restrict Ω] U :=
    chartRestrictionLp_coeFn q α hΩ hΩc hΩs 2 F
  have hU : MemLp U 2 (volume.restrict Ω) := (Lp.memLp (R F)).ae_eq hR
  have hρU : MemLp (fun z => ρ z * U z) 2 (volume.restrict Ω) := by
    apply hU.of_le_mul (c := A)
      (((hρ.mono subset_closure).aestronglyMeasurable hΩ).mul hU.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem hΩ] with z hz
    change ‖ρ z * U z‖ ≤ A * ‖U z‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hρb hz) (norm_nonneg _)
  refine ⟨hρU, ?_⟩
  have hUsq : (∫ z in Ω, U z ^ 2) ≤ ‖R‖ ^ 2 * ‖F‖ ^ 2 := by
    calc
      _ = ∫ z in Ω, (R F z) ^ 2 := integral_congr_ae (hR.symm.fun_comp (fun r => r ^ 2))
      _ = ‖R F‖ ^ 2 := by
        rw [DifferentialGeometry.Analysis.Integration.integral_sq_eq_l2 (Lp.memLp (R F)),
          ← Lp.norm_def]
      _ ≤ (‖R‖ * ‖F‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (R.le_opNorm F) 2
      _ = _ := mul_pow _ _ _
  calc
    (∫ z in Ω, (ρ z * U z) ^ 2) ≤ A ^ 2 * (∫ z in Ω, U z ^ 2) := by
      rw [← integral_const_mul]
      apply integral_mono_ae hρU.integrable_sq (hU.integrable_sq.const_mul _)
      filter_upwards [ae_restrict_mem hΩ] with z hz
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      calc
        (ρ z) ^ 2 = ‖ρ z‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
        _ ≤ A ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hρb hz) 2
    _ ≤ A ^ 2 * (‖R‖ ^ 2 * ‖F‖ ^ 2) := mul_le_mul_of_nonneg_left hUsq (sq_nonneg _)
    _ = _ := by ring

end DifferentialGeometry.Integral.Measure
