import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Analysis.Sobolev.Manifold.RellichManifold

/-!
# Chart-to-intrinsic L² norm comparison for scalar functions

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)`
modelled on a finite-dimensional real inner-product space `E`, a chart point
`α : M`, and a measurable scalar function `u : M → ℝ`, we provide a uniform
bound

`eLpNorm (chartPushed (chartAtlasPOU I M) α u) 2 (volume.restrict ChTE_α)
  ≤ ENNReal.ofReal C · eLpNorm u 2 (riemannianVolumeMeasure g)`

with `C ≥ 0` depending only on `g` and `α` (in particular, independent of `u`).

The proof chains three existing pieces:

1. `chartPushed (chartAtlasPOU) α u` agrees a.e. on
   `volume.restrict ChTE_α` with the raw chart-push of `ρ_α · u`
   (`chartPushed_eq_chartPushedRaw_pou_ae`).
2. The reverse chart-density bridge
   `eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset`
   applied with `K := tsupport ρ_α ⊆ (chartAt H α).source`.
3. The pointwise bound `|ρ_α(x) · u(x)| ≤ |u(x)|` (using
   `(chartAtlasPOU I M).le_one`), combined with `eLpNorm_mono`, removes the
   partition-of-unity weight from the right-hand side.

The exponent `p = 2` is used here; the structure of the proof would generalise
to any `1 ≤ p < ∞` if needed.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Pointwise bound `|ρ_α(x) · u(x)| ≤ |u(x)|` for the canonical partition of
unity, valid because `0 ≤ ρ_α ≤ 1` everywhere. -/
private lemma abs_pou_mul_le_abs
    [T2Space M] [SigmaCompactSpace M]
    (α : M) (u : M → ℝ) (x : M) :
    |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
        : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x| ≤ |u x| := by
  rw [abs_mul]
  have hρ_nn : 0 ≤ ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).nonneg α x
  have hρ_le : ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ≤ 1 :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M).le_one α x
  have hρ_abs_le_one : |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
      : C^∞⟮I, M; ℝ⟯) : M → ℝ) x| ≤ 1 := by
    rw [abs_of_nonneg hρ_nn]; exact hρ_le
  calc |((DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α
            : C^∞⟮I, M; ℝ⟯) : M → ℝ) x| * |u x|
      ≤ 1 * |u x| := by
        gcongr
    _ = |u x| := one_mul _

/-- For a measurable scalar function `u : M → ℝ` on a closed Riemannian
manifold and any chart point `α`, the L² norm of the
partition-of-unity-weighted chart pushforward of `u` against Lebesgue volume on
the chart target is controlled by the intrinsic L² norm of `u` against the
canonical Riemannian volume measure. The constant `C ≥ 0` depends only on `g`
and `α`. -/
theorem eLpNorm_chartPushed_le_const_mul_eLpNorm_riemannianVolumeMeasure
    [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric I M)
    (α : M)
    (u : M → ℝ) (hu_meas : Measurable u) :
    ∃ C : ℝ, 0 ≤ C ∧
      eLpNorm (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
          (I := I) (M := M)
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M) α u) 2
          ((MeasureTheory.volume :
              Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I) (M := M) α)) ≤
        ENNReal.ofReal C *
          eLpNorm u 2
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) := by
  classical
  set ρ : C^∞⟮I, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I M α with hρ_def
  set Kα : Set M := tsupport ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I M α
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hp_top : (2 : ℝ≥0∞) ≠ ⊤ := by decide
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I) (M := M) g α hKα_compact hKα_sub hp_one hp_top
  refine ⟨C, hC_pos.le, ?_⟩
  set f : M → ℝ := fun x : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x with hf_def
  have hρ_cont : Continuous ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
    (ρ.contMDiff).continuous
  have hf_meas : Measurable f := hρ_cont.measurable.mul hu_meas
  have hf_supp : tsupport f ⊆ Kα := by
    have h_eq : f = (fun x : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x • u x) := by
      funext x; rfl
    rw [h_eq]
    exact tsupport_smul_subset_left
      (f := fun x : M => ((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) (g := u)
  have h_raw_bound :=
    hC_bound (u := f) hf_meas hf_supp
  rw [show DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
        = DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g from rfl]
    at h_raw_bound
  have h_ae :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed_eq_chartPushedRaw_pou_ae
      (I := I) (M := M)
      (ρ := DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)
      α u
  rw [eLpNorm_congr_ae h_ae]
  refine h_raw_bound.trans ?_
  gcongr
  refine eLpNorm_mono (f := f) (g := u) ?_
  intro x
  have h_norm_f : ‖f x‖ = |((ρ : C^∞⟮I, M; ℝ⟯) : M → ℝ) x * u x| := Real.norm_eq_abs _
  have h_norm_u : ‖u x‖ = |u x| := Real.norm_eq_abs _
  rw [h_norm_f, h_norm_u]
  exact abs_pou_mul_le_abs (I := I) (M := M) α u x

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry
