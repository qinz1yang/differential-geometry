import DifferentialGeometry.Analysis.Parabolic.WeakEquation.PartitionOfUnity
import DifferentialGeometry.Analysis.Integration.Measure.Chart.Integrability


noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis

open Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in
private theorem tsupport_time_spatial_derivative_subset
    {K : Set M} (hK : IsClosed K) {f : ℝ × M → ℝ}
    (hfK : ∀ t, Function.support (fun x => f (t, x)) ⊆ K)
    (w : ℝ × M → ℝ)
    (A : ∀ z : ℝ × M, (TangentSpace I z.2 →L[ℝ] ℝ) →L[ℝ] ℝ) (t : ℝ) :
    tsupport (fun x => w (t, x) * deriv (fun r => f (r, x)) t +
      A (t, x) (mvfderiv I (fun y => f (t, y)) x)) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hxK
  have hz (r : ℝ) : f (r, x) = 0 :=
    Function.notMem_support.mp (fun hf => hxK (hfK r hf))
  have ht : (fun r => f (r, x)) = fun _ => (0 : ℝ) := funext hz
  have heq : (fun y => f (t, y)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hxK] with y hy
    exact Function.notMem_support.mp (fun hf => hy (hfK t hf))
  have hd : mvfderiv I (fun y => f (t, y)) x = 0 := by
    have hmf := heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ))
    simp only [mfderiv_const] at hmf
    rw [mvfderiv, hmf]
    ext v
    change NormedSpace.fromTangentSpace (𝕜 := ℝ) (f (t, x)) 0 = 0
    exact map_zero _
  apply hx
  change w (t, x) * deriv (fun r => f (r, x)) t +
    A (t, x) (mvfderiv I (fun y => f (t, y)) x) = 0
  rw [ht, deriv_const, hd, map_zero, mul_zero, add_zero]

theorem integrable_and_integral_parabolic_residual_nonneg_of_chart_integrals
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate (fun i => (chartAt H i).source))
    (g : ℝ → SmoothRiemannianMetric I M) (μ : Measure ℝ)
    {K : Set M} (hK : IsCompact K) {f : ℝ × M → ℝ}
    (hfK : ∀ t, Function.support (fun x => f (t, x)) ⊆ K)
    (hf : ∀ᵐ t ∂μ, ∀ᵐ x ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) (g t),
      MDifferentiableAt I 𝓘(ℝ) (fun y => f (t, y)) x)
    (w : ℝ × M → ℝ)
    (A : ∀ z : ℝ × M, (TangentSpace I z.2 →L[ℝ] ℝ) →L[ℝ] ℝ) :
    let L := fun (v : ℝ × M → ℝ) (t : ℝ) (x : M) =>
      w (t, x) * deriv (fun r => v (r, x)) t +
        A (t, x) (mvfderiv I (fun y => v (t, y)) x)
    let C := fun (i : M) (t : ℝ) (y : E) =>
      chartDensity (g t) i ((extChartAt I i).symm y) *
        L (fun z => ρ i z.2 * f z) t ((extChartAt I i).symm y)
    (∀ᵐ t ∂μ, ∀ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      Integrable (C i t) ((modelHaar (E := E)).restrict (extChartAt I i).target)) →
    (∀ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      Integrable (fun t => ∫ y in (extChartAt I i).target, C i t y
        ∂(modelHaar (E := E))) μ) →
    (∀ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      0 ≤ ∫ t, ∫ y in (extChartAt I i).target, C i t y
        ∂(modelHaar (E := E)) ∂μ) →
    (∀ᵐ t ∂μ, Integrable (L f t)
      (Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) (g t))) ∧
    Integrable (fun t => ∫ x, L f t x
      ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) (g t)) μ ∧
      0 ≤ ∫ t, ∫ x, L f t x
        ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) (g t) ∂μ := by
  intro L C hchart htime hnonneg
  have hcompact : ∀ᵐ t ∂μ, ∀ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      HasCompactSupport (L (fun z => ρ i z.2 * f z) t) ∧
        tsupport (L (fun z => ρ i z.2 * f z) t) ⊆ (extChartAt I i).source := by
    apply Eventually.of_forall
    intro t i _
    have hsupport : ∀ r, Function.support (fun x => ρ i x * f (r, x)) ⊆
        tsupport (ρ i) ∩ K := by
      intro r x hx
      exact ⟨subset_tsupport _ (left_ne_zero_of_mul hx), hfK r (right_ne_zero_of_mul hx)⟩
    have hs := tsupport_time_spatial_derivative_subset
      (f := fun z : ℝ × M => ρ i z.2 * f z)
      ((isClosed_tsupport (ρ i)).inter hK.isClosed) hsupport w A t
    refine ⟨?_, ?_⟩
    · exact (hK.of_isClosed_subset ((isClosed_tsupport _).inter hK.isClosed)
        inter_subset_right).of_isClosed_subset (isClosed_tsupport _) hs
    · intro x hx
      rw [extChartAt_source]
      exact hρ i (hs hx).1
  have hlocal : ∀ᵐ t ∂μ, ∀ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      Integrable (L (fun z => ρ i z.2 * f z) t)
        (Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) (g t)) := by
    filter_upwards [hcompact, hchart] with t hct hit
    intro i hi
    apply (integrable_riemannianVolumeMeasure_iff_chartDensity_of_tsupport_subset
      (g t) i (hct i hi).1 (hct i hi).2).mpr
    simpa only [smul_eq_mul] using hit i hi
  have htransport (i : M) (hi : i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK) :
      (fun t => ∫ x, L (fun z => ρ i z.2 * f z) t x
        ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) (g t))
        =ᵐ[μ] (fun t => ∫ y in (extChartAt I i).target, C i t y
          ∂(modelHaar (E := E))) := by
    filter_upwards [hcompact, hchart] with t hct hit
    have hm : Integrable (L (fun z => ρ i z.2 * f z) t)
        (chartLocalMeasure (g t) i) := by
      apply (integrable_chartLocalMeasure_iff (g t) i).mpr
      simpa only [smul_eq_mul] using hit i hi
    exact integral_riemannianVolumeMeasure_eq_chartDensity_of_tsupport_subset
      (g t) i (hct i hi).1 (by simpa only [extChartAt_source] using (hct i hi).2)
        hm.aestronglyMeasurable
  have htimeLocal (i : M) (hi : i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK) :
      Integrable (fun t => ∫ x, L (fun z => ρ i z.2 * f z) t x
        ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) (g t)) μ :=
    (htime i hi).congr (htransport i hi).symm
  have hspatial : ∀ᵐ t ∂μ, Integrable (L f t)
      (Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) (g t)) := by
    filter_upwards [hf, hlocal] with t hft hint
    apply (integrable_finsetSum _ hint).congr
    filter_upwards [hft] with x hx
    change (∑ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      (w (t, x) * deriv (fun r => ρ i x * f (r, x)) t +
        A (t, x) (mvfderiv I (fun y => ρ i y * f (t, y)) x))) = L f t x
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      ρ.sum_deriv_mul_fintsupportOn hK hfK (fun _ => subset_univ _) t x,
      ← map_sum, ρ.sum_mvfderiv_mul_fintsupportOn hK (hfK t) (subset_univ _) hx]
  have hs := ρ.integrable_and_integral_integral_time_spatial_derivative_eq_sum_fintsupportOn
    μ (fun t => Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) (g t)) hK hfK
    (fun _ => subset_univ _) hf w A hlocal htimeLocal
  refine ⟨hspatial, hs.1, ?_⟩
  rw [hs.2]
  apply Finset.sum_nonneg
  intro i hi
  rw [integral_congr_ae (htransport i hi)]
  exact hnonneg i hi

end DifferentialGeometry.Analysis
