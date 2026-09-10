import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyBasic
import DifferentialGeometry.Analysis.Integration.Measure.Family.ParametricContinuity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

omit [CompleteSpace E] in
theorem surfaceArea_pos [Nonempty M] (g : SmoothRiemannianMetric I M) :
    0 < surfaceArea g := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let _ : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  let _ : μ.IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  exact measureReal_univ_pos

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]

omit [CompleteSpace E] in
theorem surfaceArea_continuousOn
    {g : P → SmoothRiemannianMetric I M} {K : Set P} (hK : IsCompact K)
    (hg : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : P × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (K ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ContinuousOn (fun p => surfaceArea (g p)) K := by
  have hi := integral_family_cont_param (I := I) (M := M)
    (g := g) (f := fun _ _ => (1 : ℝ)) hK hg continuousOn_const
  simpa only [riemannianMeasureFamily_def, integral_const, smul_eq_mul,
    mul_one, surfaceArea] using hi

theorem totalScalarCurvature_continuousOn
    {g : P → SmoothRiemannianMetric I M} {K : Set P} (hK : IsCompact K)
    (hg : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : P × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (K ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hR : ContinuousOn (fun p : P × M => metricScalarAt (I := I) (g p.1) p.2)
      (K ×ˢ Set.univ)) :
    ContinuousOn (fun p => totalScalarCurvature (g p)) K := by
  simpa only [totalScalarCurvature, riemannianMeasureFamily_def] using
    integral_family_cont_param (I := I) (M := M)
      (g := g) (f := fun p x => metricScalarAt (I := I) (g p) x) hK hg hR

theorem surfaceEntropy_continuousOn [Nonempty M]
    {g : P → SmoothRiemannianMetric I M} {K : Set P} (hK : IsCompact K)
    (hg : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : P × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (K ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hR : ContinuousOn (fun p : P × M => metricScalarAt (I := I) (g p.1) p.2)
      (K ×ˢ Set.univ)) :
    ContinuousOn (fun p => surfaceEntropy (g p)) K := by
  have hA := surfaceArea_continuousOn hK hg
  have hAjoint : ContinuousOn (fun p : P × M => surfaceArea (g p.1))
      (K ×ˢ Set.univ) :=
    hA.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hAinv : ContinuousOn (fun p : P × M => (surfaceArea (g p.1))⁻¹)
      (K ×ˢ Set.univ) :=
    hAjoint.inv₀ (fun p _ => (surfaceArea_pos (g p.1)).ne')
  have hmulLog : ContinuousOn
      (fun p : P × M =>
        (surfaceArea (g p.1) * metricScalarAt (I := I) (g p.1) p.2) *
          Real.log (surfaceArea (g p.1) * metricScalarAt (I := I) (g p.1) p.2))
      (K ×ˢ Set.univ) :=
    Real.continuous_mul_log.comp_continuousOn (hAjoint.mul hR)
  have hintegrand : ContinuousOn
      (fun p : P × M => metricScalarAt (I := I) (g p.1) p.2 *
        Real.log (metricScalarAt (I := I) (g p.1) p.2 * surfaceArea (g p.1)))
      (K ×ˢ Set.univ) := by
    apply (hAinv.mul hmulLog).congr
    intro p _
    let A := surfaceArea (g p.1)
    let R := metricScalarAt (I := I) (g p.1) p.2
    have hAne : A ≠ 0 := (surfaceArea_pos (g p.1)).ne'
    change R * Real.log (R * A) = A⁻¹ * ((A * R) * Real.log (A * R))
    rw [mul_comm R A]
    calc
      R * Real.log (A * R) = (A⁻¹ * A) * (R * Real.log (A * R)) := by
        rw [inv_mul_cancel₀ hAne, one_mul]
      _ = A⁻¹ * ((A * R) * Real.log (A * R)) := by ring
  simpa only [surfaceEntropy, riemannianMeasureFamily_def] using
    integral_family_cont_param (I := I) (M := M)
      (g := g) (f := fun p x => metricScalarAt (I := I) (g p) x *
        Real.log (metricScalarAt (I := I) (g p) x * surfaceArea (g p))) hK hg hintegrand

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
