import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped ContDiff Manifold

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open MeasureTheory

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem redVolume_set_low
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (tau l₀ : Real) {A : Set M} (hA : MeasurableSet A)
    (hl : ∀ y ∈ A, redLength S T x y tau ≤ l₀) :
    riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (T - tau)) A *
        ENNReal.ofReal
          (Real.exp
            (-l₀ -
              ((Module.finrank Real E : Real) / 2) * Real.log tau -
              ((Module.finrank Real E : Real) / 2) *
                Real.log (4 * Real.pi))) ≤
      redVolume S T x tau := by
  let μ := riemannianVolumeMeasure (I := I) (M := M)
    (S.base.metric (T - tau))
  let c := Real.exp
    (-l₀ -
      ((Module.finrank Real E : Real) / 2) * Real.log tau -
      ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))
  have hc : ∀ y ∈ A,
      ENNReal.ofReal c ≤ ENNReal.ofReal (redDensity S T x y tau) := by
    intro y hy
    apply ENNReal.ofReal_le_ofReal
    unfold c redDensity
    apply Real.exp_le_exp.mpr
    linarith [hl y hy]
  calc
    μ A * ENNReal.ofReal c = ENNReal.ofReal c * μ A := by
      rw [mul_comm]
    _ = ∫⁻ _y in A, ENNReal.ofReal c ∂μ := by
      rw [MeasureTheory.setLIntegral_const]
    _ ≤ ∫⁻ y in A, ENNReal.ofReal (redDensity S T x y tau) ∂μ := by
      exact MeasureTheory.setLIntegral_mono' hA hc
    _ ≤ ∫⁻ y, ENNReal.ofReal (redDensity S T x y tau) ∂μ := by
      simpa using MeasureTheory.lintegral_mono_set (Set.subset_univ A)
    _ = redVolume S T x tau := by
      rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman
