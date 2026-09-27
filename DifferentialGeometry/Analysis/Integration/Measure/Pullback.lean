import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

theorem riemannianVolumeMeasure_pullback
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space N] [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N) :
    riemannianVolumeMeasure (I := I) (M := M)
        (Diffeomorph.pullbackMetric g Phi) =
      Measure.map (Phi.symm : N → M)
        (riemannianVolumeMeasure (I := I) (M := N) g) := by
  simpa only [Diffeomorph.pullbackMetricCross_eq_pullbackMetric] using
    riemannianVolumeMeasure_pullback_cross g Phi

omit [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
private theorem map_symm_withDensity
    (mu : Measure N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (rho : M → ENNReal) (hrho : Measurable rho) :
    (Measure.map (Phi.symm : N → M) mu).withDensity rho =
      Measure.map (Phi.symm : N → M)
        (mu.withDensity (fun y => rho (Phi.symm y))) := by
  ext A hA
  rw [MeasureTheory.withDensity_apply _ hA]
  rw [MeasureTheory.setLIntegral_map hA hrho Phi.symm.continuous.measurable]
  rw [Measure.map_apply Phi.symm.continuous.measurable hA]
  have hpre : MeasurableSet ((Phi.symm : N → M) ⁻¹' A) :=
    Phi.symm.continuous.measurable hA
  rw [MeasureTheory.withDensity_apply _ hpre]

theorem riemannianVolumeMeasure_pullback_withDensity
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space N] [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (rho : M → ENNReal) (hrho : Measurable rho) :
    (riemannianVolumeMeasure (I := I) (M := M)
        (Diffeomorph.pullbackMetric g Phi)).withDensity rho =
      Measure.map (Phi.symm : N → M)
        ((riemannianVolumeMeasure (I := I) (M := N) g).withDensity
          (fun y => rho (Phi.symm y))) := by
  rw [riemannianVolumeMeasure_pullback (I := I) g Phi]
  exact map_symm_withDensity (I := I)
    (riemannianVolumeMeasure (I := I) (M := N) g) Phi rho hrho

end DifferentialGeometry.Integral.Measure
