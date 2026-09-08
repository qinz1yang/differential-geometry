import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.GaussianTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Defs

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open MeasureTheory Set
open DifferentialGeometry.Analysis.Measure DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open scoped ContDiff ENNReal Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  {D : RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem lintegral_redDensity_le_gaussianTail
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x q : M)
    (tau : ℝ) {decay : ℝ} (hdecay : 0 < decay) (C : ℝ)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric (T - tau)))
    (hRic : RicciBoundedBelow (I := I) (S.base.metric (T - tau)) 0) (N : ℕ)
    (hquad : ∀ᵐ y ∂(riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric (T - tau))).restrict
        {y : M | (N : ℝ) ≤
          (riemannianEDistOf (I := I) (S.base.metric (T - tau)) q y).toReal},
      decay * (riemannianEDistOf (I := I)
          (S.base.metric (T - tau)) q y).toReal ^ 2 - C ≤ redLength S T x y tau) :
    ∫⁻ y in {y : M | (N : ℝ) ≤
          (riemannianEDistOf (I := I) (S.base.metric (T - tau)) q y).toReal},
        ENNReal.ofReal (redDensity S T x y tau)
        ∂riemannianVolumeMeasure (I := I) (M := M) (S.base.metric (T - tau)) ≤
      ENNReal.ofReal (Real.exp
        (C - ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
          ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))) *
        (((volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).toSphere univ *
          ENNReal.ofReal ((Module.finrank ℝ E : ℝ)⁻¹)) *
          gaussianTail (Module.finrank ℝ E) decay N) := by
  let A : ℝ := Real.exp
    (C - ((Module.finrank ℝ E : ℝ) / 2) * Real.log tau -
      ((Module.finrank ℝ E : ℝ) / 2) * Real.log (4 * Real.pi))
  let rho : M → ℝ := fun y =>
    (riemannianEDistOf (I := I) (S.base.metric (T - tau)) q y).toReal
  let tail : Set M := {y | (N : ℝ) ≤ rho y}
  let μ : Measure M := riemannianVolumeMeasure (I := I) (M := M)
    (S.base.metric (T - tau))
  let G : M → ℝ := fun y => Real.exp (-decay * rho y ^ 2)
  have hpoint : ∀ᵐ y ∂μ.restrict tail, redDensity S T x y tau ≤ A * G y := by
    filter_upwards [hquad] with y hy
    dsimp only [A, G]
    rw [← Real.exp_add, redDensity]
    apply Real.exp_le_exp.mpr
    change decay * rho y ^ 2 - C ≤ redLength S T x y tau at hy
    linarith
  have hfactor : (∫⁻ y in tail, ENNReal.ofReal (A * G y) ∂μ) =
      ENNReal.ofReal A * (∫⁻ y in tail, ENNReal.ofReal (G y) ∂μ) := by
    calc
      _ = ∫⁻ y in tail, ENNReal.ofReal A * ENNReal.ofReal (G y) ∂μ :=
        lintegral_congr fun _ => ENNReal.ofReal_mul (Real.exp_pos _).le
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have htail := lintegral_gaussian_riemannianEDistOf_le
    (S.base.metric (T - tau)) hcomplete q hdecay hRic N
  exact (lintegral_mono_ae (hpoint.mono fun _ h => ENNReal.ofReal_le_ofReal h)).trans
    (hfactor.trans_le (mul_le_mul_right htail (ENNReal.ofReal A)))

end DifferentialGeometry.PDE.RicciFlow.Perelman
