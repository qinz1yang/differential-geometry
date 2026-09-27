import DifferentialGeometry.Geometry.Metric.Family.Measurable
import DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuous
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs

noncomputable section

open MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {D : RealTimeInterval}

theorem aestronglyMeasurable_lRegularizedLagrangian
    (S : SolutionOn (I := I) (M := M) D) (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S) {μ : Measure ℝ} {Ω : Set ℝ}
    (hΩ : IsOpen Ω) (T : ℝ) (γ : ℝ → M) (hγ : ContinuousOn γ Ω)
    (hd : ∀ᵐ t ∂μ.restrict Ω, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hclock : ∀ t ∈ Ω, T - t ^ 2 ∈ D.carrier) :
    AEStronglyMeasurable (lRegularizedLagrangian S T γ) (μ.restrict Ω) := by
  have hτ : ContinuousOn (fun t : ℝ => T - t ^ 2) Ω :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn
  have hkin : AEMeasurable (fun t => (S.family.metric (T - t ^ 2)).inner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
      (μ.restrict Ω) :=
    MetricFamilySmoothOn.aemeasurable_metricQuadratic_mfderiv
      (I := I) (M := M) (μ := μ) (Ω := Ω) hMet hΩ γ hγ hd
      (fun t => T - t ^ 2) hτ hclock
  have hpair : ContinuousOn (fun t : ℝ => (T - t ^ 2, γ t)) Ω := hτ.prodMk hγ
  have hmaps : MapsTo (fun t : ℝ => (T - t ^ 2, γ t)) Ω (D.carrier ×ˢ (univ : Set M)) :=
    fun t ht => ⟨hclock t ht, mem_univ _⟩
  have hscalar : ContinuousOn (fun t => S.scalar (T - t ^ 2) (γ t)) Ω := by
    simpa only [Function.comp_def] using hSc.scalar_continuousOn.comp hpair hmaps
  have hsc : AEMeasurable (fun t => S.scalar (T - t ^ 2) (γ t)) (μ.restrict Ω) :=
    hscalar.aemeasurable hΩ.measurableSet
  have hweight : AEMeasurable (fun t : ℝ => 2 * t ^ 2) (μ.restrict Ω) :=
    (continuous_const.mul (continuous_id.pow 2)).measurable.aemeasurable
  have hkinScalar : AEMeasurable (fun t => (1 / 2 : ℝ) *
      (S.base.metric (T - t ^ 2)).inner (γ t) (lVelocity γ t) (lVelocity γ t))
      (μ.restrict Ω) := by
    change AEMeasurable (fun t => (1 / 2 : ℝ) *
      (S.family.metric (T - t ^ 2)).inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) (μ.restrict Ω)
    exact aemeasurable_const.mul hkin
  have hsc' : AEMeasurable (fun t => 2 * t ^ 2 * S.scalar (T - t ^ 2) (γ t))
      (μ.restrict Ω) := hweight.mul hsc
  have hlag : AEMeasurable (lRegularizedLagrangian S T γ) (μ.restrict Ω) := by
    unfold lRegularizedLagrangian
    exact hkinScalar.add hsc'
  exact hlag.aestronglyMeasurable

theorem aestronglyMeasurable_lRegularizedLagrangian_of_absolutelyContinuousOnInterval
    (S : SolutionOn (I := I) (M := M) D) (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S) (T : ℝ) (γ : ℝ → M) {a b : ℝ}
    (hγ : Manifold.absolutelyContinuousOnInterval I γ a b)
    (hclock : ∀ t ∈ Ioo a b, T - t ^ 2 ∈ D.carrier) :
    AEStronglyMeasurable (lRegularizedLagrangian S T γ) (volume.restrict (Ioo a b)) := by
  apply aestronglyMeasurable_lRegularizedLagrangian S hMet hSc isOpen_Ioo T γ
    (hγ.1.mono (Ioo_subset_Icc_self.trans Icc_subset_uIcc)) _ hclock
  exact (Manifold.absolutelyContinuousOnInterval_ae_mdifferentiableAt hγ).filter_mono
    (ae_mono (Measure.restrict_mono (Ioo_subset_Icc_self.trans Icc_subset_uIcc) le_rfl))

end DifferentialGeometry.PDE.RicciFlow.Perelman
